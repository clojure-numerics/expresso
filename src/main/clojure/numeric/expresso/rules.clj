(ns numeric.expresso.rules
  (:refer-clojure :exclude [== record?])
  (:use [clojure.core.logic]
        [numeric.expresso.impl.matcher]
        [numeric.expresso.protocols])
  (:require [numeric.expresso.properties :as props]
            [clojure.walk :as walk]
            [clojure.core.memoize :as memo]
            [numeric.expresso.utils :as utils]
            [clojure.set :as set]
            [numeric.expresso.construct :as c]))
;;this namespace provides expresso rule-based translator facility. Most notable
;;are the rule macro, which constructs a rule and apply-rule wich applies a
;;rule in a core.logic context.

;;A rule consists of a 3-element vector with [pattern transformation guard]
;;The elements of the vector can contain fresh lvars
;;the rule macro converts ?-starting symbols to fresh lvars
;;The transition can be a normal lvar-containing expression like the pattern
;;or can be a core.logic relation
;;the guard is optional (succeed is used if no guard is supplied)


(declare exp-isa?)
(defn- replace-?-with-lvar
  "replaces a symbol with a not gensymed lvar if it starts with a ?"
  [node]
  (if (and (symbol? node) (.startsWith (name node) "?"))
    (lvar node false)
    node))

(defn- ?-to-lvar
  "walks the code to replace ?-symbols with unifyable lvars"
  [code]
  (walk/prewalk replace-?-with-lvar code))


(defn- check-guardo
  "succeeds iff the guard relation succeeds"
  [guard]
  (project [guard] guard))

(defn- apply-transformationo
  "the transformation can either be an expression or a core.logic relation
   of (trans result)"
  [trans n-exp]
  (project [trans]
           (if (and (ifn? trans)
                    (not (coll? trans))
                    (not (keyword? trans))
                    (not (symbol? trans)))
             (trans n-exp)
             (== trans n-exp))))

(defn- name-of-lvar [c]
  (let [n (re-find #"<lvar:(\?(?:\&[\+\*])?\w*)>"  (str c))]
    (and (seq n) (symbol (second n)))))

(defn- revert-back-lvars [code]
  (walk/postwalk (fn [c] (if-let [name (name-of-lvar c)]
                           name
                           c)) code))
;;utility macros to create inline core.logic relations which act as transition
;;and guard in a rule. the ...fn macros take normal clojure code as argument and
;;convert it to a core.logic relation and the ...rel macros take a core.logic
;;relation.

(defmacro transfn
  "transfn creates a function to be used as transition in a rule"
  [args & code]
  (let [args (revert-back-lvars args)
        code (revert-back-lvars code)]
  `(fn ~args
     (fn [res#]
       (project ~args
                (fresh [tmp#]
                       (== tmp# (do ~@code))
                       (conda
                        ((nilo tmp#) fail)
                        ((== res# tmp#)))))))))

(defmacro transrel
  "transrel creates a relation to be used as transition in a rule"
  [args & code]
  (let [args (revert-back-lvars args)
        code (revert-back-lvars code)]
    `(fn ~(vec (butlast args))
       (fn [~(last args)]
         (project ~(vec (butlast args))
                  (fresh []
                         ~@code))))))

(defmacro guardfn
  "guardfn creates a function to be used as guard in a rule"
  [args & code]
  (let [args (revert-back-lvars args)
        code (revert-back-lvars code)]
  `(fn ~args
     (project ~args
              (== true (do ~@code))))))

(defmacro guardrel
  "guardrel creates a relations to be used as guard in a rule"
  [args & code]
  (let [args (revert-back-lvars args)
        code (revert-back-lvars code)]
    `(fn ~(vec args)
       (project ~(vec args)
                (fresh [] ~@code)))))


(defn- lvars-in-code [transcode]
  (let [lv (filter #(.startsWith (str %) "?") (flatten transcode))]
    (into [] (into #{} lv))))

(defn- str-seq
  "fully transforms (possible lazy ) s to a string"
  [s]
  (if (sequential? s)
    (apply str (map str-seq s))
    (str s)))
    

(defn- replace-back [transcode]
  (let [matches (re-seq #"<lvar:(\?(?:\&[\+\*])?\w*)>" (str-seq transcode))
        symb-matches (map (fn [v] [(symbol (first v)) (symbol (second v))]) matches)
        replacement-map (into {} matches)
        erg (walk/postwalk #(do 
                              (if-let [r (get replacement-map (str %) nil)]
                                  (symbol r)  %)) transcode)]
    erg))

(defn- reconstruct [lvars]
  (map replace-?-with-lvar lvars))

(defn- make-inline-trans [transcode]
  (let [lvars (lvars-in-code transcode)]
    `((transfn ~lvars ~transcode) ~@lvars)))

(defn trans*
  "function version of trans"
  [transcode]
  (let [res (?-to-lvar (make-inline-trans (replace-back transcode)))]
    res))

(defmacro trans
  "to be used inside a rule to transform the inline-code to a core.logic
   relation which is suitable for the rule based translator as translation
   relation. All values of the ?-symbols of the pattern are defined inside
   trans."
  [transcode]
  (trans* transcode))


(defn make-inline-guard [guardcode]
  (let [lvars (lvars-in-code guardcode)]
    `((guardfn ~lvars ~guardcode) ~@lvars)))

(defn guard* [guardcode]
  (let [res (?-to-lvar (make-inline-guard (replace-back guardcode)))]
    res))

(defmacro guard
  "to be used inside a rule to transform the inline (boolean returning) code
   to a core.logic relation which is suitable for the rule based translator
   as guard relation. All values of the ?-symbols of the pattern are defined
   inside guard"
  [guardcode]
  (guard* guardcode))


(defn rule*
  "function version of rule"
  [v]
  (let [expanded (?-to-lvar v)
        [pat to trans & rest] v
        trans (if (= to :==>) (make-inline-trans trans) trans)
        guard (if (and (seq rest) (= :if (first rest))) (second rest) succeed)]
    (with-meta [(?-to-lvar pat) (?-to-lvar trans) (?-to-lvar guard)] {:syntactic (and (seq rest) (= (last rest) :syntactic))})))
  

(defmacro rule
  "constructs a rule. Syntax is (rule pat :=> trans) pat is a normal expression
   which can contain symbols starting with a ? which will be transformed to
   logic variables which are unified while matching the an expression to the
   pattern. trans can also be an expression containing lvars or it can be an
   arbitrary core.logic relation which takes the transformed rule as its output
   argument. :==> can be used to automatically translate a normal inline clojure
   function to the needed core.logic relation.
   It supports an optional guard argument. Syntax is then (rule pat :=> trans :if
   guard) guard is a core.logic relation which is called after matching the pat
   with the expression and succeeds if the rule is applicable or fails if not."
  [& v]
  (rule* v))


(defn define-extractor
  "defines and installs an extractor with the given name and relation.
   The relation will be called during matching and unifies the arguments
   of the extractor with the expression it is being matched with"
  [name rel]
  (.addMethod props/extractor-rel name (fn [_] rel)))


(defn apply-semantic-rule
  "applies rule to expression. The first succesful application of the rule gets
   performed"
  [rule exp]
  (first (-run {:occurs-check false :n 1 :reify-vars (fn [v s] s)} [q]
               (fresh [pat trans guard tmp]
                      (== rule [pat trans guard])
                      (match-expressiono pat exp)
                      (check-guardo guard)
                      (apply-transformationo trans tmp)
                      (replace-symbolso tmp q)))))

(defn apply-syntactic-rule
  "applies simple syntactical rule to expression."
  [rule exp]
  (first (run 1 [q]
              (fresh [pat trans guard]
                     (== rule [pat trans guard])
                     (== pat exp)
                     (check-guardo guard)
                     (apply-transformationo trans q)))))
(defn apply-rule
  "applies the specified rule to the epxression returning a modified one if the
   rule was applicable of nil if the rule was not applicable"
  [rule exp]
  (let [ex-op (expr-op exp)
        rule-op (expr-op (first rule))]
    (if (or (c/extractor? (first rule))
            (not (or (and (nil? rule-op)
                          (not (sequential? (first rule)))
                          (not (lvar? (first rule))))
                     (and ex-op rule-op (not (exp-isa? ex-op rule-op))))))
      (if (:syntactic (meta rule))
        (apply-syntactic-rule rule exp)
        (apply-semantic-rule rule exp)))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;various functions to build rule application strategies outside and inside of
;;a core.logic context


(defn apply-ruleo
  "core.logic relation of apply-rule - not relational, you can't generate all possible rules which transform an expression to the new-expression"
  [rule exp n-exp]
  (project [rule exp]
           (if-let [res (apply-rule rule exp)]
             (== res n-exp)
             fail)))

(declare apply-rules)

(defn apply-ruleso
  "non-relational core.logic equivalent of apply-rules"
[rules expr nexpr]
  (matche [rules]
          ([[?r . ?rs]] (conde
                         ((apply-ruleo ?r expr nexpr))
                         ((apply-ruleso ?rs expr nexpr))))))

(defn apply-rules-debug
  "like apply-rules but gives realtime information about the rules which gets tried and applied"
  [rules expr]
  (loop  [rules rules expr expr]
    (if (seq rules)
      (do (prn "try apply " (butlast (first rules)) "with " expr)
          (if-let [erg (apply-rule (first rules) expr)]
            (do (prn "applied rule " (butlast (first rules)) " with result " erg)
                erg)
            (recur (rest rules) expr)))
      expr)))

(declare apply-rules transform-with-rules transform-expression*
         transform-expressiono)
(defn- apply-to-end
  [rules expr]
    (let [nexpr (apply-rules rules expr)]
      (if (= expr nexpr)
        nexpr
        (transform-expression* nexpr))))

(defn- apply-to-endo [rules expr new-expr]
  (fresh [nexpr]
         (conda
          ((apply-ruleso rules expr nexpr)
           (transform-expressiono rules nexpr new-expr))
          ((== new-expr expr)))))

(defn apply-all-rules
  "tries to apply all rules in rules on expression"
  [rules expr]
  (loop [rules rules expr expr]
    (if (seq rules)
      (recur (rest rules) (if-let [nexpr (apply-rule (first rules) expr)]
                            nexpr expr))
      expr)))

(defn- exp-isa?
  "isa? semantics in expression. For unqualified symbols check e/symbol"
  [ex-op rule-op]
  (or (isa? ex-op rule-op) (isa? (symbol (str "e/" ex-op)) rule-op)))

(defn apply-rules
  "returns the result of the first succesful application of a rule in rules "
  [rules expr]
  (let [rules (into [] rules)]
  (loop  [rules rules expr expr]
    (if (seq rules)
      (if-let [erg (apply-rule (first rules) expr)]
        erg
        (recur (rest rules) expr))
      expr))))

(def ^:dynamic *rules*)

(defn transform-with-rules
  "transforms the expr according to the rules in the rules vector until no rule
   can be applied any more. Uses clojure.walk/prewalk to walk the expression tree
   in the default case. A custom walkfn and applyfn can be specified defaults to
   clojure.walk/postwalk and apply-rules"
  ([rules expr walkfn applyfn]
     (let [tmp (walkfn
                (fn [a] (let [res (applyfn rules a)] res)) expr)]
       (if (= tmp expr) tmp (recur rules tmp walkfn applyfn))))
  ([rules expr] (transform-with-rules rules expr walk/prewalk apply-rules)))

(defn transform-with-rules-wo-recursion
  "transforms the expr according to the rules in the rules vector until no rule
   can be applied any more. Uses clojure.walk/prewalk to walk the expression tree
   in the default case. A custom walkfn and applyfn can be specified defaults to
   clojure.walk/postwalk and apply-rules"
  ([rules expr walkfn applyfn]
     (let [tmp (walkfn
                (fn [a] (let [res (applyfn rules a)] res)) expr)]
       tmp))
  ([rules expr] (transform-with-rules rules expr walk/prewalk apply-rules)))

(defn- simplified? [expr rules]
  (and (instance? clojure.lang.IObj expr)
       (contains? (:simplified-by (meta expr)) (:id (meta rules)))))

(defn- annotate-simplified [expr *rules*]
  (if (instance? clojure.lang.IObj expr)
    (with-meta expr (assoc (meta expr)
                      :simplified-by #{(:id (meta *rules*))}))
    expr))

(defn- add-simp-annotations [res expr]
  (if (instance? clojure.lang.IObj res)
    (with-meta res (update-in (meta res)
                              [:simplified-by]
                              #(set/union % (:simplified-by (meta expr)))))))


(defn- merge-transformed-meta [meta-exp transformed] 
  (if (instance? clojure.lang.IObj transformed)
    (with-meta transformed (merge meta-exp (meta transformed)))
    transformed))

(defn- transform-expression* [expr]
  (transform-expr expr *rules*))

;;Transform-expression is the optimized transform-all function to transform
;;an expression according to the rules in the rule vector. The outcoming
;;expression is guaranteed to be in a standart form defined by the rule vector
;;applies the rules in a fully recursive bottom-up approach.
;;uses tagging to avoid repetive transformations and also apply-rules semantics
;;to avoid applying a rule where it is clear to fail.
;;uses a protocol dispatch so that custom expression types can specify how
;;rules will be applied. For example the LetExpression transforms itself by
;;first transforming the bindings and then the body.

(defn transform-expression
  "transforms the expression according to the rules in the rules vector in a
   bottom up manner until no rule can be applied to any subexpression anymore"
  [rules expr]
  (binding [*rules* (if (:id (meta rules))
                      rules
                      (with-meta rules (assoc (meta rules) :id (gensym "id"))))]
    (let [res (transform-expression* expr)]
      res)))

;;transform-expression uses tagging to mark expression simplified according to
;;the :id key in the metadata of the rule. If no is specified a new will be
;;gensymed. if the expression is simplified the id of the actual rules will be
;;added to the simplified-by key in the expression metadata, which takes care
;;that the expression wont't be simplified again by transform-expression.
;;It is also possible that the expression was simplified by other rules and that
;;the current transformation hasn't changed it. In this case the old simplified
;;by key can be retained and the union of the ids will be the new simplified-by
;;set. It also merges the metadata of the transformed expression with the
;;previous expressions in that way that the transformed meta has has priority.
;;This is important for the inferred shape which is stored in another metadata
;;key. 
(extend-protocol PTransformExpression
  Object
  (transform-expr [expr rules]
    (if (simplified? expr rules)
      expr
      (let [res
            (if-let [op (expr-op expr)]
              (let [transformed (doall (map  transform-expression*
                                             (expr-args expr)))
                    n-expr (merge-transformed-meta
                              (meta expr) (c/cev (first expr) transformed))
                    res (apply-to-end rules n-expr)]
                (if (= expr res)
                  (add-simp-annotations
                   (annotate-simplified res rules) expr)
                  (annotate-simplified res rules)))
              (annotate-simplified (apply-to-end rules expr) rules))]
        res)))
  numeric.expresso.impl.pimplementation.LetExpression
  (transform-expr [expr rules]
    (let [bindings (.-bindings expr) code (.-code expr)]
      (c/let-expr (mapv #(transform-expression rules %) bindings)
                  (map #(transform-expression rules %) code)))))
    

(defn transform-expressiono
  "core.logic equivalent of transform-expression"
  [rules expr nexpr]
  (project [rules expr]
           (fresh [res]
                  (conda
                   ((nilo (expr-op expr)) (apply-to-endo rules expr nexpr))
                   ((fresh [transformed]
                           (utils/mapo #(transform-expressiono rules %1 %2)
                                       (expr-args expr)
                                       transformed)
                           (project [transformed]
                                    (apply-to-endo
                                     rules (list* (first expr)
                                                  transformed) nexpr))))))))

(defn transform-one-level
  "transforms the top level of expr according to rules"
  [rules expr]
  (transform-with-rules rules expr (fn [f expr] (f expr)) apply-rules))

;;See if it is possible to reinstantiate rules so that they can be applied all
;;in the core.logic context
