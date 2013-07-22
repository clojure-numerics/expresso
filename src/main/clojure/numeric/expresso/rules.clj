(ns numeric.expresso.rules
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is]]
        [numeric.expresso.matcher]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [numeric.expresso.utils :as utils]
            [numeric.expresso.construct :as c]))
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

(defn name-of-lvar [c]
  (let [n (re-find #"<lvar:(\?(?:\&[\+\*])?\w*)>"  (str c))]
    (and (seq n) (symbol (second n)))))

(defn revert-back-lvars [code]
  (walk/postwalk (fn [c] (if-let [name (name-of-lvar c)]
                           name
                           c)) code))


(defmacro transfn [args & code]
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

(defmacro transrel [args & code]
  (let [args (revert-back-lvars args)
        code (revert-back-lvars code)]
    `(fn ~(vec (butlast args))
       (fn [~(last args)]
         (project ~(vec (butlast args))
                  (fresh []
                         ~@code))))))

(defmacro guardfn [args & code]
  (let [args (revert-back-lvars args)
        code (revert-back-lvars code)]
  `(fn ~args
     (project ~args
              (== true (do ~@code))))))

(defmacro guardrel [args & code]
  (let [args (revert-back-lvars args)
        code (revert-back-lvars code)]
    `(fn ~(vec args)
       (project ~(vec args)
                (fresh [] ~@code)))))


(defn lvars-in-code [transcode]
  (let [lv (filter #(.startsWith (str %) "?") (flatten transcode))]
    (into [] (into #{} lv))))

(defn str-seq [s]
  (if (sequential? s)
    (apply str (map str-seq s))
    (str s)))
    

(defn replace-back [transcode]
  (let [matches (re-seq #"<lvar:(\?(?:\&[\+\*])?\w*)>" (str-seq transcode))
        symb-matches (map (fn [v] [(symbol (first v)) (symbol (second v))]) matches)
        replacement-map (into {} matches)
        erg (walk/postwalk #(do 
                              (if-let [r (get replacement-map (str %) nil)]
                                  (symbol r)  %)) transcode)]
    erg))

(defn reconstruct [lvars]
  (map replace-?-with-lvar lvars))

(defn make-inline-trans [transcode]
  (let [lvars (lvars-in-code transcode)]
    `((transfn ~lvars ~transcode) ~@lvars)))
    
(defmacro trans [transcode]
  (let [res (?-to-lvar (make-inline-trans (replace-back transcode)))]
    res))

(defn make-inline-guard [guardcode]
  (let [lvars (lvars-in-code guardcode)]
    `((guardfn ~lvars ~guardcode) ~@lvars)))

(defmacro guard [guardcode]
  (let [res (?-to-lvar (make-inline-guard (replace-back guardcode)))]
    res))

(defmacro rule
  "constructs an rule. Syntax is (rule pat :=> trans) or \n
   (rule pat :=> trans :if guard)"
  [& v]
  (let [expanded (?-to-lvar v)
        [pat to trans & rest] v
        trans (if (= to :==>) (make-inline-trans trans) trans)
        guard (if (and (seq rest) (= :if (first rest))) (second rest) succeed)]
    (with-meta [(?-to-lvar pat) (?-to-lvar trans) (?-to-lvar guard)] {:syntactic (and (seq rest) (= (last rest) :syntactical))})))



(defn apply-semantic-rule
  "applies rule to expression. The first succesful application of the rule gets performed"
  [rule exp]
  (first (run 1 [q]
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


(defn apply-rule [rule exp]
  (if-let [m (meta rule)]
    (if (:syntactical m)
      (apply-syntactic-rule rule exp)
      (apply-semantic-rule rule exp))))

(defn apply-ruleo
  "core.logic relation of apply-rule - not relational, you can't generate all possible rules which transform an expression to the new-expression"
  [rule exp n-exp]
  (project [rule]
  (fresh [res]
         (== res (apply-rule rule exp))
         (conda ((nilo res) fail) ((== res n-exp))))))

(declare apply-rules)
(defn apply-ruleso [rules expr nexpr]
  (project [rules expr]
           (fresh [a]
                  (== a (apply-rules rules expr))
                  (conda
                   ((nilo a) fail)
                   ((== nexpr a))))))

#_(defn apply-ruleso
  "non-relational core.logic equivalent of apply-rules"
[expr nexpr]
  (matche [rules]
          ([[?r . ?rs]] (conda
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

(declare apply-rules transform-with-rules transform-expression)
(defn apply-to-end
  [rules expr]
  (loop [rules rules expr expr]
    (let [nexpr (apply-rules rules expr)]
      (if (= expr nexpr)
        nexpr
        (transform-expression rules nexpr)))))

(defn apply-simp
  [rules expr]
  (let [nexpr (apply-rules rules expr)]
    (if (= nexpr expr)
      expr
      (transform-with-rules rules nexpr walk/postwalk apply-simp))))

(defn apply-all-rules
  "tries to apply all rules in rules on expression"
  [rules expr]
  (loop [rules rules expr expr]
    (if (seq rules)
      (recur (rest rules) (if-let [nexpr (apply-rule (first rules) expr)]
                            nexpr expr))
      expr)))

(defn apply-rules
  "returns the result of the first succesful application of a rule in rules "
  [rules expr]
  (loop  [rules rules expr expr]
    (if (seq rules)
      (if-let [erg (apply-rule (first rules) expr)]
        erg
        (recur (rest rules) expr))
      expr)))

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


(defn transform-expression [rules expr]
  (if (and (sequential? expr) (symbol? (first expr)))
    (let [transformed (map (partial transform-expression rules) (rest expr))
         ]
      (apply-to-end rules (list* (first expr) transformed)))
    (apply-to-end rules expr)))

;;See if it is possible to reinstantiate rules so that they can be applied all
;;in the core.logic context
