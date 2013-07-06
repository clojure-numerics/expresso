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

(defmacro rule
  "constructs an rule. Syntax is (rule pat :=> trans) or \n
   (rule pat :=> trans :if guard)"
  [& v]
  (let [expanded (?-to-lvar v)
        [pat to trans & rest] expanded
       ; ep (c/ex* pat) et (c/ex* trans)
        guard (if (seq rest) (second rest) succeed)]
    [pat trans guard]))



  
(defn apply-rule
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

(defn apply-ruleo
  "core.logic relation of apply-rule - not relational, you can't generate all possible rules which transform an expression to the new-expression"
  [rule exp n-exp]
  (project [rule]
  (fresh [res]
         (== res (apply-rule rule exp))
         (conda ((nilo res) fail) ((== res n-exp))))))



(defn apply-ruleso
  "non-relational core.logic equivalent of apply-rules"
  [rules expr nexpr]
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
   in the default case. A custom walkfn can be specified"
  ([rules expr walkfn]
     (let [tmp (walkfn
                (fn [a] (let [res (apply-rules rules a)] res)) expr)]
       (if (= tmp expr) tmp (recur rules tmp walkfn))))
  ([rules expr] (transform-with-rules rules expr walk/prewalk)))



