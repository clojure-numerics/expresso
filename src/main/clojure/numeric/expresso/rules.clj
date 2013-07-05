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
  "used by the rule macro to make ?... symbols unifyable"
  [node]
  (if (and (symbol? node) (.startsWith (name node) "?"))
    (lvar node false)
    node))

(defn- ?-to-lvar [code]
  (walk/prewalk replace-?-with-lvar code))


(defn- check-guardo [guard]
  (project [guard] guard))

(defn- apply-transformationo [trans n-exp]
  (project [trans]
           (if (and  (ifn? trans) (not (coll? trans)) (not (keyword? trans)) (not (symbol? trans)))
             (trans n-exp)
             (== trans n-exp))))

(defmacro rule
  "constructs an rule. Syntax is (rule pat :=> trans) or \n
   (rule pat :=> trans :if guard)"
  [& v]
  (let [expanded (?-to-lvar v)
        [pat to trans & rest] expanded
        guard (if (seq rest) (second rest) succeed)]
    [pat trans guard]))



  
(defn apply-rule
  "applies rule to expression in a core.logic run 1 block, so the first succesful application of a rule
   gets chosen"
  [rule exp]
  (first (run 1 [q]
              (fresh [pat trans guard tmp]
                     (== rule [pat trans guard])
                     (match-expressiono pat exp)
                     (check-guardo guard)
                     (apply-transformationo trans tmp)
                     (replace-symbolso tmp q)))))


(defn apply-ruleo
  "applies rule to exp failing if not applicable or unifying n-exp
   to the result"
  [rule exp n-exp]
  (project [rule]
  (fresh [res]
         (== res (apply-rule rule exp))
         (conda ((nilo res) fail) ((== res n-exp))))))



(defn apply-ruleso
  "returns the result of the first succesful application of a rule in rules"
  [rules expr nexpr]
  (matche [rules]
          ([[?r . ?rs]] (conda
                         ((apply-ruleo ?r expr nexpr))
                         ((apply-ruleso ?rs expr nexpr))))))

(defn apply-rules-debug
  "returns the result of the first succesful application of a rule in rules "
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

(defn transform-with-rules [rules expr]
  (let [tmp (walk/postwalk
             (fn [a] (let [res (apply-rules rules a)] res)) expr)]
    (if (= tmp expr) tmp (recur rules tmp))))



