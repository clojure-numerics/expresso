(ns numeric.expresso.rules
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] ]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [numeric.expresso.utils :as utils]
            [numeric.expresso.construct :as c]))

(defn replace-?-with-lvar [node]
  (if (and (symbol? node) (.startsWith (name node) "?"))
    (lvar node false)
    node))


(defn ?-to-lvar [code]
  (walk/prewalk replace-?-with-lvar code))

(defn isao [a b]
  (conda
   ((== a b))
   ((project [a b]
             (== true (isa? a b))))))

(defn check-guardo [guard]
  (project [guard] guard))

(defn apply-transformationo [trans n-exp]
  (project [trans]
           (if (and  (ifn? trans) (not (coll? trans)))
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

(defn is-seqo [v]
  (project [v]
           (== true (coll? v))))
(declare match-expressiono)

(defna match-expressionso [pargs eargs]
  ([[p . ps] [e . es]] (match-expressiono p e) (match-expressionso ps es))
  ([[] []] succeed)
  ([_ _] fail))

(defn expression-matcho [pargs eargs]
  (project [pargs eargs]
           (do ;(prn "expr-matcho with " pargs eargs)
           (if (not= (count pargs) (count eargs))
             fail
             succeed)))
  (match-expressionso pargs eargs))

(defn split-list [v]
                                        ; (println "split-list " v)
  (let [res
        (for [x (range (count v)) :when (not (lvar? (nth v x)))] 
          (let [elem (nth v x)
                left (take x v)
                right (drop (clojure.core/+ x 1) v)]
            [elem (concat left right)]))]
    res))


(defn split-listo [l erg]
  (project [l ]
       ;    (println "l ist " l " erg ist " erg)
           (== erg (split-list l))))

(defn only-lvarso [args]
  (project [args]
           (== true (every? lvar? args))))

(defn match-lvars-commutativeo [pargs eargs]
  (fresh [perm]
         (permuteo pargs perm)
         (== perm eargs)))

(defn match-commutativeo [pargs eargs]
  (fresh [esl psl eng png er pr]
         (conda
          ((only-lvarso pargs) (match-lvars-commutativeo pargs eargs))
          ((only-lvarso eargs) (match-lvars-commutativeo pargs eargs))
         ((split-listo pargs psl)
          (membero [png pr] psl)
          (split-listo eargs esl)
          (membero [eng er] esl)
          (match-expressiono png eng)
          (match-expressionso pr er)))))

(defn get-symbol [expr]
  (if (coll? expr) (first expr) expr))

(defmulti matcher get-symbol)

(defmethod matcher :default [_]
  expression-matcho)

(defmethod matcher 'e/ca-op [_] match-commutativeo)

(def replacements (atom {}))

(defn replace-symbolso [old new]
  (project [old]
           (let [res (walk/prewalk-replace @replacements old)]
             (do (reset! replacements {})
                 (== res new)))))

(defn add-replacemento [es ps]
  (project [es ps]
           (if (= es ps)
             succeed
             (do (swap! replacements assoc ps es)
                 succeed))))
(defn match-expressiono [pat exp]
  (conda
   ((== pat exp))
   ((is-seqo pat) (is-seqo exp)
    (fresh [ps es pargs eargs]
           (c/expo ps pargs pat)
           (c/expo es eargs exp)
           (isao es ps)
           (add-replacemento es ps)
           (project [ps pargs eargs pat exp]
                    (let [f (matcher ps)]
                      (f pargs eargs)))))))
    

(defn apply-rule [rule exp]
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

(defn apply-ruleso [rules expr nexpr]
  (matche [rules]
          ([[?r . ?rs]] (conda
                         ((apply-ruleo ?r expr nexpr))
                         ((apply-ruleso ?rs expr nexpr))))))

(defn transform-with-rules [rules expr]
  (walk/postwalk #(or (first (run* [q] (apply-ruleso rules % q))) %) expr))


(defn collabs-factorso [x a b]
  (fn [res]
    (project [a b]
             (== res (c/ex 'e/ca* x (+ a b))))))

  
(defna numberso [vars] 
  ([[n . rest]] (project [n] (do (== true (number? n))) (numberso rest)))
  ([[]] succeed))


(c/with-expresso [* + - e/ca+ e/ca* e/- e/div]

(def simplification-rules
  [(rule (e/ca+ 0 ?x) :=> ?x)
   (rule (e/ca* 0 ?x) :=> 0)
   (rule (e/ca* 1 ?x) :=> ?x)
   (rule (e/- 0 ?x) :=> (e/- ?x))
   (rule (e/- ?x 0) :=> ?x)
   (rule (e/ca* ?x (e/div 1 ?x)) :=> 1 :if (!= ?x 0))
   (rule (e/ca+ ?x (e/- ?x)) :=> 0)
   (rule (e/ca+ (e/ca* ?a ?x) (e/ca* ?b ?x)) :=> (collabs-factorso ?x ?a ?b)
         :if (numberso [?a ?b]))
   (rule (e/ca* ?x (e/ca+ ?a ?b)) :=> (e/ca+ (e/ca* ?x ?a) (e/ca* ?x ?b)))])

(deftest test-transform-with-rules
  (is (= '(clojure.core/* 3 3)
         (transform-with-rules simplification-rules 
			       (* 3 (+ (+ 0 3) (* 0 3))))))))