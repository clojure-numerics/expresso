(ns numeric.expresso.core
  (:refer-clojure :exclude [== * + / -])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [numeric.expresso.construct :only [* + / - ca+ ca*]]
        [clojure.test])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [clojure.core.logic.unifier :as u]
            [numeric.expresso.utils :as utils]
            [numeric.expresso.solve :as s]
            [numeric.expresso.construct :as c]))


(defn has-metao [q m]
  (== (meta q) (partial-map m)))

(defn is-commutativeo [exp]
  (fresh [m]
         (has-metao exp {:properties m})
         (membero :commutative m)))





#_(defn apply-rule-simple [rule expression]
  (run 1 [q]
       (fresh [pat trans]
              (== rule [pat trans])
              (expression-matcho expression pat)
              (== trans q))))


(defn apply-ruleo [rule expression result]
  (fresh [res]
         (== res (first (apply-rule-simple rule expression)))
         (conda
          ((nilo res) fail)
          ((== result res)))))

(defmacro ?-expand [x]
  `(fresh[~'?x]
         (let [~'a ~x]
           a)))

(defn noto [g]
  (fn [a]
    (if (nil? (g a))
      a)))

(defn split-list [v]
 ; (println "split-list " v)
  (for [x (range (count v)) :when (not (lvar? (nth v x)))] 
    (let [elem (nth v x)
          left (take x v)
          right (drop (clojure.core/+ x 1) v)]
      [elem (concat left right)])))

(comment
  (run* [q] (fresh [a b c d e f g] 
					(== a (split-list v))
					(membero b a)
					(== [c d] b)
					(membero e expr)
					(== c e)
					(== q c)))
(1))
"new approach"
"A rule is a s-expresion"

(defn split-listo [l erg]
  (project [l ]
       ;    (println "l ist " l " erg ist " erg)
           (== erg (split-list l))))
           

(declare match-commutativeo)

(defn apply-commutative-rule [rule expression]
  (run* [q]
       (fresh [patt trans n ]
              (== rule [patt trans])
              (match-commutativeo expression patt n)
              (== q trans))))





(comment (def rule (r/?-to-logic [(* ?x 1)  ?x]))
(def rule2 (r/?-to-logic [(* 0 ?x) 0]))

(def rule3 (r/?-to-logic [(ca+ ?x 1) ?x]))
(def rule4 (r/?-to-logic [(ca* ?x (+ ?a ?b)) (+ (ca* ?x ?a) (ca* ?x ?b))])))

(defn match-commutativeo [expr pat n]
  (conda
   ((== expr pat))
   ((fresh [exprsymb patsymb exprargs patargs split-list
            split-list-expr ng r mtchd a]
           (c/expo exprsymb exprargs expr)
           (c/expo patsymb patargs pat)
           (split-listo patargs split-list)
           (membero [ng r] split-list)
           (split-listo exprargs split-list-expr)
           (membero [ng a] split-list-expr)
           (match-commutativeo (* a) (* r) n)
           ))))

           
(comment 
(apply-commutative-rule rule3 (* 1 2))
(apply-commutative-rule rule4 (* 3 (+ 2 4))))


#_(next thing to do is to let the expression symbol match with the actual
        symbol. And in the expression match match recursively and with the
        right symbol. And make the transformation a function and not a
        pattern)


(defn not-nullo [x]
  (!= x 0))

(defn calculate [expr]
  (fn [result]
    (s/resulto expr result)))
(comment 
(def frule (?-to-logic [?expr (s/no-variablo ?expr) (calculate ?expr)]))

(run* [q] (fresh [pat guard trans]
					(== [pat guard trans] frule)
					(expression-matcho (* 10 2) pat)
					(project [guard] guard)
					(project [trans]
						 (trans q))))

)
