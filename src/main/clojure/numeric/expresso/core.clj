(ns numeric.expresso.core
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [clojure.test])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [clojure.core.logic.unifier :as u]
            [numeric.expresso.utils :as utils]
            [numeric.expresso.construct :as c]))


(defn has-metao [q m]
  (== (meta q) (partial-map m)))

(defn is-commutativeo [exp]
  (fresh [m]
         (has-metao exp {:properties m})
         (membero :commutative m)))

(defn isao [a b]
  (project [a b]
  (== true (isa? a b))))

(defn expression-matcho [e1 e2]
  (conda
   ((== e1 e2))
   ((fresh [a b c d]
           (c/expo a b e1)
           (c/expo c d e2)
           (isao a c)
           (== b d))))
  )

(defn ce [symb & args]
  (list* symb args))

(defn replace-?-with-lvar [node]
  (if (and (symbol? node) (.startsWith (name node) "?"))
    (lvar node false)
    node))


(defn ?-to-lvar [code]
  (walk/prewalk replace-?-with-lvar code))


(defmacro with-? [& code]
  `(fresh []  ~@(?-to-lvar code)))

(defmacro ?-to-logic [code]
  (?-to-lvar code))
(def rule (?-to-logic [(ce `* ?x 1)  ?x]))

(defn apply-rule-simple [rule expression]
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
  (for [x (range (count v)) :when (not (lvar? (nth v x)))] 
    (let [elem (nth v x)
          left (take x v)
          right (drop (+ x 1) v)]
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
           (match-commutativeo (ce `* a) (ce `* r) n)
           ))))
         ;  (== n [exprsymb patsymb exprargs patargs])))))
           

(apply-commutative-rule rule (ce `* 1 2))