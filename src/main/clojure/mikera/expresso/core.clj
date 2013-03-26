(ns mikera.expresso.core
  (:use [mikera.cljutils error])
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.logic.unifier :as u]))

(set! *warn-on-reflection* true)
(set! *unchecked-math* true)

(declare ex*)

(defn- express-list 
  ([[op & exprs]]
    (cons op (map ex* exprs))))

(defn ex* 
  ([expr]
    (cond 
      ;; an operation with child expressions
      (sequential? expr)
        (let [childs (express-list expr)]
          childs)
        
      ;; a symbol
      (symbol? expr)
        expr
        
      ;; else must be a constant
      :else
        expr)))

(defmacro ex 
  "Constructs an Expression."
  ([expr]
    `(quote ~(ex* expr))))

(defn constant? [expr]
  (number? expr))

;; logic stuff

(defn lifto
  "Lifts a function into a core.logic relation."
  ([f]
    (fn [& vs]
      (project [vs] (== (last vs) (apply f (butlast vs)))))))

(def NO_MATCH (Object.))

(defn lifto-with-inverse
  "Lifts a unary function into a core.logic relation."
  ([f g]
    (fn [& vs]
      (let [[x y] vs]
        (conda 
          [(project [x] (== y (if (number? x) (f x) NO_MATCH)))]
          [(project [y] (== x (if (number? y) (g y) NO_MATCH)))])))))

(defn mapo [fo vs rs]
  (conda
    [(emptyo vs) (emptyo rs)]
    [(fresh [v r restvs restrs]
            (conso v restvs vs)
            (conso r restrs rs)
            (fo v r)
            (mapo fo restvs restrs))]))


(defn expo 
  "Creates an expression with the given operator and parameters"
  ([op params exp]
    (== (ex* (cons op params)) exp)))


(defn simplifico 
  "Determines the simplified form of an expression."
  ([a b]
    nil))

(defn resulto 
  "Computes the arithmetical result of an expression. Not relational."
  ([exp v]
    (conda 
      [(pred exp number? ) (== v exp)]
      [(fresh [op params eparams]
              (expo op params exp)
              (mapo resulto params eparams)
              ((lifto op) eparams v))])))

(defn equivo [a b]
  (let [diff `(- ~a ~b)]
    (conda 
      [(fresh [s] (== 0 (simplifico s diff)))]
      [(resulto diff 0)])))

(comment
  (run* [q] 
        (fresh [a b]
          (== (ex [+ 2 4]) [a b q] )))
  
  (run* [q]
        (expo + [1 2] q))
  
  (run* [q] (resulto (ex (+ 2 3)) q))
  
  )