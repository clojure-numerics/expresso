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

(declare ex* mapo resulto)

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
      (fresh [res args]
        (== res (last vs))
        (mapo resulto (butlast vs) args)
        (project [f args]
             (== res (apply f args)))))))

(defn lifto-with-inverse
  "Lifts a unary function and its inverse into a core.logic relation."
  ([f g]
    (fn [& vs]
      (let [[x y] vs]
        (conda 
          [(pred x number?) (project [x] (== y (f x)))]
          [(pred y number?) (project [y] (== x (g y)))])))))

(defn mapo [fo vs rs]
  (conda
    [(emptyo vs) (emptyo rs)]
    [(fresh [v r restvs restrs]
            (conso v restvs vs)
            (conso r restrs rs)
            (fo v r)
            (mapo fo restvs restrs))]))

(defn applyo 
  "Applies a logic function to a set of parameters."
  ([fo params result]
    (fresh []
           (project [params]
             (apply fo (concat params (list result)))))))

(defn expo 
  "Creates an expression with the given operator and parameters"
  ([op params exp]
    (conso op params exp)))

(defn resolve-opo 
  "Resolves an operator to an actual function"
  ([op resolved-fn]
    (fresh []
      (project [op]
           (== resolved-fn @(resolve op)))))) 


(defn resulto 
  "Computes the arithmetical result of an expression. Not relational."
  ([exp v]
    (conda 
      [(pred exp number?) 
       (== v exp)]
      [(pred exp sequential?)
       (fresh [op rop params]
              (expo op params exp)
              (resolve-opo op rop) 
              (applyo (lifto rop) params v))])))


(defn without-symbol? [sym expr]
  (cond
    (and (symbol? expr) (= sym expr)) false
    (sequential? expr) (every? #(without-symbol? sym %) expr)
    :else true))

(defn simplifico 
  "Determines the simplified form of an expression."
  ([a b]
    (conde
      [(resulto a b)])))


(defn equivo [a b]
  (let [diff `(- ~a ~b)]
    (conda 
      [(fresh [s] (== 0 (simplifico s diff)))]
      [(resulto diff 0)])))

(defn rearrangeo 
  "Re-arranges an equality expression."
  ([orig res]
    (conde 
      [(== orig res)]
      [(fresh [s x] (== orig ['= x s]) (simplifico s res))])))

(defn expresso 
  "Expresses a symbol as a formula"
  ([sym expr result]
    (fresh [r]
           (rearrangeo expr r)
           (== ['= sym result] r)
           (pred result #(without-symbol? sym %)))))

(comment
  (run* [q] 
        (fresh [a b]
          (== (ex [+ 2 4]) [a b q] )))
  
  (run* [q]
        (expo + [1 2] q))
  
  (run* [q] (resulto (ex (+ 2 3)) q))
  
  )