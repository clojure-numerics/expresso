(ns numeric.expresso.utils
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.walk :as walk])
  (:require [clojure.core.logic.unifier :as u]))

(def debug-mode true)

(defmacro debug [vars & message]
  `(project ~vars
            (do (when debug-mode
                  (prn ~@message)) (== 1 1))))




(defn mapo [fo vs rs]
  (conda
    [(emptyo vs) (emptyo rs)]
    [(fresh [v r restvs restrs]
            (conso v restvs vs)
            (conso r restrs rs)
            (fo v r)
            (mapo fo restvs restrs))]))

(defn lifto-with-inverse
  "Lifts a unary function and its inverse into a core.logic relation."
  ([f g]
    (fn [& vs]
      (let [[x y] vs]
        (conda 
          [(pred x number?) (project [x] (== y (f x)))]
          [(pred y number?) (project [y] (== x (g y)))])))))


(defn constant? [expr]
  (number? expr))


(defn resolve-opo 
  "Resolves an operator to an actual function"
  ([op resolved-fn]
    (fresh []
      (project [op]
           (== resolved-fn @(resolve op)))))) 

(defn applyo 
  "Applies a logic function to a set of parameters."
  ([fo params result]
    (fresh []
           (project [params]
                    (apply fo (concat params (list result)))))))


(defn inco [a res]
  (project [a]
           (== res (inc a))))




(defn without-symbol? [sym expr]
  (cond
    (and (symbol? expr) (= sym expr)) false
    (sequential? expr) (every? #(without-symbol? sym %) expr)
    :else true))


(defn expo 
  "Creates an expression with the given operator and parameters"
  ([op params exp]
     (conso op params exp)))


(defn extract [c]
  (mapcat #(if (and (coll? %) (= (first %) :numeric.expresso.construct/seq-match)) (second %) [%]) c))


(defn splice-in-seq-matchers [expr]
  (walk/postwalk (fn [expr] (if (coll? expr) (extract expr) expr)) expr))
(defn expo 
  "Creates an expression with the given operator and parameters"
  ([op params exp]
     (conso op params exp)))


(defn extract [c]
  (mapcat #(if (and (coll? %) (= (first %) :numeric.expresso.construct/seq-match)) (second %) [%]) c))


(defn splice-in-seq-matchers [expr]
  (walk/postwalk (fn [expr] (if (coll? expr) (extract expr) expr)) expr))