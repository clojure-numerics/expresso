(ns mikera.expresso.scratch
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.logic.unifier :as u]))

(run* [q]
      (fresh [a b] 
             (== [a q b] '(1 2 3))))

(defn expo [op params ex]
  (conso op params ex))
;; (run* [q] (fresh [a b] (expo '+ [a b] q)))
;; => ((+ _0 _1))

(defn inco [a res]
  (project [a]
           (== res (inc a))))

(defn mapo [fo vs rs]
  (conda
    [(emptyo vs) (emptyo rs)]
    [(fresh [v r restvs restrs]
            (conso v restvs vs)
            (conso r restrs rs)
            (fo v r)
            (mapo fo restvs restrs))]))
;; (run* [q] (mapo inco [1 2] q))

(defn resulto 
  "Computes the arithmetical result of an expression. Not relational."
  ([exp v]
    (conda 
      [(pred exp number? ) (== v exp)]
      [(fresh [op params eparams]
              (expo op params exp)
              (mapo resulto params eparams)
              (project [eparams op] (== v (apply op eparams))))])))
;; (run* [q] (resulto 10 q))
;; => 10
;;
;; (run* [q] (resulto [+ 5 6] q))
;; => 11

(defn equivo [a b]
  (resulto [- a b] 0 ))


;; (run* [q] (equivo [+ 4 5] [+ 1 8]))
