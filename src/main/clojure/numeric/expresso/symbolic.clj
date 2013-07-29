(ns numeric.expresso.symbolic
  (:refer-clojure :exclude [])
  (:use [clojure.core.logic.protocols]
        [numeric.expresso.matcher]
        [numeric.expresso.protocols]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [clojure.core.matrix.operators :as matop]
            [numeric.expresso.utils :as utils]
            [clojure.core.matrix :as mat]
            [numeric.expresso.construct :as c]))

(def plus (partial mat/emap (partial c/ce `+)))
(defn emul [m s]
  (mat/emap (partial c/ce `* s) m))
(def scale emul)

(defn vector-dot [a b]
  (reduce (partial c/ce `+) (map (partial c/ce `*) a b)))
(defn mul [m a]
  (let [mdims (long (mat/dimensionality m))
        adims (long (mat/dimensionality a))]
    (cond
     (== adims 0) (scale m a)
     (and (== mdims 1) (== adims 2))
     (vec (for [i (range (mat/dimension-count a 1))]
            (let [r (mat/get-column a i)]
              (vector-dot m r))))
     (and (== mdims 2) (== adims 2))
     (mapv (fn [r]
             (vec (for [j (range (mat/dimension-count a 1))]
                    (vector-dot r (mat/get-column a j))))) m))))

(def testmatrix [[3 4 -2 1 -2]
                 [1 -1 2 2 7]
                 [4 -3 4 -3 2]
                 [-1 1 6 -1 1]])


(defn gaus-solve [m]
  (let [rc (mat/row-count m)
        cc (mat/column-count m)
        mm (mat/mutable-matrix m)]
    (loop [k 0 m m]
      (if (== k rc)
        m
        (recur (+ k 1)
               (let [p (mat/mget m k k)
                     prow (mat/mget m k)]
                 (loop [si (range (+ k 1) rc) m m]
                   (if (seq si)
                     (let [i (first si)
                           aktrow (mat/mget m i)
                           pakt (mat/mget m i k)]
                       (recur (rest si) (->> aktrow (mapv #(- %2 (* (/ pakt p) %1)) prow)
                                             (mat/mset m i))))
                     m))))))))
      