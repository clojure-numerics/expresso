(ns numeric.expresso.impl.symbolic
  (:refer-clojure :exclude [record?])
  (:use [clojure.core.logic.protocols]
        [numeric.expresso.impl.matcher]
        [numeric.expresso.protocols]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd :exclude [record?]]
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

(defn swap-rows [mat i j]
  (if (== i j) mat
      (let [n (mat/row-count mat)]
        (loop [index 0  nrows (transient [])]
          (if (< index n)
            (recur (inc index) (conj! nrows
                                      (cond
                                       (== index i) (mat/get-row mat j)
                                       (== index j) (mat/get-row mat i)
                                       :else (mat/get-row mat index))))
            (mat/matrix (persistent! nrows)))))))
  
  (defn multiply-row [row m] (mat/emap #(* %1 m) row))
(defn add-rows [row1 row2] (mat/emap + row1 row2))

(defn set-row [mat pos row]
  (let [n (mat/row-count mat)]
    (loop [index 0 nrows (transient [])]
      (if (< index n)
        (recur (inc index) (conj! nrows
                                  (if (== index pos)
                                    row
                                    (mat/get-row mat index))))
        (mat/matrix (persistent! nrows))))))


(defn ffgaus-step [mat prowpos pcolpos div]
  (let [prow (mat/get-row mat prowpos)
        pivot (mat/mget mat prowpos pcolpos)
        n (mat/row-count mat)]
    (loop [index (inc prowpos) mat mat]
      (if (< index n)
        (let [ aktrow (mat/get-row mat index)
              aktpivot (mat/mget mat index pcolpos)
              nrow (multiply-row (add-rows (multiply-row aktrow pivot)
                                           (multiply-row prow (* -1 aktpivot)))
                                 (/ 1 div))]
          (recur (inc index) (set-row mat index nrow)))
        mat))))
                          
                

(defn ff-gauss-echelon [mat]
  (let [n (mat/row-count mat) m (mat/column-count mat)]
    (loop [index 0 indexcol 0 mat mat div 1]
      (if (and (< (inc index) n) (< indexcol m))
        (let [pivot (mat/mget mat index indexcol)
              swap (loop [k index pivot pivot]
                     (cond (== (inc k) n) false
                           (== 0 pivot)  (recur (inc k)
                                                (mat/mget mat (inc k) indexcol))
                           :else k))]
            (if swap 
              (recur (inc index) (inc indexcol)
                     (let [res (ffgaus-step (swap-rows mat index swap)
                                            index indexcol div)]
                       res)
                     (let [ndiv (mat/mget mat index indexcol)]
                       (if (== 0 ndiv) div ndiv)))
              (recur index (inc indexcol) mat div)))
        mat))))

(defn find-elim-pivot [mat index]
  (let [m (dec (mat/column-count mat))]
    (loop [row index col 0]
      (if (== (mat/mget mat row col) 0)
        (if (== col m)
          (if (== 0 row)
            [0 0]
            (recur (dec row) 0))
          (recur row (inc col)))
        [row col]))))
          
(defn ff-gauss-reduced-echelon [[mat index]]
  ;;search pivot element for resub
  (let [n (mat/row-count mat) m (mat/column-count mat)
        [prowi pcoli] (find-elim-pivot mat index)]
    [prowi pcoli]))



(defn check-zero-or-inf-sols [mat]
  ;;if there is one butzero line no solution
  (let [cc (mat/column-count mat)
        rows (mat/rows mat)
        but-zero-lines
        (some #{true} (map (fn [e] (and (every? #(== 0 %) (butlast e))
                                          (not (== 0 (last e))))) rows))
        zero-lines (filter #{true} (map (fn [e] (every? #(== 0 %) e)) rows))
        det-row-count (- (mat/row-count mat) (count zero-lines))]
    (if but-zero-lines :zero
        (if (== cc (inc det-row-count)) :one
            (if (>= det-row-count cc) :zero :infinitive)))))


(defn s+ [a b]
  (if (and (number? a) (number? b))
    (+ a b)
    (c/ce `+ a b)))

(defn s- [a b]
  (if (and (number? a) (number? b))
    (- a b)
    (c/ce `- a b)))

(defn s* [a b]
  (if (and (number? a) (number? b))
    (* a b)
    (c/ce `* a b)))

(defn sd [a b]
  (if (and (number? a) (number? b))
    (/ a b)
    (c/ce `/ a b)))

(defn pivot-index [row]
  (loop [i 0]
    (if (< i (mat/ecount row))
      (if (== (mat/mget row i) 0) (recur (inc i)) i))))

(defn sort-rows [m]
  (let [rows (mat/rows m)]
    (mat/matrix
     (sort-by pivot-index rows))))

(defn remove-zeros [m]
  (->> (mat/rows m) (remove #(every? (fn [x] (== x 0)) %)) mat/matrix))

(defn add-zeros [m]
  (let [rows (vec (mat/rows m))
        cc (mat/column-count m)
        rc (mat/row-count m)]
    (loop [i 0 rows rows]
      (if (< i rc)
        (if-let [pi (pivot-index (nth rows i))]
          (if (> pi i)
            (recur (inc i) (vec (concat
                                 (subvec rows 0 i)
                                 (repeat (- pi i) (mat/new-vector cc))
                                 (subvec rows i))))
            (recur (inc i) rows))
          (recur (inc i) rows))
        (mat/matrix rows)))))


(defn solution-vec [m]
  (let [cc (mat/column-count m)
        row (- cc 2) col (- cc 2)
        m (-> m remove-zeros sort-rows add-zeros)
        m (if (< 0 (- cc (mat/row-count m) 1))
            (mat/matrix (concat (mat/rows m)
                                (repeat (- cc (mat/row-count m) 1)
                                        (mat/new-vector cc))))
            m)]   
      (loop [row row numbv 0 solv []]
        (if (< row 0)
          solv
          (if (== 0 (mat/mget m row row))
            (recur (dec row) (inc numbv) (conj solv (symbol (str "_" numbv))))
            (recur (dec row) numbv
                   (conj solv (sd (s- (mat/mget m row (dec cc))
                                      (loop [col (- cc 2) i 0 res 0]
                                        (if (<= col row) res
                                            (recur (dec col) (inc i)
                                                   (s+ res (s* (mat/mget m row col)
                                                               (nth solv i)))))))
                                  (mat/mget m row row)))))))))
(defn report-solution [echelon-matrix]
  (let [zero-inf? (check-zero-or-inf-sols echelon-matrix)]
    (cond
     (= zero-inf? :zero) '()
     (= zero-inf? :infinite) '(_0)
     :else (into [] (reverse (solution-vec echelon-matrix))))))


(defn gaus-solve [matrix]
  (report-solution (ff-gauss-echelon matrix)))

