(ns numeric.expresso.properties
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [clojure.test])
  (:require [numeric.expresso.protocols :as protocols]) 
  (:import [numeric.expresso.protocols Expression AtomicExpression])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [clojure.core.logic.unifier :as u]
            [clojure.core.matrix.operators :as mop]
            [clojure.core.matrix :as mat]
            [clojure.set :as set]
            [numeric.expresso.types :as types]
            [numeric.expresso.utils :as utils]
            [numeric.expresso.matcher :as match]))



(defmulti props identity)
(defmethod props :default [_] {})
(defmethod props '* [_] {:exec-func *
                         :properties #{:associative
                                      :commutative
                                      :n-ary}
                         })
(defmethod props '+ [_] {:exec-func +
                         :properties #{:associative :commutative :n-ary}})
(defmethod props '- [_] {:exec-func -
                         :properties [:n-ary [:inverse-of 'clojure.core/+]]})
(defmethod props '/ [_] {:exec-func /
                         :properties #{:n-ary} :inverse-of 'clojure.core/*})
(defmethod props 'e/ca-op [_] {:properties [:commutative]})
(defmethod props '** [_] {:exec-func (fn [a b]
                                       (Math/pow a b))})
(defmethod props 'emul [_] {:exec-func mat/emul})
(defmethod props 'div [_] {:exec-func mat/div})
(defmethod props 'add [_] {:exec-func mat/add})
(defmethod props 'sub [_] {:exec-func mat/sub})
(defmethod props 'inner-product [_] {:exec-func mat/inner-product})
(defmethod props 'negate [_] {:exec-func mat/negate})


(defmulti matcher first)
(defmethod matcher :default [_]
  (if (contains? (:properties (second _)) :commutative)
    {:match-rel match/match-commutativeo}
    {:match-rel match/expression-matcho}))
(defmethod matcher 'e/ca-op [_] {:match-rel match/match-commutativeo})


(defn zero-matrix? [expr]
  (if (symbol? expr)
    false
    (loop [elem (mat/eseq expr)]
      (if (seq elem)
        (if (clojure.core/== 0 (first elem))
          (recur (rest elem))
          false)
        true))))

(defn identity-matrix? [expr]
  (if (symbol? expr) false
      (let [d (mat/dimensionality expr)]
        (cond
         (clojure.core/== d 0) (clojure.core/== expr 0)
         (clojure.core/== d 1) (and (clojure.core/== (count expr) 1)
                                    (clojure.core/== (first expr) 0))
         (clojure.core/== d 2)
         (let [rc (mat/row-count expr)
               cc (mat/column-count expr)]
           (loop [i 0]
             (if (< i rc)
               (if (nil? (loop [j 0]
                           (if (< j cc)
                             (let [elem (mat/mget expr i j)]
                               (cond
                                (clojure.core/== elem 0) (if (clojure.core/== i j)
                                                           false
                                                           (recur (inc j)))
                                (clojure.core/== elem 1) (if (clojure.core/== i j)
                                                           (recur (inc j))
                                                           false)
                                :else false)))))
                 (recur (inc i))
                 false)
               true)))))))
      
(defn extract-mzero [pargs expr]
  (project [pargs expr]
           (let [x (first pargs)]
             (if (contains? (protocols/properties expr) :mzero)
               (== x expr)
               (if (zero-matrix? expr)
                 (== x expr)
                 fail)))))

(defn extract-midentity [pargs expr]
  (project [pargs expr]
           (let [x (first pargs)]
             (if (contains? (protocols/properties expr) :midentity)
               (== x expr)
               (if (identity-matrix? expr)
                 (== x expr)
                 fail)))))

(defmulti extractor-rel identity)
(defmethod extractor-rel :default [_] nil)
(defmethod extractor-rel 'is? [_] match/extract-is)
(defmethod extractor-rel 'cons? [_] match/extract-cons)
(defmethod extractor-rel 'mzero? [_] extract-mzero)
(defmethod extractor-rel 'midentity? [_] extract-midentity)

(defn add-information [op]
  (let [p (props op)
        m (matcher [op p])]
    (merge {:expression true} p m)))




(defn is-number? [x]
  (or (number? x) (isa? (protocols/type-of x) types/number)))