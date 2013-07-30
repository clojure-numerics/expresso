(ns numeric.expresso.properties
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [clojure.test])
  (:require [numeric.expresso.protocols]) 
  (:import [numeric.expresso.protocols Expression AtomicExpression])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [clojure.core.logic.unifier :as u]
            [clojure.core.matrix.operators :as mop]
            [clojure.core.matrix :as mat]
            [numeric.expresso.utils :as utils]
            [numeric.expresso.matcher :as match]))

(defmulti props identity)
(defmethod props :default [_]
  (if (= (str _) "clojure.core//") {:exec-func /
                                    :properties #{:n-ary}
                                    :inverse-op 'clojure.core/* }
      {}))
(defmethod props 'clojure.core/* [_] {:exec-func *
                                      :properies #{:associative
                                                   :commutative
                                                   :n-ary}
                                      })
(defmethod props 'clojure.core/+ [_] {:exec-func +
                                      :properties #{:associative :commutative :n-ary}})
(defmethod props 'clojure.core/- [_] {:exec-func -
                                      :properties [:n-ary [:inverse-of 'clojure.core/+]]})
(defmethod props 'clojure.core// [_] {:exec-func /
                                      :properties #{:n-ary} :inverse-of 'clojure.core/*})
(defmethod props 'e/ca-op [_] {:properties [:commutative]})
(defmethod props 'numeric.expresso.core/** [_] {:exec-func (fn [a b]
                                                             (Math/pow a b))})
(defmulti matcher identity)
(defmethod matcher :default [_] {:match-rel match/expression-matcho})
(defmethod matcher 'e/ca-op [_] {:match-rel match/match-commutativeo})


(defn zero-matrix? [expr]
  (loop [elem (mat/eseq expr)]
    (if (seq elem)
      (if (= 0 (first elem))
        (recur (rest elem))
        false)
      true)))

(defn extract-mzero [pargs expr]
  (project [pargs]
           (let [x (first pargs)]
             (if (and (meta x) (contains? (meta x) :mzero))
               (== x expr)
               (if (zero-matrix? expr)
                 (== x expr)
                 fail)))))

(defmulti extractor-rel identity)
(defmethod extractor-rel :default [_] nil)
(defmethod extractor-rel 'is? [_] match/extract-is)
(defmethod extractor-rel 'cons? [_] match/extract-cons)
(defmethod extractor-rel 'mzero? [_] extract-mzero)

(defn add-information [op]
  (merge {:expression true} (props op) (matcher op)))