(ns numeric.expresso.properties
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [clojure.test])
  (:import [numeric.expresso.protocols Expression AtomicExpression])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [clojure.core.logic.unifier :as u]
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
(defmulti matcher identity)
(defmethod matcher :default [_] {:match-rel match/expression-matcho})
(defmethod matcher 'e/ca-op [_] {:match-rel match/match-commutativeo})

(defmulti extractor-rel identity)
(defmethod extractor-rel :default [_] nil)
(defmethod extractor-rel 'is? [_] match/extract-is)
(defmethod extractor-rel 'cons? [_] match/extract-cons)

(defn add-information [op]
  (merge (props op) (matcher op)))