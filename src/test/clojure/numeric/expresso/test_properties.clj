(ns numeric.expresso.test-properties
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [numeric.expresso.properties]
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
            [numeric.expresso.utils :as utils]
            [numeric.expresso.matcher :as match]))


(def lhs (lvar 'lhs false))
(def rhs (lvar 'rhs false))
(def trans (lvar 'trans false))

(def v1 (add-constraint [lhs rhs] (== lhs rhs)))
(def v2 (add-constraint [lhs trans] (== lhs trans)))

(def vv1 (check-constraints v1))
(def vv2 (check-constraints v2))

(def cv (add-constraint [vv1 vv2] (== lhs rhs)))
(def cv (add-constraint cv (== lhs trans)))

(def ccv (check-constraints cv))

(deftest test-check-constraints
  (is (= [rhs rhs] vv1))
  (is (= [trans trans] vv2))
  (is (= 1 (count (into #{} (flatten ccv))))))

(deftest test-add-constraint
  (is (= #{0} (protocols/constraints (add-constraint 'a 0)))))