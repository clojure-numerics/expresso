(ns numeric.expresso.test-construct
  (:use numeric.expresso.construct)
  (:use clojure.test)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [clojure.test])
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.logic.unifier :as u]))



(deftest test-expo 
  (is (= [[1 2]] (run* [q] (fresh [ex op lhs rhs]
                                  (expo '+ [1 2] ex)
                                  (expo op [lhs rhs] ex)
                                  (== q [lhs rhs]))))))


(deftest test-ex
  (is (= '(clojure.core/* 1 2 (clojure.core/+ 3 4) 3 4 5)
         (ex `* 1 2 (ex `+ 3 4) [:numeric.expresso.construct/seq-match [3 4 5]]))))