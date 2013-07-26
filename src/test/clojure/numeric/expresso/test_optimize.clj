(ns numeric.expresso.test-optimize
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [numeric.expresso.construct]
        [numeric.expresso.properties :as props]
        [numeric.expresso.protocols]
        [numeric.expresso.optimize]
        [numeric.expresso.rules]
        [clojure.test])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [clojure.core.logic.unifier :as u]
            [numeric.expresso.utils :as utils]
            [numeric.expresso.solve :as s]
            [clojure.core.matrix :as matrix]
            [clojure.core.matrix.operators :as mop]
            [numeric.expresso.matcher :as m]
            [numeric.expresso.construct :as c]))


(deftest test-common-subexpressions
  (is (= [#{(ex (* 1 (* 2 3)))} #{(ex (* 2 3))}]
         (common-subexpressions (ex (+ (* 1 (* 2 3))  (+ (* 1 (* 2 3))))))))
  (is (= [] (common-subexpressions (ex (+ 3 4 (+ 1 2))))))
  (is (= [#{(ex (* 2 1)) (ex (* 1 2))}]
         (common-subexpressions (ex (+ (* 1 2) (* 2 1)))))))



(deftest test-evaluate-let
  (is (= 4 (evaluate (optimize* (ex (+ (* 1 2) (* 2 1)))) {}))))

(deftest test-compile
  (is (= 8 ((compile-expr (optimize* (ex (+ (* x 2) (* 2 x))))) {'x 2}))))
