(ns numeric.expresso.test-construct
  (:use numeric.expresso.construct)
  (:use [clojure.core.logic :exclude [is]]
        [clojure.test])
  (:refer-clojure :exclude [==])
  (:require [numeric.expresso.protocols :as protocols]
            [numeric.expresso.impl.pimplementation :as impl]))

(deftest test-to-expression
  (testing "a normal s-expression is converted to an expresso expression in an idempotent step"
    (let [sexp '(clojure.core/+ x 2)
          exp1 (to-expression sexp)
          exp2 (to-expression exp1)]
      (is (not (identical? exp1 sexp)))
      (is (identical? exp1 exp2)))))

(deftest test-ex
  (is (= '(+ 1 2 3) (ex (+ 1 2 3))))
  (is (= '(+ x y z a b) (ex (+ x y z a b))))
  (is (= '(+ x 3)) (let [x 3] (ex (+ x ~x)))))

(deftest test-ex'
  (is (= '(+ 1 2 3) (ex' (+ 1 2 3))))
  (is (= '(+ x y z a b) (ex' (+ 'x 'y 'z 'a 'b))))
  (is (= '(+ x y z a b) (ex' [x y z a b] (+ x y z a b))))
  (is (= '(+ c 3)) (let [x 3] (ex' [c] (+ c x)))))




(deftest test-shape-elemwise
  (is (= [] (protocols/shape (ex (+ 1 2 3)))))
  (is (= [2 2] (protocols/shape (ex (+ [[1 2][3 4]] 5)))))
  (is (= [] (protocols/shape (ex (+ 1 x 2)))))
  (is (= [] (let [expr (ex (+ 1 x 2))]
              (protocols/shape (impl/check-constraints
                                (protocols/add-constraint expr
                                                          [== (protocols/shape (nth expr 2)) []])))))))

(deftest test-shape-inner-product
  (is (= [] (protocols/shape (ex (inner-product 1 2)))))
  (is (= [] (protocols/shape (ex (inner-product 1 2 3 4 )))))
  (is (= [] (protocols/shape (ex (inner-product [1 2] [3 4])))))
  (is (= [2] (protocols/shape (ex (inner-product 2 [1 2])))))
  (is (= [2 2] (protocols/shape (ex (inner-product [[1 2][3 4]] 1 [[1 2][3 4]])))))
  (is (= [3 1] (protocols/shape (ex (inner-product [[1 2][3 4][5 6]] [[1][2]])))))
  (is (protocols/expr-op (protocols/shape (ex (inner-product 1 ^:matrix x [[1 2][3 4]]))))))