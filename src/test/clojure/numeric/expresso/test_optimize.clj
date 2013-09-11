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
            [numeric.expresso.impl.matcher :as m]
            [numeric.expresso.construct :as c]))


(deftest test-common-subexpressions
  (is (= [#{(ex (* 1 (* 2 3)))} #{(ex (* 2 3))}]
         (common-subexpressions (ex (+ (* 1 (* 2 3))  (+ (* 1 (* 2 3))))))))
  (is (= [] (common-subexpressions (ex (+ 3 4 (+ 1 2))))))
  (is (= [#{(ex (* 2 1)) (ex (* 1 2))}]
         (common-subexpressions (ex (+ (* 1 2) (* 2 1)))))))


(deftest test-evaluate-let
  (is (= 4 (evaluate (optimize (ex (+ (* 1 2) (* 2 1)))) {}))))

(deftest test-compile
  (is (= 8 ((compile-expr [x] (optimize (ex (+ (* x 2) (* 2 x))))) 2))))

(deftest test-optimize
  (is (= 3 (optimize (ex (+ 1 2)))))
  (is (= (ex (+ 3 x)) (optimize (ex (+ 1 2 x)))))
  (is (= (ex (* x (+ y z))) (optimize (ex (+ (* x y) (* x z))))))
  (is (= 0 (optimize (ex (+ x (- x))))))
  (is (= 0 (optimize (ex (- x x)))))
  (is (= 1 (optimize (ex (/ x x)))))
  (is (= 1 (optimize (ex (* x (/ x))))))
  (is (= 'x (optimize (ex (- (- x))))))
  (is (= (ex (sqrt x)) (optimize (ex (** x 0.5)))))
  (is (= (ex (* z (sum k 0 5 k) (** x 2)))
         (optimize (ex (sum k 0 5 (* x x z k))))))
  (is (= (ex (inner-product (inner-product a (inner-product b c)) d))
         (optimize (ex (inner-product 	^{:shape [40 20]} a
                                        ^{:shape [20 30]} b
                                        ^{:shape [30 10]} c
                                        ^{:shape [10 30]} d)))))
  (is (= (ex (inner-product (inner-product (inner-product a b) c) d))
         (optimize (ex (inner-product 	^{:shape [10 20]} a
                                        ^{:shape [20 30]} b
                                        ^{:shape [30 40]} c
                                        ^{:shape [40 30]} d))))))


(deftest test-emit-code*
  (is (= '(* x (+ y z)) (emit-code (ex (* x (+ y z))))))
  (is (= '(_0)
         (run* [q] (fresh[n res]
                         (== `(loop [~n (long 0) ~res 0]
                                (if (<= ~n 5)
                                  (let [~'k ~n]
                                    (recur (inc ~n)
                                           (clojure.core.matrix/add ~res ~'k)))
                                  ~res))
                             (emit-code (ex (sum k 0 5 k)))))))))


