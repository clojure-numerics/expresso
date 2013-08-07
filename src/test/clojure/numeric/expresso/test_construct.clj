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
  (is (= '(+ 1 2 3) (ex (+ 1 2 3))))
  (is (= '(+ x y z a b) (ex (+ x y z a b))))
  (is (= '(+ x 3)) (let [x 3] (ex (+ x ~x)))))

(deftest test-ex'
  (is (= '(+ 1 2 3) (ex' (+ 1 2 3))))
  (is (= '(+ x y z a b) (ex' (+ 'x 'y 'z 'a 'b))))
  (is (= '(+ x y z a b) (ex' [x y z a b] (+ x y z a b))))
  (is (= '(+ c 3)) (let [x 3] (ex' [c] (+ c x)))))


(deftest test-to-poly-normal-form
  (is (= 7 (to-poly-normal-form '(+ 3 x 4 (- x)))))
  (is (= (poly 'x (poly 'y 0 2) 2) (to-poly-normal-form '(+ x y y x)))))