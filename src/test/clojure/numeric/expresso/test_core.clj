(ns numeric.expresso.test-core
  (:use numeric.expresso.core)
  (:use clojure.test)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [numeric.expresso.rules]
        [numeric.expresso.construct]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.logic.unifier :as u]))

(deftest test-simplify
  (is (= 4 (simplify (ex (+ 2 2)))))
  (is (= 137 (simplify (ex (+ (* 5 20) 30 7)))))
  (is (= 0 (simplify (ex (- (* 5 x) (* (+ 4 1) x))))))
  (is (= 0 (simplify (ex (* (/ y z) (- (* 5 x) (* (+ 4 1) x)))))))
  (is (= '(clojure.core/* 6 x) (simplify (ex (* 3 2 x)))))
  (is (= '(clojure.core/* 720 x y z) (simplify (ex (* 2 x 3 y 4 z 5 6)))))
  (is (= 7 (simplify (ex (+ x 3 4 (- x))))))
  (is (= 3 (simplify (ex (** e (ln (+ 3 0 (* 0 42))))))))
  (is (= '(sin (clojure.core/* 12 (numeric.expresso.core/** x 3)))
         (simplify (ex (sin (diff (* (** x 4) (/ (* 3 x) x)) x)))))))


(deftest test-transform-to-polynomial-normal-form
  (is (= '(numeric.expresso.core/** x 3)
         (to-polynomial-normal-form 'x (ex (+ (** x 3) (* 3 (** x 2))
                                           (- (* 2 (** x 2))
                                              (* 5 (** x 2))))) )))
  (is (= '(clojure.core/+ (clojure.core/* 243.0 (numeric.expresso.core/** x 10)) (clojure.core/* 1215.0 (numeric.expresso.core/** x 9)) (clojure.core/* 4050.0 (numeric.expresso.core/** x 8)) (clojure.core/* 8910.0 (numeric.expresso.core/** x 7)) (clojure.core/* 15255.0 (numeric.expresso.core/** x 6)) (clojure.core/* 19683.0 (numeric.expresso.core/** x 5)) (clojure.core/* 20340.0 (numeric.expresso.core/** x 4)) (clojure.core/* 15840.0 (numeric.expresso.core/** x 3)) (clojure.core/* 9600.0 (numeric.expresso.core/** x 2)) (clojure.core/* 3840.0 x) 1024.0)
         (to-polynomial-normal-form 'x (ex (** (+ (* 3 x) 4 (* 3 (** x 2))) 5))))))

(deftest test-rearrange
  (is (= '(clojure.core/= x (clojure.core/- 4 1))
          (rearrange 'x (ex (= (+ 1 x) 4))))))
         
