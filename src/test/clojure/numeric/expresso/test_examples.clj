(ns numeric.expresso.test-examples
  (:use [clojure.test])
  (:use [numeric.expresso.construct])
  (:use [numeric.expresso.examples]))

(deftest test-transform-to-polynomial-normal-form
  (is (= (ex (** x 3))
         (to-polynomial-normal-form 'x (ex (+ (** x 3) (* 3 (** x 2))
                                              (- (* 2 (** x 2))
                                                 (* 5 (** x 2))))) )))
  (is (= (ex (+ (* 243.0 (** x 10)) (* 1215.0 (** x 9)) (* 4050.0 (** x 8)) (* 8910.0 (** x 7)) (* 15255.0 (** x 6)) (* 19683.0 (** x 5)) (* 20340.0 (** x 4)) (* 15840.0 (** x 3)) (* 9600.0 (** x 2)) (* 3840.0 x) 1024.0))
         (to-polynomial-normal-form 'x (ex (** (+ (* 3 x) 4 (* 3 (** x 2))) 5))))))