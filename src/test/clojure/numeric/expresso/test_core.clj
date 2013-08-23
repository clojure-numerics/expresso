(ns numeric.expresso.test-core
  (:use numeric.expresso.core)
  (:use clojure.test)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        clojure.test)
  (:require [numeric.expresso.protocols :as protocols])
  (:require [clojure.core.logic.unifier :as u]))

(deftest test-simplify
  (is (= 4 (simplify (ex (+ 2 2)))))
  (is (= 137 (simplify (ex (+ (* 5 20) 30 7)))))
  (is (= 0 (simplify (ex (- (* 5 x) (* (+ 4 1) x))))))
  (is (= 0 (simplify (ex (* (/ y z) (- (* 5 x) (* (+ 4 1) x)))))))
  (is (= (ex (* 6 x)) (simplify (ex (* 3 2 x)))))
  (is (= (ex (* 720 x y z)) (simplify (ex (* 2 x 3 y 4 z 5 6)))))
  (is (= 7 (simplify (ex (+ x 3 4 (- x)))))))

(deftest test-transform-to-polynomial-normal-form
  (is (= (ex (+ (** x 3)))
         (to-polynomial-normal-form 'x (ex (+ (** x 3) (* 3 (** x 2))
                                              (- (* 2 (** x 2))
                                                 (* 5 (** x 2))))) )))
  (is (= (ex (+ 1024 (* 3840 x) (* 9600 (** x 2)) (* 15840 (** x 3))
                (* 20340 (** x 4)) (* 19683 (** x 5)) (* 15255 (** x 6))
                (* 8910 (** x 7)) (* 4050 (** x 8)) (* 1215 (** x 9))
                (* 243 (** x 10))))
         (to-polynomial-normal-form 'x (ex (** (+ (* 3 x) 4 (* 3 (** x 2))) 5))))))

(deftest test-rearrange
  (is (= [(ex (= x (- 4 1)))]
         (rearrange 'x (ex (= (+ 1 x) 4))))))


(deftest test-solve
  (is (= #{2} (solve '#{x} (ex (= (+ 1 x) 3)))))
  (is (= '#{} (solve '#{x} (ex (= x (+ x 1))))))
  (is (= '_0 (solve '#{x} (ex (= x x)))))
  (is (= '#{(arcsin 0) 1} (solve '#{x} (ex (= (* (sin x) (- x 1)) 0)))))
  (is (= #{4} (solve '#{x} (ex (= (+ 1 (* 2 (- 3 (/ 4 x)))) 5))))) 
  (is (= #{-4}
         (solve '#{x} (ex (= (* 3 x) (+ (* 4 x) 4))))))
  (is (= '#{(* 1/2 (+ (- a) (sqrt (+ (** a 2) -4))))
           (* 1/2 (+ (- a) (- (sqrt (+ (** a 2) -4)))))}
         (solve '#{x} (ex (= (+ (** x 2) (* a x) 1) 0)))))
  (is (= '#{{y (+ (* a 1/2) (* -1/4 (- (sqrt (+ (* -4.0 (** a 2)) 8))))),
             x (+ (* 1/2 a) (* (- (sqrt (+ (* -4.0 (** a 2)) 8))) 1/4))}
            {y (+ (* a 1/2) (* -1/4 (sqrt (+ (* -4.0 (** a 2)) 8)))),
             x (+ (* 1/2 a) (* (sqrt (+ (* -4.0 (** a 2)) 8)) 1/4))}}
       (solve '[x y] (ex (= (+ (** x 2) (** y 2)) 1))
                (ex (= (+ x y) a))))))

(deftest test-differentiate
  (is (= (ex (* 2 x)) (differentiate '[x] (ex (** x 2)))))
  (is (= 2 (differentiate '[x x] (ex (** x 2)))))
  (is (= (ex (* 3 (** x 2))) (differentiate '[x] (ex (** x 3)))))
  (is (= (ex (* 12 (** x 3)))
         (differentiate '[x] (ex (* (** x 3) (* 3 x)))))))

(deftest test-compile-expr
  (is (= 4 ((compile-expr [] (ex (+ (* 1 2) (* 2 1)))))))
  (is (= 8 ((compile-expr [x] (ex (+ (* x 2) (* 2 x)))) 2))))

(deftest test-optimize
  (is (= 4 (evaluate (optimize (ex (+ (* 1 2) (* 2 1)))) {})))
  (is (= 8 (evaluate (optimize (ex (+ (* x 2) (* 2 x)))) {'x 2}))))

