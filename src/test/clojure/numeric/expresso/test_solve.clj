(ns numeric.expresso.test-solve
  (:use numeric.expresso.solve)
  (:use clojure.test)
  (:use numeric.expresso.rules)
  (:use numeric.expresso.construct)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        clojure.test)
  (:require [numeric.expresso.construct :as c])
  (:require [clojure.core.matrix :as matrix])
  (:require [clojure.core.matrix.operators :as mop])
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.logic.unifier :as u]))


(deftest test-matrix-simplification-rules
  (is (matrix/e== (matrix/broadcast 0 [2 2]) (apply-rules
                      matrix-simplification-rules
                      (ex (matrix/mul [[1 2][3 4]] [[0 0][0 0]])))))
  (is (matrix/e== (matrix/broadcast 0 [3 2]) (apply-rules
                      matrix-simplification-rules
                      (ex (matrix/mul [[1 2][3 4] [5 6]] [[0 0][0 0]]))))))


(deftest test-solve-linear-system
  (is (= '#{{x 3}} (solve-linear-system '[x] [(ex (= x y))
                                       (ex (= y 3))])))
  (is (= '#{{z _1 y _0 x 3}}
         (solve-linear-system '[x y z] [(ex (= x 3))
                               (ex (= y y))
                               (ex (= z z))])))
  (is (= nil
         (solve-linear-system '[x] [(ex (= x (+ x 1)))])))
  (is (= '#{{y _0 x _0}}
         (solve-linear-system '[x y] [(ex (= x y))])))
  (is (= '#{{x 180/7 y 40/7}}
         (solve-linear-system '[x y] [(ex (= (+ (* 3 x) (* 4 y)) 100))
						   (ex (= (- x y) 20))]))))

(deftest test-solve-system
  (is (= #{{'y [3 6 9]}}
         (solve-system '[y]
                       #{(ex (= z (mop/* 2 x)))
                         (ex (= y (mop/+ x z)))
                         (ex (== x [1 2 3]))})))
  (is (= #{{'y [3 6 9]
          'z [2 4 6]
          'x [1 2 3]}}
         (solve-system '[y z x]
                       #{(ex (= z (mop/* 2 x)))
                         (ex (= y (mop/+ x z)))
                         (ex (== x [1 2 3]))})))
  (is (= #{{'x 2}} (solve-system '[x] #{(ex (= (+ x y) 3))
				     (ex (= y 1))})))
  (is (= #{{'x 1}} (solve-system '[x] #{(ex (= (+ x y) 3))
                                       (ex (= (+ x 1) y))})))
  (is (= '#{{y (+ 7 (* -8 (/ (+ a b)) a)), x (* 8 (/ (+ a b)))}}
         (solve-system '[x y] #{(ex (= (+ (* a x) y) 7))
                                (ex (= (- (* b x) y) 1))})))
  (is (= '#{{y (+ (* a 1/2) (* -1/4 (sqrt (+ (* -4.0 (** a 2)) 8)))),
            x (+ (* 1/2 a) (* (sqrt (+ (* -4.0 (** a 2)) 8)) 1/4))}
           {y (+ (* a 1/2) (* -1/4 (- (sqrt (+ (* -4.0 (** a 2)) 8))))),
            x (+ (* 1/2 a) (* (- (sqrt (+ (* -4.0 (** a 2)) 8))) 1/4))}}
         (solve-system '[x y] #{(ex (= (+ (** x 2) (** y 2)) 1))
					       (ex (= (+ x y) a))}))))