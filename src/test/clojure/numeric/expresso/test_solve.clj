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
                       #{(ex (= z (* 2 x)))
                         (ex (= y (+ x z)))
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
  (is (= '#{{y (+ 7 (* -8 (/ (+ b a)) a)), x (* 8 (/ (+ b a)))}}
         (solve-system '[x y] #{(ex (= (+ (* a x) y) 7))
                                (ex (= (- (* b x) y) 1))})))
  (is (= '#{{y (+ (* a 1/2) (* -1/4 (sqrt (+ (* -4.0 (** a 2)) 8)))),
            x (+ (* 1/2 a) (* (sqrt (+ (* -4.0 (** a 2)) 8)) 1/4))}
           {y (+ (* a 1/2) (* -1/4 (- (sqrt (+ (* -4.0 (** a 2)) 8))))),
            x (+ (* 1/2 a) (* (- (sqrt (+ (* -4.0 (** a 2)) 8))) 1/4))}}
         (solve-system '[x y] #{(ex (= (+ (** x 2) (** y 2)) 1))
                                (ex (= (+ x y) a))}))))

(deftest test-solve-square-roots
  (is (= #{9.0} (solve 'x (ex (= (+ (sqrt x) (sqrt (- x 5))) 1)))))
  (is (= #{1.0 -4.2444444444444445}
         (solve
          'x (ex (= (+ (sqrt (+ x 8)) (sqrt (+ x 15))) (sqrt (+ (* 9 x) 40)))))))
  (is (= #{1.0 -0.017994858611825194}
         (solve
          'x (ex (= (+ (sqrt (+ (* 5 x) 4))
                       (sqrt (+ (* 7 x) 2)))
                    (sqrt (+ (* 35 x) 1)))))))
  (is (= #{4.999999999999999 0.39167589808513964}
         (solve
          'x (ex (= (- (* 7 (sqrt (- (* 2 x) 1)))
                       (* 8 (sqrt (- x 1))))
                    (* 10 (sqrt (/ (- x 4) 4))))))))
  (is (= #{8.165253628132167 4.890301927423389}
         (solve
          'x (ex (= (- (sqrt (- (* 9 x) 14)) (sqrt (+ (* 3 x) 6)))
                    (sqrt (/ (- (* 6 x) 25) 5))))))))

(deftest test-solve-fractions
  (is (= #{5} (solve
               'x (ex (= (+ (/ (- x 3))
                            (/ (+ x 3)))
                         (/ 10 (- (** x 2) 9)))))))
  (is (= #{} (solve
              'x (ex (= (/ 1 (- x 2))
                        (- (/ 3 (+ x 2))
                           (/ (* 6 x) (- (** x 2) 4))))))))
  (is (= #{0.7588723439378913 -0.6588723439378913}
         (solve
          'x (ex (= (/ (- (* 2 x) 1) (+ x 1))
                    (+ (/ (* 2 x) (- x 1)) (/ 5 x))))))))