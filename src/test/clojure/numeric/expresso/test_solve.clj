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
  (is (= '[3 _1 _0]
         (solve-linear-system [(ex (= x 3))
                               (ex (= y y))
                               (ex (= z z))]
                              '[x y z])))
  (is (= '()
         (solve-linear-system [(ex (= x (+ x 1)))] '[x])))
  (is (= '_0
         (second (solve-linear-system [(ex (= x y))] '[x y])))))

(deftest test-solve-system
  (is (= {'y [3 6 9]}
         (solve-system '[y]
                       #{(ex (= z (mop/* 2 x)))
                         (ex (= y (mop/+ x z)))
                         (ex (== x [1 2 3]))})))
  (is (= {'y [3 6 9]
          'z [2 4 6]
          'x [1 2 3]}
         (solve-system '[y z x]
                       #{(ex (= z (mop/* 2 x)))
                         (ex (= y (mop/+ x z)))
                         (ex (== x [1 2 3]))})))
  (is (= {'x 2} (solve-system '[x] #{(ex (= (+ x y) 3))
				     (ex (= y 1))})))
  (is (= {'x 1} (solve-system '[x] #{(ex (= (+ x y) 3))
                                     (ex (= (+ x 1) y))}))))