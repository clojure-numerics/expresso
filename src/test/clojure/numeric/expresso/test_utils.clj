(ns numeric.expresso.test-utils
  (:use numeric.expresso.utils)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [is] :as l]
        [clojure.test]))


(deftest test-expo 
  (is (= [[1 2]] (run* [q] (fresh [ex op lhs rhs]
                                  (expo '+ [1 2] ex)
                                  (expo op [lhs rhs] ex)
                                  (== q [lhs rhs]))))))


(deftest test-lifto-with-inverse
  (let [inco (lifto-with-inverse inc dec)]
    (is (= [3] (run* [q] (inco 2 q))))
    (is (= [2] (run* [q] (inco q 3))))))


(deftest test-mapo 
  (is (= [2] (run* [q] (mapo (lifto-with-inverse inc dec) [1 q 3] [2 3 4])))))

(deftest test-resolve-opo
  (is (= [clojure.core/+] (run* [q] (resolve-opo '+ q)))))

(deftest test-applyo 
  (is (= [[1 2 3 4]] (run* [q] (applyo conso [1 [2 3 4]] q))))
  (is (= [3] (run* [q] (applyo conso [1 [2 q 4]] [1 2 3 4])))))