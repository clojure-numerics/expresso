(ns numeric.expresso.test-construct
  (:use numeric.expresso.construct)
  (:use clojure.test)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [clojure.test])
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.logic.unifier :as u]))

(deftest test-plus
  (is (= 4 (plus 1 3))))

(deftest test-expo 
  (is (= [1] (run* [q] (expo '+ [q 2]  (ex (+ 1 2))))))
  (is (= [] (run* [q] (expo '- [q 2]  (ex (+ 1 2))))))
  (is (= [[1 2]] (run* [q] (fresh [ex op lhs rhs]
                                  (expo '+ [1 2] ex)
                                  (expo op [lhs rhs] ex)
                                  (== q [lhs rhs]))))))



(deftest test-unify
  (let [ex1 (ex (+ 1 X))]
    ;;(is (= [(ex X)] (run* [q] (fresh [op p] (== [op p q] ex1)))))
    (is (= [(ex X)] (run* [q] (fresh [op p] (== ex1 [op p q])))))
    (is (= [(ex (+ 1 X))] (run* [q] (== ex1 q))))
    
    ))