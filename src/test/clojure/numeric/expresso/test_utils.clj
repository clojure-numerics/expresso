(ns numeric.expresso.test-utils
  (:use numeric.expresso.utils)
  (:use clojure.test)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        clojure.test)
;  (:require [numeric.expresso.construct :as c])
  (:require [clojure.core.logic.fd :as fd]
            [numeric.expresso.construct :as c]
            [numeric.expresso.solve :as s])
  (:require [clojure.core.logic.unifier :as u]))


(deftest test-constant
  (is (= 10 (c/ex 10)))
  (is (constant? (c/ex 1)))
  (is (not (constant? (c/ex (+ 1 X))))))

(deftest test-without-symbol
  (is (without-symbol? 'X (c/ex Y)))
  (is (without-symbol? 'X (c/ex (+ 1 Y))))
  (is (not (without-symbol? 'X (c/ex X))))
  (is (not (without-symbol? 'X (c/ex (+ 1 X))))))


(deftest test-lifto-with-inverse
  (let [inco (lifto-with-inverse inc dec)]
    (is (= [3] (run* [q] (inco 2 q))))
    (is (= [2] (run* [q] (inco q 3))))))

(deftest test-mapo 
  (is (= [[2 3 4]] (run* [q] (mapo (s/lifto inc) [1 2 3] q))))
  (is (= [2] (run* [q] (mapo (lifto-with-inverse inc dec) [1 q 3] [2 3 4])))))

(deftest test-resolve-opo
  (is (= [clojure.core/+] (run* [q] (resolve-opo '+ q)))))

(deftest test-applyo 
  (is (= [[1 2 3 4]] (run* [q] (applyo conso [1 [2 3 4]] q))))
  (is (= [3] (run* [q] (applyo conso [1 [2 q 4]] [1 2 3 4])))))