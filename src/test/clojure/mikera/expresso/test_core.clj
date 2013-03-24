(ns mikera.expresso.test-core
  (:use mikera.expresso.core)
  (:use clojure.test)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.logic.unifier :as u]))

(deftest test-unify
  (let [ex1 (ex [+ 1 X])]
    ;;(is (= [(ex X)] (run* [q] (fresh [a b] (== [a b q] ex1)))))
    (is (= [(ex X)] (run* [q] (fresh [a b] (== ex1 [a b q])))))
    
    ))

(deftest test-constant
  (is (constant? (ex 1)))
  (is (not (constant? (ex (+ 1 X))))))

(deftest test-lifto
  (is (= [3] (run* [q] ((lifto inc) 2 q)))))

(deftest test-resulto
  (is (= [2] (run* [q] (resulto (ex 2) q)))))
