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
  (let [ex1 (ex (+ 1 X))]
    ;;(is (= [(ex X)] (run* [q] (fresh [op p] (== [op p q] ex1)))))
    (is (= [(ex X)] (run* [q] (fresh [op p] (== ex1 [op p q])))))
    (is (= [(ex (+ 1 X))] (run* [q] (== ex1 q))))
    
    ))

(deftest test-constant
  (is (constant? (ex 1)))
  (is (not (constant? (ex (+ 1 X))))))

(deftest test-without-symbol
  (is (without-symbol? 'X (ex Y)))
  (is (without-symbol? 'X (ex (+ 1 Y))))
  (is (not (without-symbol? 'X (ex X))))
  (is (not (without-symbol? 'X (ex (+ 1 X))))))

(deftest test-lifto
  (is (= [3] (run* [q] ((lifto inc) 2 q)))))

(deftest test-lifto-with-inverse
  (let [inco (lifto-with-inverse inc dec)]
    (is (= [3] (run* [q] (inco 2 q))))
    (is (= [2] (run* [q] (inco q 3))))))

(deftest test-resulto
  (is (= [2] (run* [q] (resulto (ex 2) q)))))

(deftest test-expresso
  (is (= [3] (run* [q] (expresso 'X (ex (= X 3)) q)))))
