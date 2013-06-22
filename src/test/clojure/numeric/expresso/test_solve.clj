(ns numeric.expresso.test-solve
  (:use numeric.expresso.solve)
  (:use clojure.test)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        clojure.test)
  (:require [numeric.expresso.construct :as c])
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.logic.unifier :as u]))

(deftest test-lifto
  (is (= [3] (run* [q] ((lifto inc) 2 q)))))


(deftest test-resulto
  (is (= [6] (run* [q] (resulto (c/ex `+ 2 4) q)))))


(deftest test-simplifyo
  (is (= [0] (run 1 [q] (simplifyo '(* x (+ 0 (* 3 (* x 0)))) q)))))


#_(deftest test-solveo
  (is (= ['(= x 7/3)] (run 1 [q] (solveo '(= (- (* x 3) 3) 4) 'x q))))
  (is (= ['(= x 4) ] (run 1 [q] (solveo '(= (+ (* 3 (+ (* x 4) (* x 3))) 5) 89) 'x  q)))))

