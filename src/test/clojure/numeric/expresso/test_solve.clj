(ns numeric.expresso.test-solve
  (:use numeric.expresso.solve)
  (:use clojure.test)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.logic.unifier :as u]))

(deftest test-simplifyo
  (is (= [0] (run* [q] (simplifyo '(* x (+ 0 (* 3 (* x 0)))) q)))))

(deftest test-solveo
  (is (= ['(= x 7/3)] (run* [q] (solveo '(= (- (* x 3) 3) 4) 'x q))))
  (is (= ['(= x 4) ] (run* [q] (solveo '(= (+ (* 3 (+ (* x 4) (* x 3))) 5) 89) 'x  q)))))
