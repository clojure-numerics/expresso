(ns numeric.expresso.test-rules
  (:use numeric.expresso.rules)
  (:use clojure.test)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.logic.unifier :as u]))


(deftest test-apply-ruleo
  (is (= ['x] (run* [q] (apply-ruleo (rule ['+ 0 x] :=> x) '(+ 0 x) q))))
  (is (= [0] (run* [q] (apply-ruleo (rule ['* x 0] :=> 0) '(* x 0) q))))
  (is (= ['(+ 0 (+ 0 x))] (run* [q] (apply-ruleo (rule ['+ 0 x] :=> x) q '(+ 0 x)))))
;  (is (= [7] (run* [q] (apply-ruleo calculo '(+ 1 (* 2 3)) q)))))
)