(ns numeric.expresso.test-polynomial
  (:use numeric.expresso.polynomial)
  (:use clojure.test)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [clojure.test])
  (:require [clojure.core.logic.fd :as fd])
  (:require [numeric.expresso.protocols :as protocols])
  (:require [clojure.core.logic.unifier :as u]))


(deftest test-to-poly-normal-form
  (is (= 7 (to-poly-normal-form '(+ 3 x 4 (- x)))))
  (is (= (poly 'x (poly 'y 0 2) 2) (to-poly-normal-form '(+ x y y x)))))