(ns numeric.expresso.types
  (:refer-clojure :exclude [== long double])
  (:use [clojure.test]
        [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is]])
  (:require 
   [clojure.set :as set]
   [clojure.core.matrix :as mat]
   [clojure.walk :as walk]))

(def matrix ::matrix)
(def number ::number)
(def integer ::integer)
(def long ::long)
(def double ::double)



(derive integer number)
(derive long number)
(derive double number)