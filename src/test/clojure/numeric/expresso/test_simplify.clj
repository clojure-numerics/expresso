(ns numeric.expresso.test-simplify
  (:use numeric.expresso.simplify)
  (:use clojure.test)
  (:use numeric.expresso.rules)
  (:use numeric.expresso.construct)
  (:use numeric.expresso.protocols)
  (:use numeric.expresso.impl.pimplementation)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        clojure.test)
  (:require [numeric.expresso.construct :as c])
  (:require [clojure.core.matrix :as matrix])
  (:require [clojure.core.matrix.operators :as mop])
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.logic.unifier :as u]))


(def matr (matrix-symb 'a))

(deftest test-simp-shape-inference
  (is (symbol? (simp-expr (ex' (- matr matr)))))
  (is (= [[0.0 0.0]
          [0.0 0.0]] (value
                      (check-constraints
                       (add-constraint (simp-expr (ex' (- matr matr)))
                                       [== (shape matr) [2 2]]))))))