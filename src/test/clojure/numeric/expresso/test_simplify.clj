(ns numeric.expresso.test-simplify
  (:use numeric.expresso.simplify)
  (:use clojure.test)
  (:use numeric.expresso.protocols)
  (:use numeric.expresso.impl.pimplementation)
  (:refer-clojure :exclude [==])
        [clojure.core.logic :exclude [is] :as l]


(def matr (matrix-symb 'a))

(deftest test-simp-shape-inference
  (is (symbol? (simp-expr (ex' (- matr matr)))))
  (is (= [[0.0 0.0]
          [0.0 0.0]] (value
                      (check-constraints
                       (add-constraint (simp-expr (ex' (- matr matr)))
                                       [== (shape matr) [2 2]]))))))