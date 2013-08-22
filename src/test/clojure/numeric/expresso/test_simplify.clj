(ns numeric.expresso.test-simplify
  (:use numeric.expresso.simplify)
  (:use clojure.test)
  (:use numeric.expresso.rules)
  (:use numeric.expresso.construct)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        clojure.test)
  (:require [numeric.expresso.construct :as c])
  (:require [clojure.core.matrix :as matrix])
  (:require [clojure.core.matrix.operators :as mop])
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.logic.unifier :as u]))



(deftest test-matrix-simplification-rules
  (is (matrix/e== (matrix/broadcast 0 [2 2]) (apply-rules
                      matrix-simplification-rules
                      (ex (matrix/mul [[1 2][3 4]] [[0 0][0 0]])))))
  (is (matrix/e== (matrix/broadcast 0 [3 2]) (apply-rules
                      matrix-simplification-rules
                      (ex (matrix/mul [[1 2][3 4] [5 6]] [[0 0][0 0]]))))))
