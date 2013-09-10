(ns numeric.expresso.constructing-functions
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is log] :as l]
        [numeric.expresso.construct]
        [numeric.expresso.properties :as props]
        [numeric.expresso.protocols]
        [numeric.expresso.rules]
        [clojure.test])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [clojure.core.logic.unifier :as u]
            [numeric.expresso.utils :as utils]
            [numeric.expresso.solve :as s]
            [clojure.core.matrix :as matrix]
            [clojure.core.memoize :as memo]
            [clojure.core.matrix.operators :as mop]
            [numeric.expresso.impl.matcher :as m]
            [numeric.expresso.simplify :as simp]
            [numeric.expresso.construct :as c]))


(defmacro define-constructing-functions
  "defines expresso construction functions for the operators. The operators can
   not be namespace qualified. An operator can also be a 2-element vector
   instead of a symbol. In this case the function generated will have the name
   of the first element and will construction the operation specified in the
   second element (which can then be qualified). The symbols should not be
   quoted."
  [operators]
  `(do ~@(for [op operators]
           (do (prn "op " op)
               (if (vector? op)
                 `(defn ~(first op) [& ~'args]
                    (cev (quote ~(second op)) ~'args))
                 `(defn ~op [& ~'args]
                    (cev (quote ~op) ~'args)))))))

(define-constructing-functions [+ - * / mul div sub add
                                ** sqrq log sin cos log asin atan
                                acos emul inner-product scale mul
                                add-product add-scaled add-scaled-product
                                normalise normalise-probabilities dot
                                outer-product cross distance det
                                inverse negate trace length length-squared
                                pow log rank sum abs exp])
