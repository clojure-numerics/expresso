(ns numeric.expresso.constructing-functions
  (:refer-clojure :exclude [== + - * /])
  (:use [numeric.expresso.construct]
        [clojure.test]))

 
(defmacro define-constructing-functions
  "defines expresso construction functions for the operators. The operators can
   not be namespace qualified. An operator can also be a 2-element vector
   instead of a symbol. In this case the function generated will have the name
   of the first element and will construction the operation specified in the
   second element (which can then be qualified). The symbols should not be
   quoted."
  [operators]
  `(do ~@(for [op operators]
           (if (vector? op)
             `(defn ~(first op) [& ~'args]
                (cev (quote ~(second op)) ~'args))
             `(defn ~op [& ~'args]
                (cev (quote ~op) ~'args))))))

(defn ^:dynamic ** [& args] (cev '** args))

(define-constructing-functions [+ - * / mul div sub add
                                sqrt log sin cos log asin atan
                                acos emul inner-product scale mul
                                add-product add-scaled add-scaled-product
                                normalise normalise-probabilities dot
                                outer-product cross distance det
                                inverse negate trace length length-squared
                                pow log rank sum abs exp is? cons? mzero?
                                midentity? as? shape?])
