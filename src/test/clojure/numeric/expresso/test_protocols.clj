(ns numeric.expresso.test-protocols
  (:require [numeric.expresso.protocols :as p])
  (:use clojure.test)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [numeric.expresso.rules]
        [numeric.expresso.construct]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.logic.unifier :as u]))

(deftest text-unification
  (= [1] (run* [q] (== (p/Expression. `+ [q 2 3]) (p/Expression. `+ [1 2 3]))))
  (= ['_0] (run* [q] (== (p/Expression. `+ [q 2 3]) (p/Expression. `+ [q 2 3]))))
  (= [] (run* [q] (== (p/Expression. `+ [q 1 3]) (p/Expression. `+ [q 2 3]))))
  (= [3] (run* [q] (== (AtomicExpression. q) 3))))