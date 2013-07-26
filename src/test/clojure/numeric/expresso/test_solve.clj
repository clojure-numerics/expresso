(ns numeric.expresso.test-solve
  (:use numeric.expresso.solve)
  (:use clojure.test)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        clojure.test)
  (:require [numeric.expresso.construct :as c])
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.logic.unifier :as u]))
