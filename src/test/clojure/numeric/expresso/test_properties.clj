(ns numeric.expresso.test-properties
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [numeric.expresso.properties]
        [clojure.core.logic :exclude [is] :as l]
        [clojure.test])
  (:require [numeric.expresso.protocols :as protocols]) 
  (:import [numeric.expresso.impl.pimplementation Expression])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [clojure.core.logic.unifier :as u]
            [clojure.core.matrix.operators :as mop]
            [clojure.core.matrix :as mat]
            [clojure.set :as set]
            [numeric.expresso.utils :as utils]
            [numeric.expresso.impl.matcher :as match]))

