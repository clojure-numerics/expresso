(ns numeric.expresso.test-parse
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [numeric.expresso.properties]
        [numeric.expresso.rules]
        [numeric.expresso.parse]
        [numeric.expresso.construct]
        [clojure.test])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [instaparse.core :as insta]
            [clojure.core.logic.unifier :as u]
            [numeric.expresso.utils :as utils]))

(deftest test-parse-expression
  (= (ex (+ 1 2)) (parse-expression "1+2"))
  (= (ex (+ 1 2 3 4)) (parse-expression "1+2+3+4"))
  (= (ex (+ (* 1 2 3) 4)) (parse-expression "1*2*3+4"))
  (= (ex (* 1 2 (+ 3 4))) (parse-expression "1*2*(3+4)")))