(ns numeric.expresso.test-construct
  (:use numeric.expresso.construct)
  (:use clojure.test)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [clojure.test])
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.logic.unifier :as u]))

(deftest test-unify
  (let [ex1 (ex (+ 1 X))]
    ;;(is (= [(ex X)] (run* [q] (fresh [op p] (== [op p q] ex1)))))
    (is (= [(ex X)] (run* [q] (fresh [op p] (== ex1 [op p q])))))
    (is (= [(ex (+ 1 X))] (run* [q] (== ex1 q))))
    
    ))

  