(ns numeric.expresso.examples
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
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
            [clojure.core.matrix.operators :as mop]
            [numeric.expresso.matcher :as m]
            [numeric.expresso.construct :as c]))

(def disjunctive-normal-form-rules
  (construct-with [not and or]
    [(rule (not (not ?x)) :=> ?x :syntactical)
     (rule (not (or ?a ?b)) :=> (and (not ?a) (not ?b)) :syntactical)
     (rule (not (and ?a ?b)) :=> (or (not ?a) (not ?b)) :syntactical)
     (rule (and ?a (or ?b ?c)) :=> (or (and ?a ?b) (and ?a ?c)) :syntactical)
     (rule (and (or ?a ?b) ?c) :=> (or (and ?a ?c) (and ?b ?c)) :syntactical)
     (rule (and (and ?a ?b) ?c) :=> (and ?a (and ?b ?c)) :syntactical)
     (rule (or (or ?a ?b) ?c) :=> (or ?a (or ?b ?c)) :syntactical)]))

(construct-with [and not or]
  (transform-with-rules disjunctive-normal-form-rules
    (or 'a (not (or 'b (and 'c (not 'd)))))))

(defn extract-zero [pargs expr]
  (== 0 expr))

(defmethod props/extractor-rel 'zero-mat? [_] extract-zero)



(def matr-rules
  [(rule (ex (mop/* ?&*1 (zero-matt?) ?&*2)) :=> (ex (mop/* ?&*1 ?&*2))
    ;  :if (guard (= 0 ?x))
         )])

