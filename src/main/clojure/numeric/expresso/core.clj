(ns numeric.expresso.core
  (:refer-clojure :exclude [== * + / -])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [numeric.expresso.construct :only [with-expresso]]
        [numeric.expresso.rules :only [rule apply-rule transform-with-rules]]
        [clojure.test])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [clojure.core.logic.unifier :as u]
            [numeric.expresso.utils :as utils]
            [numeric.expresso.solve :as s]
            [numeric.expresso.construct :as c]))


(def disjunctive-normal-form-rules
  (with-expresso [not and or]
    [(rule (not (not ?x)) :=> ?x)
     (rule (not (or ?a ?b)) :=> (and (not ?a) (not ?b)))
     (rule (not (and ?a ?b)) :=> (or (not ?a) (not ?b)))
     (rule (and ?a (or ?b ?c)) :=> (or (and ?a ?b) (and ?a ?c)))
     (rule (and (or ?a ?b) ?c) :=> (or (and ?a ?c) (and ?b ?c)))
     (rule (and (and ?a ?b) ?c) :=> (and ?a (and ?b ?c)))
     (rule (or (or ?a ?b) ?c) :=> (or ?a (or ?b ?c)))]))


(with-expresso [and not or]
(transform-with-rules disjunctive-normal-form-rules
  (or 'a (not (or 'b (and 'c (not 'd)))))))