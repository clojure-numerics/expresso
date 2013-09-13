(ns numeric.expresso.examples
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [numeric.expresso.construct]
        [numeric.expresso.properties :as props]
        [numeric.expresso.protocols]
        [numeric.expresso.simplify]
        [numeric.expresso.rules]
        [clojure.test])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [clojure.core.logic.unifier :as u]
            [numeric.expresso.utils :as utils]
            [clojure.core.matrix :as matrix]
            [clojure.core.matrix.operators :as mop]
            [numeric.expresso.impl.matcher :as m]
            [numeric.expresso.construct :as c]))
;;stub
;;very basic syntactical rules example to transform logic expressions to dnf

(def disjunctive-normal-form-rules
  (construct-with [not and or]
    [(rule (not (not ?x)) :=> ?x :syntactic)
     (rule (not (or ?a ?b)) :=> (and (not ?a) (not ?b)) :syntactic)
     (rule (not (and ?a ?b)) :=> (or (not ?a) (not ?b)) :syntactic)
     (rule (and ?a (or ?b ?c)) :=> (or (and ?a ?b) (and ?a ?c)) :syntactic)
     (rule (and (or ?a ?b) ?c) :=> (or (and ?a ?c) (and ?b ?c)) :syntactic)
     (rule (and (and ?a ?b) ?c) :=> (and ?a (and ?b ?c)) :syntactic)
     (rule (or (or ?a ?b) ?c) :=> (or ?a (or ?b ?c)) :syntactic)]))

(construct-with [and not or]
  (transform-with-rules disjunctive-normal-form-rules
    (or 'a (not (or 'b (and 'c (not 'd)))))))

