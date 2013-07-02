(ns numeric.expresso.core
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [numeric.expresso.construct :only [with-expresso ex]]
        [numeric.expresso.rules :only [rule apply-rule transform-with-rules]]
        [clojure.test])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [clojure.core.logic.unifier :as u]
            [numeric.expresso.utils :as utils]
            [numeric.expresso.solve :as s]
            [numeric.expresso.construct :as c]))

(defn ** [a b]
  (Math/pow a b))

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



(defn minus-to-pluso [?a ?&+]
  (fn [res]
    (project [?a ?&+]
             (let [nargs [(first ?&+) (map (fn [a] (ex `* -1  a)) (second ?&+))]]
             (== res (ex `+ ?a nargs))))))

(defn multiply-outo [?&+a ?&+b ?&*]
  (fn [res]
    (project [?&+a ?&+b ?&*]
             (let [aargs (second ?&+a)
                   bargs (second ?&+b)]
               (== res (ex `+ [(first ?&+a) (map (fn [[a b]] (ex `* a b)) 
                                                 (for [a aargs b bargs] [a b]))]
                           ?&*))))))

(with-expresso [+ - * /]

  

(def expand-brackets)

(def concat-similar)


;; start example of using the rule based translator to simplify and transform
;; a polynomial input to standart form. start with variable 'x



(def normal-form-rules
  [(rule (+) :=> 0)
   (rule (*) :=> 1)
   (rule (+ 0 ?&*) :=> (+ ?&*))
   (rule (* 0 ?&*) :=> 0)
   (rule (- ?a ?&+) :=> (minus-to-pluso ?a ?&+))
   (rule (* (+ ?&+a) (+ ?&+b) ?&*) :=> (multiply-outo ?&+a ?&+b ?&*))
   ])

(apply-rule (last normal-form-rules) (* (+ 'a 'b) (+ 'c 'd)))

(transform-with-rules normal-form-rules (- 3 4 0 5))
)