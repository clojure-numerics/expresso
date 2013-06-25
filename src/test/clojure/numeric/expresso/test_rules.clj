(ns numeric.expresso.test-rules
  (:use numeric.expresso.rules)
  (:use clojure.test)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd])
  (:require [numeric.expresso.construct :as c])
  (:require [clojure.core.logic.unifier :as u]))




(c/with-expresso [* + - e/ca+ e/ca* e/- e/div]
(def rules [(rule (* ?x 1) :=> ?x)
            (rule (* ?x 0) :=> 0)
            (rule (+ ?x 0) :=> ?x)
            (rule (+ ?x (- ?x)) :=> 0)
            (rule (- ?x ?x) :=> (- (* 2 ?x)))])


(deftest test-apply-ruleo
  (is (= '(3) (run* [q] (apply-ruleo (first rules) (* 3 1) q))))
  (is (= '() (run* [q] (apply-ruleo (first rules) (+ 3 1) q))))
  (is (= '(0) (run* [q] (apply-ruleo (nth rules 3) (+ 2 (- 2)) q))))
  (is (=  '((clojure.core/- (clojure.core/* 2 1)))
          (run* [q] (apply-ruleo (last rules) (- 1 1) q)))))
)

(defn collabs-factorso [x a b]
  (fn [res]
    (project [a b]
             (== res (c/ex 'e/ca* x (+ a b))))))

  
(defna numberso [vars] 
  ([[n . rest]] (project [n] (do (== true (number? n))) (numberso rest)))
  ([[]] succeed))

(c/with-expresso [* + - e/ca+ e/ca* e/- e/div]

(def simplification-rules
  [(rule (e/ca+ 0 ?&*) :=> ?&*)
   (rule (e/ca* 0 ?&*) :=> 0)
   (rule (e/ca* 1 ?&x) :=> ?&x)
   (rule (e/- 0 ?x) :=> (e/- ?x))
   (rule (e/- ?x 0) :=> ?x)
   (rule (e/ca* ?x (e/div 1 ?x) ?&*) :=> (e/ca* ?&*) :if (!= ?x 0))
   (rule (e/ca+ ?x (e/- ?x) ?&*) :=> 0)
   (rule (e/ca+ (e/ca* ?a ?x) (e/ca* ?b ?x)) :=> (collabs-factorso ?x ?a ?b)
         :if (numberso [?a ?b]))
   (rule (e/ca* ?x (e/ca+ ?a ?b)) :=> (e/ca+ (e/ca* ?x ?a) (e/ca* ?x ?b)))])

(deftest test-transform-with-rules
  (is (= '(clojure.core/* 3 3)
         (transform-with-rules simplification-rules 
           (* 3 (+ (+ 0 3) (* 0 3)))))))

(def rr (rule (+ (* ?x ?&*a) (* ?x ?&*b) ?&*r) :=>
              (+ (* ?x (+ (* ?&*a) (* ?&*b))) ?&*r)))

(deftest test-seq-matching-commutative-rule
  (is (= '(clojure.core/+ (clojure.core/* x (clojure.core/+ (clojure.core/* 3 2) (clojure.core/* 4 3))) 1)
          (apply-rule rr (+ (* 'x 3 2) (* 'x 4 3) 1))))))