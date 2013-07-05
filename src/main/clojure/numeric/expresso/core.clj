(ns numeric.expresso.core
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [numeric.expresso.construct :only [with-expresso ex expo]]
        [numeric.expresso.rules :only [rule apply-rule
                                       apply-rules transform-with-rules]]
        [clojure.test])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [clojure.core.logic.unifier :as u]
            [numeric.expresso.utils :as utils]
            [numeric.expresso.solve :as s]
            [numeric.expresso.construct :as c]))

(defn ^:dynamic ** [a b]
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

(with-expresso [+ - * / **]
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

(defn not-nullo [x]
  (project [x] (== true (!= x 0))))


(defn calc-reso [x]
  (fn [res]
    (project [x]
             (== (eval x) res))))

(defn no-symbol [x]
  (if (coll? x)
    (not (some #(and (symbol? %) (not (resolve %))) (flatten x)))))

(defn no-symbolso [x]
  (project [x]
           (== true (no-symbol x))))
 
(defn zip [& colls]
  (apply (partial map (fn [& a] a)) colls))

(defn contains-no-var? [x] (and (not (symbol? x)) (no-symbol x)))

(defn collabse-arguments-commutative [xs args]
  (let [gb (group-by contains-no-var? args)
        fix (concat (gb nil) (gb true))
        var (gb false)]
    (list* xs (eval (list* xs fix)) var)))

(defn collabse-arguments-associative [xs args]
  (let [parts (partition-by contains-no-var? args)
        eval-parts (fn [part]
                     (if (or (= nil (contains-no-var? part)) (contains-no-var? part))
                       [(eval (list* xs part))]
                       part))
        mc (mapcat eval-parts parts)]
    (list* xs mc)))

(defn compute-subexpression [expr]
  (if (coll? expr)
    (let [[xs & args] expr]
      (cond (isa? xs 'e/ca-op) (collabse-arguments-commutative xs args)
            (isa? xs 'e/ao-op) (collabse-arguments-associative xs args)
            :else expr))
    expr))
                                                        
(defn compute-subexpressiono [x]
  (fn [res]
    (project [x]
             (let [tmp (compute-subexpression x)]
               (if (= tmp res)
                 fail
                 (== res tmp))))))
           

(def simp-rules
  [(rule ?x :=> (calc-reso ?x) :if (no-symbolso ?x))
   (rule (+) :=> 0)
   (rule (*) :=> 1)
   (rule (+ ?x) :=> ?x)
   (rule (* ?x) :=> ?x)
   (rule (+ 0 ?&*) :=> (+ ?&*))
   (rule (+ ?x ?x ?&*) :=> (+ (* 2 ?x) ?&*))
   (rule (- ?x 0 ?&*) :=> (- ?x ?&*))
   (rule (- 0 ?x) :=> (- ?x))
  ; (rule (- ?x ?x) :=> 0)
   (rule (- ?x ?&*a ?x ?&*b) :=> (- 0 ?&*a ?&*b))
   (rule (- 0) :=> 0)
   (rule (* 1 ?&*) :=> (* ?&*))
   (rule (* 0 ?&*) :=> 0)
   (rule (* ?x ?x ?&*) :=> (* (** ?x 2) ?&*))
   (rule (/ ?x ?&* 0 ?&*a) :=> 'div-by-zero-error :if (not-nullo ?x))
   (rule (/ 0 ?&*) :=> 0)
   (rule (/ ?x 1 ?&*) :=> (/ ?x ?&*))
  ; (rule (/ ?x ?x) :=> 1)
   (rule (/ ?x ?&* ?x ?&*2) :=> (/ 1 ?&* ?&*2))
   (rule (** 0 0) :=> 'undefined)
   (rule (** ?x 0) :=> 1)
   (rule (** 0 ?x) :=> 0)
   (rule (** 1 ?x) :=> 1)
   (rule (** ?x 1 ) :=> ?x)
   (rule (** ?x -1) :=> (/ 1 ?x))
   (rule (* ?x (/ ?&+ ?x ?&*2) ?&*) :=> (* (/ ?&+ ?&*2) ?&*))
   (rule (/ (* ?x ?&*) ?x) :=> (* ?&*))
   (rule (/ ?x (* ?x ?&*)) :=> (* ?&*))
   (rule (+ ?x (- ?x) ?&*) :=> (+ ?&*))
   (rule ?x :=> (compute-subexpressiono ?x))

   ])

(transform-with-rules simp-rules (+ 2 2))

(transform-with-rules simp-rules (+ (* 5 20) 30 7))

(transform-with-rules simp-rules (- (* 5 'x) (* (+ 4 1) 'x)))

(transform-with-rules simp-rules (* (/ 'y 'z) (- (* 5 'x) (* (+ 4 1) 'x))))

(transform-with-rules simp-rules (* 3 2 'x))

(transform-with-rules simp-rules (* 2 'x 3 'y 4 'z 5 6))

(transform-with-rules simp-rules (+ 'x 3 4 (- 'x))))