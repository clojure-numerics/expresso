(ns numeric.expresso.test-various
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [numeric.expresso.construct]
        [numeric.expresso.properties :as props]
        [numeric.expresso.protocols]
        [numeric.expresso.impl.pimplementation]
        [numeric.expresso.rules]
        [numeric.expresso.simplify]
        [clojure.test])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [clojure.core.logic.unifier :as u]
            [numeric.expresso.utils :as utils]
            [clojure.core.matrix :as matrix]
            [clojure.core.matrix.operators :as mop]
            [numeric.expresso.impl.matcher :as m]
            [numeric.expresso.construct :as c]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;,,

(defn expression? [exp]
  (or (not (sequential? exp)) (and (sequential? exp) (symbol? (first exp)))))


(construct-with [+ - * / **]
  (def transform-to-polynomial-normal-form-rules
    (concat universal-rules
            [(rule (+ [?x ?y] [?z ?y] ?&*)
                   :==> (+ [(+ ?x ?z) ?y] ?&*)
                   :if (guard (and  (number? ?y))))
             (rule (* [?x ?y] [?z ?a] ?&*)
                   :==>  (* [(* ?x ?z) (clojure.core/+ ?y ?a)] ?&*)
                   :if (guard (and (number? ?y)
                                    (number? ?a))))
             (rule (- [?x ?y]) :==> [(- ?x) ?y]
                   :if (guard (and (number? ?y))))
             (rule (/ [?x ?y]) :==>[(/ ?x) ?y]
                   :if (guard (and  (number? ?y))))
             (rule (ce ?op [?x 0]) :=> [(ce ?op ?x) 0])])))

(defn- transform-to-coefficients-form [v expr]
  (if (sequential? expr)
    (if (= (first expr) '**)
      [1 (second (rest  expr))]
      (apply (partial ce (first expr)) (map (partial transform-to-coefficients-form v) (rest expr))))
    (if (= v expr) [1 1] [expr 0])))


(defn translate-back [v expr]
  (conj
         (walk/postwalk #(if (and (sequential? %) (= (count %) 2) (expression? (first %)) (number? (second %)))
                           (if (= 0 (second %)) (first %)
                               (ex' (* ~(first %) (** v ~(second %)))))
                           %) (sort #(> (second %1) (second %2)) (rest expr))) (first expr)))



(defn dbg
  ([x] (prn x) x)
  ([m x] (prn m x) x))


(defn to-polynomial-normal-form [v expr]
  (->> expr
       (transform-expression (concat eval-rules
                                     universal-rules
                                     to-inverses-rules
                                     multiply-out-rules))
       (transform-to-coefficients-form v)
       (transform-expression transform-to-polynomial-normal-form-rules)
       (#(ce `+ %))
       (apply-rules [(rule (ex (+ (+ ?&*) ?&*r)) :=> (ex (+ ?&* ?&*r)))])
       (translate-back v)
       (transform-expression (concat eval-rules
                                     universal-rules
                                     to-inverses-rules
                                     multiply-out-rules))))

(def c= =)

(construct-with [+ cons? nth-arg? = - / * mop/+ mop/- mop/* matrix/div]
(def rearrange-rules
  [(rule [(cons? ?p ?ps) (= (+ ?&+) ?rhs)]
         :==> (let [[left x right] (split-in-pos-sm ?&+ ?p)]
                [?ps (= x (- ?rhs left right))]))
   (rule [(cons? ?p ?ps) (= (mop/+ ?&+) ?rhs)]
         :==> (let [[left x right] (split-in-pos-sm ?&+ ?p)]
                [?ps (= x (mop/- ?rhs left right))]))
   (rule [(cons? ?p ?ps) (= (* ?&+) ?rhs)]
         :==> (let [[left x right] (split-in-pos-sm ?&+ ?p)]
                [?ps (= x (/ ?rhs (* left right)))]))
   (rule [(cons? ?p ?ps) (= (mop/* ?&+) ?rhs)]
         :==> (let [[left x right] (split-in-pos-sm ?&+ ?p)]
                [?ps (= x (matrix/div ?rhs (mop/* left right)))]))
   (rule [(cons? ?p ?ps) (= (- ?&+) ?rhs)]
         :==> (if (c= (count-sm ?&+) 1)
                [?ps (= ?&+ (- ?rhs))]
                (let [[left x right] (split-in-pos-sm ?&+ ?p)]
                  [?ps (= x (if (c= ?p 0)
                              (+ ?rhs right)
                              #_(- left right ?rhs)
                              (+ (- ?rhs (first-sm left)) (rest-sm left)
                                 right)))])))
   (rule [(cons? ?p ?ps) (= (mop/- ?&+) ?rhs)]
         :==> (let [[left x right] (split-in-pos-sm ?&+ ?p)]
                [?ps (= x (if (c= ?p 0)
                            (mop/+ ?rhs right)
                            (mop/- left right ?rhs)))]))
   (rule [(cons? ?p ?ps) (= (/ ?&+) ?rhs)]
         :==> (let [[left x right] (split-in-pos-sm ?&+ ?p)]
                [?ps (= x (if (c= ?p 0)
                            (* ?rhs right)
                            (/ left right ?rhs)))]))]))


(deftest test-transform-to-polynomial-normal-form
  (is (= (ex (** x 3))
         (to-polynomial-normal-form 'x (ex (+ (** x 3) (* 3 (** x 2))
                                              (- (* 2 (** x 2))
                                                 (* 5 (** x 2))))) )))
  (is (= (ex (+ (* 243.0 (** x 10)) (* 1215.0 (** x 9)) (* 4050.0 (** x 8)) (* 8910.0 (** x 7)) (* 15255.0 (** x 6)) (* 19683.0 (** x 5)) (* 20340.0 (** x 4)) (* 15840.0 (** x 3)) (* 9600.0 (** x 2)) (* 3840.0 x) 1024.0))
         (to-polynomial-normal-form 'x (ex (** (+ (* 3 x) 4 (* 3 (** x 2))) 5))))))

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
