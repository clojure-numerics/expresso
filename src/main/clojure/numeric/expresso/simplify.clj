(ns numeric.expresso.simplify
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
            [clojure.set :as set]
            [numeric.expresso.symbolic :as symb]
            [clojure.core.matrix :as matrix]
            [clojure.core.matrix.operators :as mop]
            [numeric.expresso.matcher :as m]
            [numeric.expresso.construct :as c]))


(defn calc-reso [x]
  (fn [res]
    (project [x]
             (== (evaluate x nil) res))))

(defn no-symbolso [x]
  (project [x]
           (fresh []
                  (== true (no-symbol x)))))
 
(defn zip [& colls]
  (apply (partial map (fn [& a] a)) colls))

(defn contains-no-var? [x]
  (let [res (if (and (not (symbol? x)) (no-symbol x)) true false)]
    res))

(defn collabse-arguments-commutative [xs args]
  (let [gb (group-by contains-no-var? args)
        fix (concat (gb nil) (gb true))
        var (gb false)]
    (if (or (empty? fix) (< (count fix) 2))
            (list* xs args)
            (list* xs (eval (list* xs fix)) var))))

(defn collabse-arguments-associative [xs args]
  (let [parts (partition-by contains-no-var? args)
        eval-parts (fn [part]
                     (if (and (and (coll? part) (> (count part) 1))
                              (or (= nil (contains-no-var? part)) (contains-no-var? part)))
                       [(eval (list* xs part))]
                       part))
        mc (mapcat eval-parts parts)]
    (list* xs mc)))

(defn compute-subexpression [expr]
  (if (coll? expr)
    (let [[xs & args] expr]
      (cond #_(isa? xs 'e/ca-op)
            (contains? (:properties (meta xs)) :commutative)
            (collabse-arguments-commutative xs args)
            (contains? (:properties (meta xs)) :associative)
            (collabse-arguments-associative xs args)
            (isa? xs 'e/ao-op) (collabse-arguments-associative xs args)
            :else expr))
    expr))
                                                        
(defn compute-subexpressiono [x]
  (fn [res]
    (project [x]
             (let [tmp (compute-subexpression x)]
               (if (= tmp x)
                 fail
                 (== res tmp))))))


(defn symbolo [x] (project [x] (== true (symbol? x))))



(construct-with [+ - * / ** diff ln sin cos]

(def universal-rules
  [(rule (+) :=> 0)
   (rule (*) :=> 1)
   (rule (+ ?x) :=> ?x)
   (rule (* ?x) :=> ?x)
   (rule (+ 0 ?&*) :=> (+ ?&*))
   (rule (* 0 ?&*) :=> 0)
   (rule (* 1 ?&*) :=> (* ?&*))
   (rule (** ?x 1) :=> ?x)
   (rule (** ?x 0) :=> 1
         :if (guard (not= ?x 0)))
   (rule (** (** ?x ?n1) ?n2) :=> (** ?x (* ?n1 ?n2)))
   (rule (* (* ?&*) ?&*r) :=> (* ?&* ?&*r))
   (rule (+ (+ ?&*) ?&*r) :=> (+ ?&* ?&*r))
   (rule (- 0 ?x) :=> (- ?x))
   (rule (- ?x 0) :=> ?x)
   (rule (+ (* ?x ?y) (* ?z ?y) ?&*) :=> (+ (* (+ ?x ?z) ?y) ?&*)
         :if (guard (and (number? ?x) (number? ?z))))
   ])

(def eval-rules
  [(rule ?x :=> (calc-reso ?x) :if (no-symbolso ?x))
   (rule ?x :=> (compute-subexpressiono ?x))])
  
(def normal-form-rules
  (concat universal-rules
   [(rule (* ?x ?x ?&*) :=> (* (** ?x 2) ?&*))
   (rule (* ?x (/ ?x) ?&*) :=> (* ?&*))
   (rule (+ (* ?x ?n1) (* ?x ?n2) ?&*) :==>
         (+ (* ?x (clojure.core/+ ?n1 ?n2)) ?&*) :if
         (guard (and (number? ?n1) (number? ?n2))))
   (rule (- ?x ?&+) :=> (trans (+ ?x (map-sm #(- %) ?&+))))
   (rule (/ ?x ?&+) :=> (trans (* ?x (map-sm #(/ %) ?&+))))
   (rule (* (+ ?&+1) (+ ?&+2) ?&*) :==>
         (let [args1 (matcher-args ?&+1)
               args2 (matcher-args ?&+2)]
           (* ?&* (+ (seq-matcher (for [a args1 b args2] (* a b)))))))
   (rule (* (+ ?&+) ?x ?&*) :==>
         (* (+ (seq-matcher (for [a (matcher-args ?&+)] (* a ?x)))) ?&*))]))

(def simplify-rules
  [(rule (* ?x ?x ?&*) :=> (* (** ?x 2) ?&*))
   (rule (* ?x (/ ?x) ?&*) :=> (* ?&*))
   (rule (+ ?x (- ?x) ?&*) :=> (+ ?&*))
   (rule (+ ?x ?x ?&*) :=> (+ (* 2 ?x) ?&*))
   (rule (+ (* ?x ?&*) (- ?x) ?&*2) :=> (+ (* ?x (- ?&* 1)) ?&*2))
   (rule (+ (* ?x ?&*) (* ?x ?&*2) ?&*3) :=> (+ (* ?x (+ ?&* ?&*2)) ?&*3))
   (rule (+ (* ?x ?&*) ?x ?&*2) :=> (+ (* ?x (+ ?&* 1)) ?&*2))
   (rule (- (- ?x)) :=> ?x)
   (rule (* -1 (- ?x) ?&*) :=> (* ?x ?&*))
   (rule (* ?x (** ?x ?n) ?&*) :=> (* (** ?x (+ ?n 1)) ?&*))
   #_(rule (** (** ?x ?n) ?n2) :=> (** ?x (* ?n ?n2)))])

(def to-inverses-rules
  [(rule (- ?x ?&+) :=> (trans (+ ?x (map-sm #(- %) ?&+))))
   (rule (- (+ ?&+)) :==> (+ (map-sm #(- %) ?&+)))
   (rule (- (* ?&+)) :=> (* -1 ?&+))
   (rule (/ ?x ?&+) :=> (trans (* ?x (map-sm #(/ %) ?&+))))])
(declare multinomial)
(def multiply-out-rules
  [(rule (* (+ ?&+1) (+ ?&+2) ?&*) :==>
         (let [args1 (matcher-args ?&+1)
               args2 (matcher-args ?&+2)]
           (* ?&* (+ (seq-matcher (for [a args1 b args2] (* a b)))))))
   (rule (* (+ ?&+) ?x ?&*) :==>
         (* (+ (seq-matcher (for [a (matcher-args ?&+)] (* a ?x)))) ?&*))
   (rule (** (* ?&+) ?n) :==> (* (map-sm #(** % ?n) ?&+))
         :if (guard (integer? ?n)))
   (rule (** (** ?x ?n1) ?n2) :==> (** ?x (clojure.core/* ?n1 ?n2))
         :if (guard (integer? ?n)))
   (rule (** (+ ?&+) ?n) :==> (multinomial ?n (matcher-args ?&+))
         :if (guard (integer? ?n)))
   (rule (* ?x (/ ?x) ?&*) :=> (* ?&*)
         :if (guard (not= 0 ?x)))]
)
(def diff-rules
  [(rule (diff ?x ?x) :=> 1)
   (rule (diff (+ ?&+) ?x) :==> (+ (map-sm #(diff % ?x) ?&+)))
   (rule (diff (* ?&+) ?x) :==>
         (+ (seq-matcher
             (for [i (range (count-sm ?&+)) :let [[bv ith af] (split-in-pos-sm ?&+ i)]]
               (* (diff ith ?x) bv af)))))
   (rule (diff (- ?a) ?x) :=> (- (diff ?a ?x)))
   (rule (diff (/ ?a) ?x) :=> (- (* (diff ?a ?x) (/ (** ?a 2)))))
   (rule (diff (** ?a ?n) ?x) :==> (* ?n (** ?a (clojure.core/- ?n 1)) (diff ?a ?x))
         :if (guard (number? ?n)))
   (rule (diff (ln ?a) ?x) :=> (* (diff ?a ?x) (/ ?a)))
   (rule (diff (sin ?a) ?x) :=> (* (cos ?a) (diff ?a ?x)))
   (rule (diff (cos ?a) ?x) :=> (* (- (sin ?a)) (diff ?a ?x)))
   (rule (diff (** 'e ?n) ?x) :=> (* (** 'e ?n) (diff ?n ?x)))
   (rule (diff ?u ?x) :=> 0)])
)
(defn- binom [n k]
  (let [rprod (fn [a b] (reduce * (range a (inc b))))]
    (/ (rprod (- n k -1) n) (rprod 1 k))))

(defn factorial [n]
  (loop [n (long n) acc (long 1)]
    (if (<= n 1)
      acc
      (recur (- n 1) (* acc n)))))

(defn- multinomial-indices [m n]
  (if (= n 0)
    (list (repeat m 0))
    (if (= m 1)
      (list (list n))
      (for [i (range (inc n))
            j (multinomial-indices (- m 1) (- n i)) ]
        (list* i j)))))

(defn multinomial-coeff [n indices]
  (quot (factorial n) (reduce * (map factorial indices))))

(defn to-factors [args index]
  (loop [i 0 index index ret []]
    (if (= i (count args))
      ret
      (recur (inc i) (rest index)
             (cond
              (= (first index) 0) ret
              (= (first index) 1) (conj ret (nth args i))
               :else (conj ret (ex' (** ~(nth args i) ~(first index)))))))))

(defn multinomial [n args]
  (let [args (vec args)
        m (count args)
        indices (multinomial-indices m n)]
    (ce `+ (seq-matcher (for [index indices]
                          (let [factors (seq-matcher (to-factors args index))
                                coeff (multinomial-coeff n index)]
                            (if (= 1 coeff)
                              factors
                              (ex' (* coeff factors)))))))))

(defn simp-expr [expr]
  (->> expr 
       (transform-expression
        (concat eval-rules universal-rules to-inverses-rules
                multiply-out-rules ))
       (transform-expression (concat universal-rules
                                     eval-rules simplify-rules))))




(defn infer-shape-zero-mat [sf x sl]
  (let [series (concat (matcher-args sf) [x] (matcher-args sl))]
    (if (= (count series) 1)
      x
      (let [s (filter identity [(first (shape (first series)))
                                       (last (shape (last series)))])]
        (if (some symbol? series)
          (zero-matrix s)
          (matrix/broadcast 0 s))))))

(defn identity-right-shape [a]
  (let [s (shape a)]
    (cond
     (empty? s) 1
     (symbol? a) (identity-matrix (first s))
     :else (matrix/identity-matrix (first s)))))

(def matrix-simplification-rules
  [(rule (ex (matrix/add (mzero? ?x) ?&*)) :=> (ex (matrix/add ?&*)))
   (rule (ex (matrix/sub ?x ?x)) :==> (let [s (shape ?x)]
                                        (if (symbol? ?x)
                                          (zero-matrix s)
                                          (matrix/broadcast 0 s))))
   (rule (ex (matrix/mul ?&*1 (mzero? ?x) ?&*2))
         :==> (infer-shape-zero-mat ?&*1 ?x ?&*2))
   (rule (ex (matrix/mul ?&*1 (midentity? ?x) ?&*2))
         :=> (ex (matrix/mul ?&*1 ?&*2)))
   (rule (ex (matrix/div ?a ?a)) :==> (identity-right-shape ?a))
   (rule (ex (matrix/mul ?a (matrix/div ?a) ?&*)) :=> (ex (matrix/mul ?&*)))])

(defn simplify-matrix-expression [expr]
  (transform-expression matrix-simplification-rules expr))


(construct-with [+ * -]
                (def diff-simp-rules
                  (concat eval-rules
                          [(rule (+) :=> 0)
                           (rule (*) :=> 1)
                           (rule (+ ?x) :=> ?x)
                           (rule (* ?x) :=> ?x)
                           (rule (+ 0 ?&*) :=> (+ ?&*))
                           (rule (* 0 ?&*) :=> 0)
                           (rule (* 1 ?&*) :=> (* ?&*))
                           (rule (- 0) :=> 0)
                           (rule (+ ?x (- ?x) ?&*) :=> (+ ?&*))
                           (rule (* (* ?&*) ?&*r) :=> (* ?&* ?&*r))
                           (rule (+ (+ ?&*) ?&*r) :=> (+ ?&* ?&*r))]
                          simplify-rules)))


(defmethod diff-function '+ [[expr v]]
  (let [args (expr-args expr)]
    (cev '+ (map #(differentiate-expr % v) args))))

(defmethod diff-function '* [[expr v]]
  (let [args (vec (expr-args expr))
        c (count args)]
    (cev '+ (loop [i 0 exprs []]
                   (if (< i c)
                     (recur (inc i)
                            (conj exprs
                                  (cev '* (concat (subvec args 0 i)
                                                       [(differentiate-expr
                                                         (nth args i) v)]
                                                       (subvec args (inc i))))
                                       ))
                      exprs)))
         ))


(defmethod diff-function '- [[expr v]]
  (let [args (vec (expr-args expr))]
    (if (= 1 (count args))
      (ce '- (differentiate-expr (first args) v))
      (differentiate-expr
       (cev '+ (concat [(first args)] (map #(ce '- %) (rest args)))) v))))

(defmethod diff-function '/ [[expr v]]
  (let [args (vec (expr-args expr))]
    (if (= 1 (count args))
      (differentiate-expr (ce '** (first args) -1) v)
      (differentiate-expr
       (cev '* (concat [(first args)] (map #(ce '/ %) (rest args)))) v))))

(defmethod diff-function '** [[expr v]]
  (let [args (vec (expr-args expr))]
    (if (= (count args) 2)
      (if (= (nth args 0) v)
        (ce '* (nth args 1) (ce '** (nth args 0)
                                     (apply-rules eval-rules
                                                  (ce '- (nth args 1) 1)))
                 (differentiate-expr (nth args 0) v))
        (differentiate-expr
         (ce 'exp (ce '* (nth args 1) (ce 'log (nth args 0)))) v))
      (differentiate-expr
       (cev '** (concat [(ce '** (nth args 0) (nth args 1))] (subvec args 2)))
       v))))

(defmethod diff-function 'log [[expr v]]
  (ce '* (ce '/ (second expr)) (differentiate-expr (second expr) v)))

(defmethod diff-function 'sin [[expr v]]
  (ce '* (ce 'cos (second expr)) (differentiate-expr (second expr) v)))

(defmethod diff-function 'cos [[expr v]]
  (ce '* (ce '- (ce 'sin (second expr))) (differentiate-expr (second expr) v)))

(defmethod diff-function 'exp [[expr v]]
  (ce '* (cev 'exp (rest expr)) (differentiate-expr (second expr) v)))


(defn differentiate [v expr]
  (->> expr
       (#(differentiate-expr % v))
       (transform-expression (concat eval-rules universal-rules
                                     simplify-rules))))