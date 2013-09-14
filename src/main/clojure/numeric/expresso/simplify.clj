(ns numeric.expresso.simplify
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [log] :as l]
        [numeric.expresso.construct]
        [numeric.expresso.impl.polynomial]
        [numeric.expresso.properties :as props]
        [numeric.expresso.protocols]
        [numeric.expresso.impl.pimplementation]
        [numeric.expresso.rules])
  (:require [clojure.walk :as walk]
            [numeric.expresso.utils :as utils]
            [clojure.set :as set]
            [numeric.expresso.impl.symbolic :as symb]
            [clojure.core.matrix :as matrix]
            [numeric.expresso.construct :as c]))

;;in this namespace are most of expresso's simplification rules defined
;;It also serves as demonstration of the power of the rule based approach btw.


;;utility functions for the eval-rules which eval a whole expression if it
;;contains no undetermined part or evaluates part of it

(defn- calc-reso
  "core.logic relation which calcualates the expression. Not relational"
  [expr]
  (fn [res]
    (project [expr]
             (== (evaluate expr nil) res))))

(defn- no-symbolso
  "succeeds if there are no symbols in the given expression"
  [expr]
  (project [expr]
           (fresh []
                  (== true (and (expr-op expr) (no-symbol expr))))))

(defn- contains-no-var? [expr]
  (if (and (not (symbol? expr)) (no-symbol expr)) true false))

(defn- collapse-arguments-commutative
  "folds constants in commutative functions"
  [xs args]
  (let [gb (group-by contains-no-var? args)
        fix (concat (gb nil) (gb true))
        var (gb false)]
    (if (or (empty? fix) (< (count fix) 2))
            (list* xs args)
            (list* xs (evaluate (list* xs fix) {}) var))))

(defn- collapse-arguments-associative
  "folds constants in associative functions"
  [xs args]
  (let [parts (partition-by contains-no-var? args)
        eval-parts (fn [part]
                     (if (and (and (coll? part) (> (count part) 1))
                              (or (= nil (contains-no-var? part)) (contains-no-var? part)))
                       [(evaluate (list* xs part) nil)]
                       part))
        mc (mapcat eval-parts parts)]
    (list* xs mc)))

(defn- compute-subexpression
  "computes subexpressions of expr"
  [expr]
  (if (coll? expr)
    (let [[xs & args] expr]
      (cond #_(isa? xs 'e/ca-op)
            (contains? (:properties (meta xs)) :commutative)
            (collapse-arguments-commutative xs args)
            (contains? (:properties (meta xs)) :associative)
            (collapse-arguments-associative xs args)
            (isa? xs 'e/ao-op) (collapse-arguments-associative xs args)
            :else expr))
    expr))
                                                        
(defn- compute-subexpressiono
  "core.logic version of compute-subexpression"
  [expr]
  (fn [res]
    (project [expr]
             (let [tmp (compute-subexpression expr)]
               (if (= tmp expr)
                 fail
                 (== res tmp))))))


(defn- symbolo [x] (project [x] (== true (symbol? x))))


(defn- with-shape
  "sets the inferred shape of the value. expands to zero- and identity-matrices
   where appropriate"
   [val shape]
  (cond
   (utils/num= val 0) (if (or (lvar? shape) (sequential? shape))
                        (value (zero-matrix :shape shape)) 0)
   (utils/num= val 1) (if (or (lvar? shape) (sequential? shape))
                        (value (identity-matrix :shape shape)) 1)
   :else (set-inferred-shape val shape)))
    

(construct-with [+ - * / **  ln sin cos sqrt exp log mzero? midentity? inner-product inverse
                 shape?]
;;to read the rule examples
;; :==> means that the transition is an in-line clojure function
;; ?&* matches zero or more elements of the expression
;; ?&+ matches one or more elements of the expression                
;; shape? mzero? and midentity? are extractors.
;; (shape? pattern ?s) matches the pattern and unifies the shape of the pattern
;; with ?s                
;; (mzero? ?x) succeeds if ?x is some zero-matrix so 0, 0.0, [[0.0]], etc.
;; (midentity? ?x) is like mzero but succeeds for identity-matrices
                
(def arity-rules
  [(rule (shape? (+) ?s) :==> (with-shape 0 ?s))
   (rule (shape? (*) ?s) :==> (with-shape 1 ?s))
   (rule (shape? (+ ?x) ?s) :==> (with-shape ?x ?s))
   (rule (shape? (* ?x) ?s) :==> (with-shape ?x ?s))])

(def universal-rules
  (concat arity-rules
    [(rule (+ (mzero? ?x) ?&*) :=> (+ ?&*))
     (rule (shape? (* (mzero? ?x) ?&*) ?s) :==> (with-shape 0 ?s))
     (rule (* (midentity? ?x) ?&*) :=> (* ?&*))
     (rule (* ?x (- ?x) ?&*) :=> (* -1 (** ?x 2) ?&*))
     (rule (** ?x 1) :=> ?x)
     (rule (** ?x 1.0) :=> ?x)
     (rule (** ?x 0.0) :=> 1)
     (rule (** ?x 0) :=> 1
           :if (guard (not= ?x 0)))
     (rule (** (** ?x ?n1) ?n2) :=> (** ?x (* ?n1 ?n2)))
     (rule (* (* ?&*) ?&*r) :=> (* ?&* ?&*r))
     (rule (+ (+ ?&*) ?&*r) :=> (+ ?&* ?&*r))
     (rule (inner-product ?&*1 (inner-product ?&*2) ?&*3)
           :=> (inner-product ?&*1 ?&*2 ?&*3))
     (rule (shape? (- (mzero? ?y) ?x) ?s) :==> (with-shape (- ?x) ?s))
     (rule (- ?x 0) :=> ?x)
     (rule (+ (* ?x ?y) (* ?z ?y) ?&*) :=> (+ (* (+ ?x ?z) ?y) ?&*)
           :if (guard (and (number? ?x) (number? ?z))))
     ]))

(def eval-rules
  [(rule ?x :=> (calc-reso ?x) :if (no-symbolso ?x))
   (rule ?x :=> (compute-subexpressiono ?x))])


(def simplify-rules
  [(rule (* ?x ?x ?&*) :=> (* (** ?x 2) ?&*))
   (rule (inverse (inverse ?x)) :=> ?x)
   (rule (shape? (inner-product ?&*1 (mzero? ?x) ?&*2) ?s)
         :==> (with-shape 0 ?s))
   (rule (shape? (inner-product ?&*1 (midentity? ?x) ?&*2) ?s)
         :==> (with-shape (inner-product ?&*1 ?&*2) ?s))
   (rule (shape? (inner-product ?&*1 ?x (inverse ?x) ?&*2) ?s)
         :==> (with-shape (inner-product ?&*1 ?&*2) ?s))
   (rule (shape? (inner-product ?&*1 (inverse ?x) ?x ?&*2) ?s)
         :==> (with-shape (inner-product ?&*1 ?&*2) ?s))
   (rule (shape? (* ?x (/ ?x) ?&*) ?s) :==> (with-shape (* ?&*) ?s))
   (rule (shape? (+ ?x (- ?x) ?&*) ?s) :==> (with-shape (+ ?&*) ?s))
   (rule (+ ?x ?x ?&*) :=> (+ (* 2 ?x) ?&*))
   (rule (+ (* ?x ?&*) (- ?x) ?&*2) :=> (+ (* ?x (- ?&* 1)) ?&*2))
   (rule (+ (* ?x ?&*) (* ?x ?&*2) ?&*3)
         :=> (+ (* ?x (+ (* ?&*) (* ?&*2))) ?&*3))
   (rule (+ (* ?x ?&*) ?x ?&*2) :=> (+ (* ?x (+ (* ?&*) 1)) ?&*2))
   (rule (- (- ?x)) :=> ?x)
   (rule (* -1 (- ?x) ?&*) :=> (* ?x ?&*))
   (rule (* ?x (** ?x ?n) ?&*) :=> (* (** ?x (+ ?n 1)) ?&*))
   (rule (** (** ?x (/ ?y)) ?y) :=> ?x)
   (rule (** (** ?x ?n) ?m) :=> ?x :if (guard (and (number? ?n) (number? ?m)
                                                   (= (/ ?m) ?n))))
   (rule (** (sqrt ?x) 2) :=> ?x)
   (rule (** (- ?x) 2) :=> (** ?x 2))])

;;the normal behaviour of (- args*) and (/ args*) is not really good for rule
;;based translation. It is not commutative and the arguments have different
;;meaning depending on what positions they are in the argument list.
;;these rules are converting (- a b c) to (+ a (- b) (- c)) so that the resulting
;;expression is easier to manipulate because only 1-ary - is there which means
;;negation and the + expression is commutative

(def to-inverses-rules
  [(rule (- ?x ?&+) :==>(+ ?x (map-sm #(- %) ?&+)))
   (rule (- (+ ?&+)) :==> (+ (map-sm #(- %) ?&+)))
   (rule (- (* ?&+)) :=> (* -1 ?&+))
   (rule (/ ?x ?&+) :==> (* ?x (map-sm #(/ %) ?&+)))])

(def cancel-inverses-rules
  (concat arity-rules
          [(rule (+ (- ?x ?&+) (- ?y) ?&*) :=> (+ (- ?x ?&+ ?y) ?&*))
           (rule (+ ?x (- ?y) ?&*) :=> (+ (- ?x ?y) ?&*))
           (rule (* (/ ?x ?&+) (/ ?y) ?&*) :=> (* (/ ?x ?&+ ?y) ?&*))
           (rule (* ?x (/ ?y) ?&*) :=> (* (/ ?x ?y) ?&*))]))

(declare multinomial)

;;this rules are a good example for the convenience of being able to have
;;arbitrary clojure code as the transition part of the rule
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
         :if (guard (not= 0 ?x)))
   (rule (** (/ ?a ?b) ?x) :=> (/ (** ?a ?x) (** ?b ?x)))
   (rule (** (/ ?a) ?x) :=> (/ (** ?a ?x)))
   (rule (sqrt (/ ?a ?b)) :=> (/ (sqrt ?a) (sqrt ?b)))
]
  )

(def partly-multiply-out-rules
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
   (rule (* ?x (/ ?x) ?&*) :=> (* ?&*)
         :if (guard (not= 0 ?x)))
   (rule (** (/ ?a ?b) ?x) :=> (/ (** ?a ?x) (** ?b ?x)))
   (rule (** (/ ?a) ?x) :=> (/ (** ?a ?x)))
   (rule (sqrt (/ ?a ?b)) :=> (/ (sqrt ?a) (sqrt ?b)))
]
  )

(def log-solve-rules
  (with-meta
    (concat universal-rules
            eval-rules
            to-inverses-rules
            multiply-out-rules
            [(rule (+ (log ?x) (log ?y)) :=> (log (* ?x ?y)))
             (rule (- (log ?x) (log ?y)) :=> (log (/ ?x ?y)))
             (rule (log (exp ?x)) :=> ?x)
             (rule (exp (log ?x)) :=> ?x)
             (rule (exp (- ?x)) :=> (/ (exp ?x)))
             (rule (exp (+ ?&*)) :==> (* (map-sm #(exp %) ?&*)))
             (rule (exp (* (log ?x) ?&*)) :=> (** ?x (* ?&*)))])
    {:id 'log-solve-rules}))

(def square-solve-rules
  (with-meta
    (concat universal-rules
            eval-rules
            to-inverses-rules
            [(rule (** (sqrt ?x) 2) :=> ?x)
             (rule (** ?x 0.5) :=> (sqrt ?x))
             (rule (** ?x (/ 2)) :=> (sqrt ?x))
             (rule (** ?x 1/2) :=> (sqrt ?x))
             (rule (** (* ?&+) ?n) :==> (* (map-sm #(** % ?n) ?&+))
                   :if (guard (integer? ?n)))
             (rule (** (** ?x ?n1) ?n2) :==> (** ?x (clojure.core/* ?n1 ?n2))
                 :if (guard (integer? ?n)))
             (rule (** (+ ?&+) ?n) :==> (multinomial ?n (matcher-args ?&+))
                   :if (guard (integer? ?n)))
             (rule (* ?x (/ ?x) ?&*) :=> (* ?&*)
                   :if (guard (not= 0 ?x)))
             (rule (** (- ?x) 2) :=> (** ?x 2))
             (rule (* ?x ?x ?&*) :=> (* (** ?x 2) ?&*))
             (rule (/ (* ?&*)) :==> (* (map-sm #(/ %) ?&*)))
             (rule (* ?x (/ ?x) ?&*) :=> (* ?&*))
             (rule (+ ?x (- ?x) ?&*) :=> (+ ?&*))
             (rule (+ ?x ?x ?&*) :=> (+ (* 2 ?x) ?&*))
             (rule (+ (* ?x ?&*) (- ?x) ?&*2) :=> (+ (* ?x (- ?&* 1)) ?&*2))
             (rule (+ (* ?x ?&*) (* ?x ?&*2) ?&*3)
                   :=> (+ (* ?x (+ (* ?&*) (* ?&*2))) ?&*3))
             (rule (+ (* ?x ?&*) ?x ?&*2) :=> (+ (* ?x (+ (* ?&*) 1)) ?&*2))
             (rule (- (- ?x)) :=> ?x)
             (rule (* -1 (- ?x) ?&*) :=> (* ?x ?&*))
             (rule (* ?x (** ?x ?n) ?&*) :=> (* (** ?x (+ ?n 1)) ?&*))
             (rule (* (- ?x) ?&*) :=> (- (* ?x ?&*)))
             (rule (/ (* ?&*)) :==> (* (map-sm #(/ %) ?&*)))
             (rule (* (sqrt ?x) (sqrt ?y) ?&*) :=> (* (sqrt (* ?x ?y)) ?&*))
             (rule (** (* ?&*) ?x) :==> (* (map-sm #(** % ?x) ?&*)))
             (rule (** (/ ?x) ?a) :=> (/ (** ?x ?a)))
             ])
    {:id 'square-solve-rules}))

)
(defn- binom [n k]
  (let [rprod (fn [a b] (reduce * (range a (inc b))))]
    (/ (rprod (- n k -1) n) (rprod 1 k))))

(defn- factorial [n]
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

(defn- multinomial-coeff [n indices]
  (quot (factorial n) (reduce * (map factorial indices))))

(defn- to-factors [args index]
  (loop [i 0 index index ret []]
    (if (= i (count args))
      ret
      (recur (inc i) (rest index)
             (cond
              (= (first index) 0) ret
              (= (first index) 1) (conj ret (nth args i))
               :else (conj ret (ex' (** ~(nth args i) ~(first index)))))))))

(defn- multinomial
  "multiplies out according to multinomial theorem"
  [n args]
  (let [args (vec args)
        m (count args)
        indices (multinomial-indices m n)]
    (ce `+ (seq-matcher (for [index indices]
                          (let [factors (seq-matcher (to-factors args index))
                                coeff (multinomial-coeff n index)]
                            (if (= 1 coeff)
                              factors
                              (ex' (* coeff factors)))))))))

(def normalize-rules
  (with-meta
     (concat eval-rules universal-rules to-inverses-rules
             partly-multiply-out-rules)
     {:id :simp-expr-rules1}))

(def simplify-rules
  (with-meta
    (concat universal-rules
            eval-rules simplify-rules)
    {:id :simp-expr-rules2}))

(defn simp-expr
  "simplifies the given expression according to simp-rules"
  ([expr]
     (simp-expr expr simplify-rules))
  ([expr simp-rules]
     (->> expr 
          (transform-expression normalize-rules)
          (transform-expression simp-rules))))




(defn- infer-shape-zero-mat [sf x sl]
  (let [series (concat (matcher-args sf) [x] (matcher-args sl))]
    (if (= (count series) 1)
      x
      (let [s (filter identity [(first (shape (first series)))
                                       (last (shape (last series)))])]
        (if (some symbol? series)
          (zero-matrix s)
          (matrix/broadcast 0 s))))))

(defn- identity-right-shape [a]
  (let [s (shape a)]
    (cond
     (empty? s) 1
     (symbol? a) (identity-matrix (first s))
     :else (matrix/identity-matrix (first s)))))




(defn multiply-out
  "fully multiplies the given expression out"
  [expr]
  (transform-expression (concat universal-rules
                                to-inverses-rules multiply-out-rules) expr))

(defn evaluate-constants
  "evaluates constants and constant subexpressions in expr"
  [expr]
  (transform-expression eval-rules expr))

(defn normalise
  "normalises the expression for further manipulation with expresso
   rules."
  [expr]
  (transform-expression (concat universal-rules to-inverses-rules) expr))