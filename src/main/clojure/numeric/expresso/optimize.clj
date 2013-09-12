(ns numeric.expresso.optimize
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
            [clojure.core.memoize :as memo]
            [clojure.core.matrix.operators :as mop]
            [numeric.expresso.impl.matcher :as m]
            [numeric.expresso.simplify :as simp]
            [numeric.expresso.construct :as c]))

;;This namespace provides the expresso optimizer. It strives to be very
;;extensible by relying on rule based translation and being datadriven by
;;a vector of optimizations which gets applied in sequence. The main function
;;of this namespace is optimize.

;;It also provides support to *compile* an expression to a (no overhead) clojure
;;function. See the compile-expr macro and compile-expr* function for reference


(declare remove-common-subexpressions)

(defn- map-elems
  "map the leaves of the expression. retains metadata unles postwalk"
  [func expr]
  (if-let [op (expr-op expr)]
    (cev op (map (partial map-elems func) (expr-args expr)))
    (func expr)))

(defn- zip [& colls]
  (apply (partial map (fn [& a] a)) colls))


(defn subexpressions [expr]
  (filter expr-op (rest (tree-seq expr-op expr-args expr))))

;;This core.logic relation finds all combinations of two subexpression in subexpressions
;;which are the same. Note that for now the test is just the match-expressiono function
;;In future this can be replaced by a more clever function which recognizes more
;;expressions as being equivalent

(defn matching-subexpressions [subs]
  (run* [q]
        (fresh [a b rem]
               (rembero a subs rem)
               (membero b rem)
               (condu ((m/match-expressiono a b)))
               (== q [a b]))))

(defn match? [a b] (not (empty? (run 1 [q] (m/match-expressiono a b)))))

;;from all pairs of matching subexpressions the subexpressions which match must be concat-
;;enated, so that we get a list of equivalent-classes which consists of the set of all
;;forms occurring in the expression which are equivalent

(defn concat-aq [msubs]
  (reduce (fn [[aq r] next]
            (let [a (first aq)
                  b (second next)]
              (if (match? a b)
                [(apply (partial conj aq) next) r]
                [aq (conj r next)])))
          [(first msubs) []] (rest msubs)))

(defn equivalent-subexpressions [msubs]
  (loop [msubs msubs aquiv []]
    (if (seq msubs)
      (let [[aq r] (concat-aq msubs)
            same (into #{} aq)]
        (recur r (conj aquiv same)))
      aquiv)))

(defn common-subexpressions [expr]
  (->> expr
      subexpressions
      matching-subexpressions
      equivalent-subexpressions))

;;to remove the common subexpressions, a let is created with a binding for each
;;set of equivalent subexpressions each subexpression in the set is then substituted
;;for the binding.
(defn remove-common-subexpressions [expr]
  (let [cs (common-subexpressions expr)
        locals (zip (repeatedly #(gensym 'local)) cs)
        expr (reduce (fn [expr [s repl]]
                       (reduce #(substitute-expr %1 {%2 s}) expr repl))
                     expr locals)]
    (if (empty? cs)
      expr
      (let-expr (vec (mapcat (fn [[l s]] [l (first s)]) locals))
                [(to-sexp expr)]))))

(construct-with [* + / - ** sum]
(def optimize-rules [(rule (* ?x ?x ?&*) :=> (* (** ?x 2) ?&*))
                     (rule (+ ?x ?x ?&*) :=> (+ (* 2 ?x) ?&*))              
                     (rule (* ?x (/ ?x) ?&*) :=> (* ?&*))
                     (rule (+ (* ?a ?&*1) (* ?a ?&*2) ?&*r)
                           :=> (+ (* ?a (+ ?&*1 ?&*2)) ?&*r))
                     (rule (* ?x (/ ?x) ?&*) :=> (* ?&*))
                     (rule (+ ?x (- ?x) ?&*) :=> (+ ?&*))
                     (rule (+ (* ?x ?&*) (- ?x) ?&*2)
                           :=> (+ (* ?x (- ?&* 1)) ?&*2))
                     (rule (+ (* ?x ?&*) ?x ?&*2) :=> (+ (* ?x (+ ?&* 1)) ?&*2))
                     (rule (- (- ?x)) :=> ?x)
                     (rule (sum ?k ?i (* ?x ?&*)) :=> (* ?x (sum ?k ?i (* ?&*)))
                           :if (guard (not= ?x ?k)))
                     (rule (* (- ?x) ?&*) :=> (- (* ?x ?&*)))]))


(defn optimize-by-rules [expr]
  (->> expr
       (transform-expression (concat simp/universal-rules
                                     simp/eval-rules simp/to-inverses-rules
                                     optimize-rules))
       (transform-expression simp/cancel-inverses-rules)))
  
(defn replace-with-special-operations [expr]
  (transform-expression
   (concat simp/arity-rules
           [(rule (ex (** ?x 0.5)) :=> (ex (sqrt ?x)))
            (rule (ex (** ?x 1/2)) :=> (ex (sqrt ?x)))
            (rule (ex (+ ?m (* ?a ?b) ~?&*))
                  :=> (ex (+ (add-product ?m ?a ?b) ~?&*))
                  :if (guard (let [shapes (map shape [?m ?a ?b])]
                               (and (not (some #{[]} shapes))
                                    (not (some lvar? shapes))
                                    (every? #{(shape ?m)} shapes)))))
            ]) expr))

(defn add-parens [symb args i j]
  (cev symb (concat (subvec args 0 i) [(cev symb (subvec args i j))]
                    (subvec args j (count args)))))
        

(def matrix-chain-cost*
  (memo/memo
   (fn [shapes i j]
     (if (= i j)
       [0 [(dec i)]]
       (loop [k (long i) minimum Long/MAX_VALUE expr []]
         (if (< k j)
           (let [[costl parensl] (matrix-chain-cost* shapes i k)
                 [costr parensr] (matrix-chain-cost* shapes (inc k) j)
                 cost (+ costl costr
                         (* (nth shapes (dec i))
                            (nth shapes k)
                            (nth shapes j)))]
             (recur (inc k) (if (< minimum cost) minimum cost)
                    (if (< minimum cost) expr (cev 'inner-product
                                                   (concat parensl parensr)))))
           [minimum [expr]]))))))

(defn matrix-chain-cost [shapes i j]
  (let [res (matrix-chain-cost* shapes i j)]
    (memo/memo-clear! matrix-chain-cost*)
    res))


(defn optimize-matrix-chain-order [args]
  (let [shapes (vec (concat (shape (first args))
                            (map (comp second shape) (rest args))))]
    (-> (first (second (matrix-chain-cost shapes 1 (dec (count shapes)))))
        (substitute-expr args))))

(def matrix-chain-rules
  [(rule (ex (inner-product ?x)) :=> ?x)
   (rule (ex (inner-product ?&+)) :==>
         (when (> (count-sm ?&+) 2)
           (let [args (matcher-args ?&+)
                 args (partition-by (comp count shape) args)
                 args (map #(if (and (not (expr-op (shape (first %))))
                                   (= (count (shape (first %))) 2))
                              (optimize-matrix-chain-order (vec %))
                              (seq-matcher %)) args)]
             (cev 'inner-product args)))
           :if (guard (> (count-sm ?&+) 2)))])
  
(defn optimize-matrix-chain [expr]
  (transform-expression matrix-chain-rules expr))

;;compiling the expression works vial the emit-code protocol function defined
;;in protocols.clj. Because standart expressions are just ISeq they can be
;;evaluated almost as they are the only difficulty is that their operators
;;may not be in scope. Because of this in the normal case the generated code
;;is (exec-func args*). the emitted code will be the body of the function
;;with the bindings vector as argument list. the function is then constructed
;;with a call to eval. This also allows to use compile-expr* like compile-expr
;;with quoting of the bindings vector, and you can use it in higher order
;;functions


(defn compile-expr* [bindings expr]
  (let [expr (to-expression expr)
        code (emit-code expr)
        c (list `fn bindings code)]
     (eval c)))

(defmacro compile-expr [bindings expr]
  `(compile-expr* ~(list 'quote bindings) ~expr))

;;This is a *very* simple optimizations which just uses the eval-rules from
;;the simplification namespace. calculates all expressions which are determined
;;and even folds constants in associative or commutative operators. See
;;simplify.clj for more

(defn constant-folding [expr]
  (transform-expression simp/eval-rules expr))


(def optimizations
  [constant-folding
   remove-common-subexpressions
   optimize-by-rules
   optimize-matrix-chain
   replace-with-special-operations])

;;optimize takes an expression and returns an optimized expression which is
;;semantically identical but runs faster. It is based on a series of
;;optimizations specified in optimizations of which each take the expression
;;and optimize certain parts of it. See the documentation for the optimizations

(defn optimize
  ([expr] (optimize expr optimizations))
  ([expr optimizations]
     (loop [opt optimizations expr expr]
       (if (seq opt)
         (recur (rest opt) ((first opt) expr))
         expr))))
  

