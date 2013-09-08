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
            [numeric.expresso.matcher :as m]
            [numeric.expresso.simplify :as simp]
            [numeric.expresso.construct :as c]))

(declare remove-common-subexpressions)
(defn map-elems [func expr]
  (if-let [op (expr-op expr)]
    (cev op (map (partial map-elems func) (expr-args expr)))
    (func expr)))

(defn zip [& colls]
  (apply (partial map (fn [& a] a)) colls))

(defn subexpressions [expr]
  (filter expr-op (rest (tree-seq expr-op expr-args expr))))

(defn matching-subexpressions [subs]
  (run* [q]
        (fresh [a b rem]
               (rembero a subs rem)
               (membero b rem)
               (condu ((m/match-expressiono a b)))
               (== q [a b]))))

(defn match? [a b] (not (empty? (run 1 [q] (m/match-expressiono a b)))))

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
                           :if (guard (not= ?x ?k)))]))




(defn optimize-by-rules [expr]
  (transform-expression (concat simp/universal-rules
                                simp/eval-rules simp/to-inverses-rules
                                simp/universal-rules optimize-rules) expr))

(defn replace-with-special-operations [expr]
  (transform-expression
   (concat simp/universal-rules
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
  [(rule (ex (inner-product ?&+)) :==>
         (let [args (matcher-args ?&+)
                 args (partition-by (comp count shape) args)
               args (map #(if (and (not (expr-op (shape (first %))))
                                   (= (count (shape (first %))) 2))
                              (optimize-matrix-chain-order (vec %))
                              (seq-matcher %)) args)]
           (cev 'inner-product args))
           :if (guard (> (count-sm ?&+) 2)))])

(defn optimize-matrix-chain [expr]
  (transform-expression
   [(rule (ex (inner-product ?x)) :=> ?x)]
   (walk/postwalk #(apply-rules matrix-chain-rules %) expr)))
    

(defn eval-func [expr]
  (fn [sm]
    (evaluate expr sm)))

(defn compile-expr* [bindings expr]
  (let [expr (to-expression expr)
        code (emit-code expr)
        c (list `fn bindings code)]
     (eval c)))

(defmacro compile-expr [bindings expr]
  `(compile-expr* ~(list 'quote bindings) ~expr)) 

(def optimizations
  [optimize-by-rules
   optimize-matrix-chain
   replace-with-special-operations
   remove-common-subexpressions])


(defn optimize [expr]
  (loop [opt optimizations expr expr]
    (if (seq opt)
      (recur (rest opt) ((first opt) expr))
      expr)))