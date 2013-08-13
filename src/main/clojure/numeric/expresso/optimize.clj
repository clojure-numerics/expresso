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
            [clojure.core.matrix.operators :as mop]
            [numeric.expresso.matcher :as m]
            [numeric.expresso.common-rules :as cr]
            [numeric.expresso.construct :as c]))

(declare remove-common-subexpressions)



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
     (let-expr (vec (mapcat (fn [[l s]] [l (first s)]) locals))
               [(to-sexp expr)])))
(construct-with [* + / - ** sum]
(def optimize-rules [(rule (* ?x ?x ?&*) :=> (* (** ?x 2) ?&*))               
                     (rule (* ?x (/ ?x) ?&*) :=> (* ?&*))
                     (rule (+ (* ?x ?n1) (* ?x ?n2) ?&*) :==>
                           (+ (* ?x (clojure.core/+ ?n1 ?n2)) ?&*))
                     (rule (+ (* ?a ?&*1) (* ?a ?&*2) ?&*r)
                           :==> (+ (* ?a (+ ?&*1 ?&*2)) ?&*r))
                     (rule (* ?x (/ ?x) ?&*) :=> (* ?&*))
                     (rule (+ ?x (- ?x) ?&*) :=> (+ ?&*))
                     (rule (+ (* ?x ?&*) (- ?x) ?&*2)
                           :=> (+ (* ?x (- ?&* 1)) ?&*2))
                     (rule (+ (* ?x ?&*) ?x ?&*2) :=> (+ (* ?x (+ ?&* 1)) ?&*2))
                     (rule (- (- ?x)) :=> ?x)
                     (rule (sum ?k ?i (* ?x ?&*)) :=> (* ?x (sum ?k ?i (* ?&*)))
                           :if (guard (not= ?x ?k)))]))




(defn optimize-by-rules [expr]
  (transform-expression (concat cr/universal-rules
                                cr/eval-rules cr/to-inverses-rules
                                cr/universal-rules optimize-rules) expr))

(defn replace-with-special-operations [expr]
  (transform-expression [(rule (ex (** ?x 0.5)) :=> (ex (sqrt ?x)))
                         (rule (ex (** ?x 1/2)) :=> (ex (sqrt ?x)))] expr))

(defn eval-func [expr]
  (fn [sm]
    (evaluate expr sm)))



(defn compile-expr* [bindings expr]
  `(let [expr# (to-expression ~expr)
         code# (emit-code expr#)
         c# (list `fn ~bindings code#)]
     (eval c#)))

(defmacro compile-expr [bindings expr]
  (compile-expr* (list 'quote bindings) expr)) 

(def optimizations
  (atom [optimize-by-rules
         replace-with-special-operations
         remove-common-subexpressions]))

(defn optimize* [expr]
  (loop [opt @optimizations expr expr]
    (if (seq opt)
      (recur (rest opt) ((first opt) expr))
      expr)))


(defn optimize [expr]
  (->> expr optimize* eval-func))