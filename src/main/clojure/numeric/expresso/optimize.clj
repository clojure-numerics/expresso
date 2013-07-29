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
            [numeric.expresso.construct :as c]))

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


(defn eval-func [expr]
  (fn [sm]
    (evaluate expr sm)))

(defmacro compile-expr [expr]
  `(fn [sm#]
     (evaluate ~expr sm#)))

(defn compile-expr* [expr]
  `(fn [sm#] (-> ~expr
                 to-expression
                 (evaluate sm#))))

(defn optimize* [expr]
  (->> expr  remove-common-subexpressions))


(defn optimize [expr]
  (->> expr optimize* eval-func))

