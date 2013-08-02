(ns numeric.expresso.core
  (:refer-clojure :exclude [==])
  (:require [numeric.expresso.solve :as solve]
            [numeric.expresso.optimize :as opt]
            [numeric.expresso.protocols :as protocols]
            [numeric.expresso.matcher :as match]
            [numeric.expresso.rules :as rules]
            [numeric.expresso.parse :as parse]
            [numeric.expresso.utils :as utils]
            [numeric.expresso.properties :as props]
            [numeric.expresso.construct :as constr])) 



(defmacro ex
  "constructs an expression from the given s-exp. variables are automatically
   quoted. Unquote can be used to supply the value for a variable in scope
   example:
   (ex (+ x (* x y)))
   (let [x 3]
     (ex (+ x (* ~x y))))
   Expresso expressions are still clojure s-expressions and can be fully
   manipulated with the clojure seq functions if wished."
  [expr]
  (constr/ex* expr))

(defmacro ex'
  "like ex but constructs the expressions with explicit quoting needed, so
   (let [x 3] (ex' (+ 3 x))) :=> (clojure.core/+ 3 3)
   supports an optional vector of symbols as first argument, which are implicitly
   quoted in the expression:
   (let [x 3] (ex' [x] (+ 3 x))) :=> (clojure.core/+ 3 x)"
  ([expr] (constr/ex'* expr))
  ([symbv expr] (apply constr/ex'* [symbv expr])))



(defn parse-expression
  "parses the expression from the given string supports + - * / ** with the
   normal precedence. unnests operators where possible
   examples:
   (parse-expression \"1+2+3\") :=> (clojure.core/+ 1 2 3)
   (parse-expression \"1+2*3**4+5\")
     :=> (clojure.core/+ 1 (clojure.core/* 2 (numeric.expresso.core/** 3 4)) 5)"
   [s]
   (parse/parse-expression s))
   
(defn evaluate
  "evaluates the expression after replacing the symbols in the symbol map with
   their associated values"
  ([expr] (evaluate expr {}))
  ([expr sm]
     (-> expr
      constr/to-expression
      (protocols/evaluate sm))))

(defn substitute [expr repl]
  "substitutes every occurrence of a key in the replacement-map by its value"
  (-> expr
      constr/to-expression
      (protocols/substitute-expr repl)))


(defn simplify
  "simplifies the given expression to a shorter form"
  [expr]
  (->> expr
       constr/to-expression
       solve/simp-expr))

(defn to-polynomial-normal-form
  "transforms the given expression to a fully expanded polynomial representation
   regarding the variable v"
  [v expr]
  (->> expr
       constr/to-expression
       (solve/to-polynomial-normal-form v)))

(defn rearrange
  "if the equation contains only one occurrence of v it will be rearranged so
   that v is the only symbol on the lhs of the equation."
  [v eq]
  (->> eq
       constr/to-expression
       utils/validate-eq
       (solve/rearrange v)))

(defn solve
  "solves the given equation in regard to the variable v"
  [v eq]
  (->> eq
       constr/to-expression
       utils/validate-eq
       (solve/solve v)))

(defn differentiate
  "Differentiates the given expression regarding the symbols in the symbol
   vector symbv"
  [symbv expr]
  (let [expr (->> expr constr/to-expression)]
    (reduce #(solve/differentiate %2 %1) expr symbv)))

(defmacro compile-expr
  "compiles the given expression to a clojure function which can be called with
   a symbol-map"
  [expr]
  (->> expr
       (opt/compile-expr*)))

(defn optimize
  "optimizes the given expression"
  [expr]
  (->> expr
       constr/to-expression
       (opt/optimize )))

(defn ^:dynamic **
  "default exponentiation operator."
  [a b]
  (Math/pow a b))


#_(run* [q]  (== q #{}))