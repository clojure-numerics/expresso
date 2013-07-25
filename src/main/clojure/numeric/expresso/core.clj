(ns numeric.expresso.core
  (:refer-clojure :exclude [==])
  (:require [numeric.expresso.solve :as solve]
            [numeric.expresso.optimize :as opt]
            [numeric.expresso.protocols :as protocols]
            [numeric.expresso.matcher :as match]
            [numeric.expresso.rules :as rules]
            [numeric.expresso.properties :as props]
            [numeric.expresso.construct :as constr])) 

(defn ^:dynamic ** [a b]
  (Math/pow a b))

(defn expression?
  "checks if the given argument is suitable for manipulation with
   expresso, for example such expressions constructed with one of
   expressos constructing functions"
  [expr]
  (boolean (protocols/expr-op expr)))

(defn evaluate
  "evaluates the expression after replacing the symbols in the symbol map with
   their associated values"
  [expr sm]
  (protocols/evaluate expr sm))

(defn substitute [expr repl]
  "substitutes every occurrence of a key in the replacement-map by its value"
  (protocols/substitute-expr expr repl))


(defn simplify
  "simplifies the given expression to a shorter form"
  [expr]
  (solve/simp-expr expr))

(defn to-polynomial-normal-form
  "transforms the given expression to a fully expanded polynomial representation
   regarding the variable v"
  [v expr]
  (solve/to-polynomial-normal-form v expr))

(defn rearrange
  "if the equation contains only one occurrence of v it will be rearranged so
   that v is the only symbol on the lhs of the equation"
  [v eq]
  (solve/rearrange v eq))

(defn differentiate
  "Differentiates the given expression regarding the variable v"
  [v expr]
  (solve/differentiate v expr))

(defmacro compile-expr
  "compiles the given expression to a clojure function."
  [expr]
  (opt/compile-expr* expr))

(defn optimize
  "optimizes the given expression"
  [expr]
  (opt/optimize expr))

(defn define-extractor
  "defines and installs an extractor with the given name and relation.
   The relation will be called during matching and unifies the arguments
   of the extractor with the expression it is being matched with"
  [name rel]
  (.addMethod props/extractor-rel name (fn [_] rel)))

(defn apply-rule
  "applies the specified rule to the epxression returning a modified one if the
   rule was applicable of nil if the rule was not applicable"
  [rule exp]
  (rules/apply-rule rule exp))

(defn apply-rules
  "returns the result of the first succesful application of a rule in the rules
   vector"
  [rules expr]
  (rules/apply-rules rules expr))

(defn transform-with-rules
  "transforms the expr according to the rules in the rules vector until no rule
   can be applied any more. Uses clojure.walk/prewalk to walk the expression tree
   in the default case. A custom walkfn and applyfn can be specified defaults to
   clojure.walk/postwalk and apply-rules"
  ([rules expr] (rules/transform-with-rules rules expr))
  ([rules expr walkfn applyfn] (rules/transform-with-rules
                                 rules expr walkfn applyfn)))


(defn transform-expression
  "transforms the expression according to the rules in the rules vector in a
   bottom up manner until no rule can be applied to any subexpression anymore"
  [rules expr]
  (rules/transform-expression rules expr))
