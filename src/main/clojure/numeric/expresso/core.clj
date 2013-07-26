(ns numeric.expresso.core
  (:refer-clojure :exclude [==])
  (:require [numeric.expresso.solve :as solve]
            [numeric.expresso.optimize :as opt]
            [numeric.expresso.protocols :as protocols]
            [numeric.expresso.matcher :as match]
            [numeric.expresso.rules :as rules]
            [numeric.expresso.parse :as parse]
            [numeric.expresso.properties :as props]
            [numeric.expresso.construct :as constr])) 


(defn ce
  "constructs an expression from the symbol with the supplied args"
  [symb & args]
  (apply (partial constr/ce symb) args))

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

(defmacro construct-with
  "replaces all occurences of the symbols in the symbol vector in the enclosed
   code by the corresponding calls to ce. Very handy for defining rules.
   No macros in the expansion so all the functions can be used in higher order
   functions. Variables need to be explicitly quoted. Example:
   (construct-with [+] (+ 1 2 3)) :=> (clojure.core/+ 1 2 3)"
  [symbv & code]
  (apply (partial constr/construct-with* symbv) code))

(defn parse-expression
  "parses the expression from the given string supports + - * / ** with the
   normal precedence. unnests operators where possible
   examples:
   (parse-expression \"1+2+3\") :=> (clojure.core/+ 1 2 3)
   (parse-expression \"1+2*3^4+5\")
     :=> (clojure.core/+ 1 (clojure.core/* 2 (numeric.expresso.core/** 3 4)) 5)"
   [s]
   (parse/parse-expression s))
   

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

(defmacro rule
  "constructs a rule. Syntax is (rule pat :=> trans) pat is a normal expression
   which can contain symbols starting with a ? which will be transformed to
   logic variables which are unified while matching the an expression to the
   pattern. trans can also be an expression containing lvars or it can be an
   arbitrary core.logic relation which takes the transformed rule as its output
   argument. :==> can be used to automatically translate a normal inline clojure
   function to the needed core.logic relation.
   It supports an optional guard argument. Syntax is then (rule pat :=> trans :if
   guard) guard is a core.logic relation which is called after matching the pat
   with the expression and succeeds if the rule is applicable or fails if not."
  [& v]
  (rules/rule* v))

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

(defn solve
  "solves the given equation in regard to the variable v"
  [v eq]
  (solve/solve v eq))

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

(defn ^:dynamic **
  "default exponentiation operator."
  [a b]
  (Math/pow a b))
