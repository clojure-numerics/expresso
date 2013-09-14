(ns numeric.expresso.core
  (:refer-clojure :exclude [==])
  (:require [clojure.core.logic :as logic]
            [numeric.expresso.solve :as solve]
            [numeric.expresso.simplify :as simp]
            [numeric.expresso.optimize :as opt]
            [numeric.expresso.protocols :as protocols]
            [numeric.expresso.rules :as rules]
            [numeric.expresso.parse :as parse]
            [numeric.expresso.calculus :as calc]
            [numeric.expresso.types :as types]
            [numeric.expresso.utils :as utils]
            [numeric.expresso.properties :as props]
            [numeric.expresso.impl.polynomial :as poly]
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
   (let [x 3] (ex' (+ 3 x))) :=> (+ 3 3)
   supports an optional vector of symbols as first argument, which are implicitly
   quoted in the expression:
   (let [x 3] (ex' [x] (+ 3 x))) :=> (+ 3 x)"
  ([expr] (constr/ex'* expr))
  ([symbv expr] (apply constr/ex'* [symbv expr])))

(defn expression?
  "tests whether the input is a compound expression.
   Examples: (expression? (ex (+ 1 2))) ;=> true
             (expression? '(+ 1 2)) ;=> true
             (expression? [+ 1 2]) ;=> false"
  [expr]
  (-> expr
      constr/to-expression
      protocols/expr-op
      boolean))

(defn constant?
  "tests whether the input is a constant. The negation of expression?.
   Examples: (constant? 5) ;=> true
             (constant? [+ 1 2]) ;=> true
             (constant? '(+ 1 2)) ;=> false"
  [expr]
  (not (expression? expr)))
             

(defn properties
  "returns the set of properties which the given expression contains
   Example: (properties (expresso-symbol 'x :properties #{:positive}))
             => #{:positive})"
  [expr]
  (protocols/properties expr))

(defn vars
  "returns the set of variables in the given expression
   Example: (vars (ex (* x y x))) ;=> #{x y}"
  [expr]
  (protocols/vars expr))

(defn shape
  "returns the shape of the given expression. Can also return an lvar or an
   expression indicating that the shape couldn't fully be inferred.
   Example: (shape (ex (+ 1 2))) ;=> [], (shape (matrix-symbol 'x)) ;=> lvar..."
  [expr]
  (protocols/shape expr))

(defn expresso-symbol
  "annotates the given symbol with the information of its shape, type and
   properties. Types are defined in numeric.expresso.types.
   Example: (expresso-symbol 'x) ;=> x,
            (expresso-symbol 'x :properties #{:positive})
   ;=> 'x and (properties x) :=> #{:positive}"
  [symb & {:keys [shape type properties]
           :or {shape (logic/lvar 'shape)
                type types/number
                properties #{}}}]
  (constr/expresso-symb symb :shape shape :type type :properties properties))

(defn matrix-symbol
  "annotates the symbol so that it represents a matrix in expresso. Also accepts
   shape and properties keyword arguments
   Example: (matrix-symbol 'x :shape [2 2]) => 'x"
  [symb &{:keys [shape properties]
          :or {shape (logic/lvar 'shape)
               properties #{}}}]
  (constr/matrix-symb symb :shape shape :properties properties))

(defn zero-matrix
  "creates a symbol (or annotates the given symbol) to represent a zero-matrix
   Example: (properties (zero-matrix)) ;=> #{:mzero}"
  [& {:keys [shape symb properties]
      :or {shape (logic/lvar 'shape)
           symb (gensym "zeromat")
           properties #{:mzero}}}]
  (constr/zero-matrix :symb symb :shape shape :properties properties))

(defn identity-matrix
  "creates a symbol (or annotates the given symbol) to represent an
   identity-matrix. Example: (properties (identity-matrix)) ;=> #{:midentity}"
  [& {:keys [shape symb properties]
      :or {shape (logic/lvar 'shape)
           symb (gensym "identitymat")
           properties #{:midentity}}}]
  (constr/identity-matrix :shape shape :symb symb :properties properties))

(defn parse-expression
  "parses the expression from the given string supports = + - * / ** with the
   normal precedence. Also supports arbitrary functions in the input.
   Unnests operators where possible.
   examples:
   (parse-expression \"1+2+3\") :=> (+ 1 2 3)
   (parse-expression \"1+2*3**4+5\")
     :=> (+ 1 (* 2 (** 3 4)) 5)
   (parse-expression \"sin(x)**2 + cos(x)**2 = 1\")
     :=> (= (+ (** (sin x) 2) (** (cos x) 2)) 1)"
   [s]
   (parse/parse-expression s))
   
(defn evaluate
  "evaluates the expression after replacing the symbols in the symbol map with
   their associated values. Example: (evaluate (ex (* 2 x)) {'x 3}) :=> 6"
  ([expr] (evaluate expr {}))
  ([expr sm]
     (-> expr
      constr/to-expression
      (protocols/evaluate sm))))

(defn substitute [expr repl]
  "substitutes every occurrence of a key in the replacement-map by its value
   Example: (substitute (ex (+ (* a b) (* a b) (/ c d)))
             {(ex (* a b)) 'x 'c 'y 'd 'z}) => (+ x x (/ y z))"
  (-> expr
      constr/to-expression
      (protocols/substitute-expr repl)))


(defn- ratio-test [simplified-expr expr ratio]
  (if-not ratio
    simplified-expr
    (let [expr-count (-> expr flatten count)
          simplified-expr-count (-> simplified-expr flatten count)]
      (when (<= (/ simplified-expr-count expr-count) ratio)
        simplified-expr))))
        

(defn simplify
  "best heuristics approach to simplify the given expression to a 'simpler' form.
   The optional ratio argument gives control about what is the maximal ratio of
   simplified/original-expression after the invokation of simplify.
   example: (simplify (ex (+ (* a b) (* a c) 5 -5))) => (* a (+ b c))
            (simplify (ex (+ (* a b) (* a c) 5 -5)) :ratio 0.5) => nil"
  [expr & {:keys [ratio simplify-rules] :or {ratio nil
                                             simplify-rules simp/simplify-rules
                                             }}]
  (-> expr
       constr/to-expression
       (simp/simp-expr simplify-rules)
       (ratio-test expr ratio)))

(defn multiply-out
  "fully multiplies out the given expression. Example:
   (multiply-out (ex (+ (* a (+ b c)) (** (+ d e) 2))))
   => (+ (** e 2) (* 2 d e) (** d 2) (* b a) (* c a))"
  [expr]
  (-> expr
      constr/to-expression
      simp/multiply-out))

(defn evaluate-constants
  "evaluates fully determined (sub-) expressions and folds determined factors
   in commutative and associative functions.
   (evaluate-constants (ex (+ (* (- 5 2) a) (* 4 5))))
   => (+ (* 3 a) 20)"
  [expr]
  (-> expr
      constr/to-expression
      simp/evaluate-constants))

(defn to-polynomial-normal-form
  "transforms the given expression to a fully expanded (recursive) polynomial
   representation with v as main variable.
   Example: (to-polynomial-normal-form 'x (ex (* (+ x a 1) (* x (+ 1 a)))))
   :=> (+ (* (+ 1 (* 2 a) (** a 2)) x) (* (+ 1 a) (** x 2)))"
  [v expr]
  (->> expr
       constr/to-expression
       (poly/poly-in v)))

(defn rearrange
  "if the equation contains only one occurrence of v it will be rearranged so
   that v is the only symbol on the lhs of the equation. returns a list of the
   possible rearrangements.
   (rearrange 'x (ex (= (abs x) 3)))
    => ((= x 3) (= x (- 3)))
   (rearrange 'x (ex (= (+ x x) 0))) => nil"
  [v eq]
  (->> eq
       constr/to-expression
       utils/validate-eq
       (solve/rearrange v)))

(defn solve
  "general solving function. Dispatches to different solving strategies based on
   the input equations. Can solve one or more equations according to the
   variables in the symbol vector/set/list.
   In case of only one symbol to solve for symbv can be the symbol itself.
   examples:
   (solve 'x (ex (= 2 (* 4 x)))) ;=> #{1/2}
   (solve '[x y] (ex (= (+ (** x 2) (** y 2)) 1))
                 (ex (= (+ x y) a)))
   ;=>
   #{{y (+ (* a 1/2) (* -1/4 (- (sqrt (+ (* -4.0 (** a 2)) 8))))),
      x (+ (* 1/2 a) (* (- (sqrt (+ (* -4.0 (** a 2)) 8))) 1/4))}
     {y (+ (* a 1/2) (* -1/4 (sqrt (+ (* -4.0 (** a 2)) 8)))),
      x (+ (* 1/2 a) (* (sqrt (+ (* -4.0 (** a 2)) 8)) 1/4))}}"
  ([symbv eq]
     (let [symbv (if (coll? symbv) symbv [symbv])]
       (->> eq
            constr/to-expression
            utils/validate-eq
            (solve/solve (first symbv)))))
  ([symbv eq & reqs]
     (let [symbv (if (coll? symbv) symbv [symbv])]
       (->> (conj reqs eq)
            (map constr/to-expression)
            (map utils/validate-eq)
            (into #{})
            (solve/solve-system symbv)))))


(defn differentiate
  "Differentiates the given expression regarding the symbols in the symbol
   vector symbv
   example:
   (differentiate '[x x] (ex (* (** x 3) (* 3 x))))
   ;=> (* 36 (** x 2))"
  [symbv expr]
  (let [expr (->> expr constr/to-expression)]
    (reduce #(calc/differentiate %2 %1) expr symbv)))

(defmacro compile-expr
  "compiles the given expression to a clojure function which can be called
   according to the bindings vector. The compiled function will not have the
   overhead of walking the expression to excecute it. Compile-expr transforms
   the expression to clojure code which is then evaluated to a function
   example:
   ((compile-expr [x] (ex (+ 1 x))) 2) ;=> 3"
  [bindings expr]
  `(opt/compile-expr* ~(list 'quote bindings) ~expr))

(defn compile-expr*
  "function equivalent of compile-expr. The bindings vector has to be quoted.
   Example: ((compile-expr* '[x] (ex (+ 1 x))) 2) ;=> 3"
  [bindings expr]
  (->> expr
       constr/to-expression
       (opt/compile-expr* bindings)))

(defn optimize
  "transforms the expr to a more optimized form for excecution. The optimized
   form can be compiled with compile-expr. supports optimizations like compile
   time computation, removing unneeded code, common-subexpression detection,
   matrix chain order optimization ...
   example:
   (optimize (ex (+ b (* 5 b) (** y (+ a b)) (** z (+ b a)))))
   ;=> (let [local478813 (+ a b)] (+ (* b 6) (** y local478813)
         (** z local478813)))"
  [expr & {:keys [optimizations]
           :or {optimizations opt/optimizations}}]
  (-> expr
       constr/to-expression
       (opt/optimize optimizations)))

