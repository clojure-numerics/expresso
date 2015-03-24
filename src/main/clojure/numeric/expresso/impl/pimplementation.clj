 (ns numeric.expresso.impl.pimplementation
  (:refer-clojure :exclude [== record?])
  (:use [clojure.test]
        [clojure.core.logic.protocols]
        [numeric.expresso.protocols]
        [clojure.core.logic :exclude [is]])
  (:require 
            [clojure.set :as set]
            [numeric.expresso.types :as types]
            [clojure.core.matrix :as mat]
            [clojure.walk :as walk]))

;;Constraint checking code
;;The constraints added to expressions encode constraints mainly on lvars in meta
;;data. Because metadata is normally not touched by core.logic it has to be
;;brought in scope and then all constraints are run.


(defn all*
  "function version of all macro in logic.clj
   Like fresh but does does not create logic variables."
  ([] clojure.core.logic/s#)
  ([goals] (fn [a] (reduce (fn [l r] (bind l r)) a goals))))


(defn to-relations
  "Maps the constraint in the form [rel args*] to the real clojure relation"
  [constraint]
  (let [[rel & args] constraint]
     (apply rel args)))

;;core.logic lvars can be in the type and shape metadata. To make it visible
;;transform the expression to {:type (type-of expresion)
;; :shape (shape expression) :value expression
(defn with-meta-informations [value]
  (let [type (type-of value)
        shape (shape value)
        value (if-let [op (expr-op value)]
                (with-meta
                  (list* op
                         (map with-meta-informations (expr-args value)))
                  (meta value))
                (if (sequential? value)
                  (with-meta (mapv with-meta-informations value)
                    (meta value))
                  value))]
    {:type type :shape shape :value value}))

;;After the query is run against the transformed expression, it has to be
;;retransformed afterwards back to its original shape 
(defn restore-expression [wmi]
  (let [type (:type wmi)
        shape (:shape wmi)
        value (:value wmi)
        value (if-let [op (expr-op value)]
                (with-meta
                  (list* op (map restore-expression (expr-args value)))
                  (meta value))
                (if (sequential? value)
                  (with-meta (mapv restore-expression value) (meta value))
                    value))]
    (-> value (set-shape shape))))

;;Now comes the constrait checking part.
;;1. make the constraints to relations
;;2. transform-the expression
;; 3. run the query - the :reify-vars kv takes care that fresh lvars
;;    stay fresh after the run block
;; 4. If the result is not unambiguous the transfomred expression is
;;    retransformed
;; 5. If the constraint check failed throw exception

(defn check-constraints
  "checks the constraints on value.
   throws exception if they don't hold"
  [value]
  (let [cs (map to-relations (constraints value))
        res (-run {:occurs-check true :n 2 :reify-vars (fn [v s] s)} [q]
                  (fresh []
                         (all* cs)
                         (== q (with-meta-informations value))))]
    (if (not= res '())
      (if (= 1 (count res))
        (restore-expression (first res))
        value)
      (throw (Exception. "constraint check failed")))))


;;The Expression deftype could be a replacement for normal clojure lists as
;;expression datatype. It demonstrates how a custom datatype can play nicely
;;with clojures abstractions and also with core.logic
;;many protocol implemetation will have the same code for ISeq and Expression
;;implements sequential, counted and ISeq mimicking the list (op args*)
;;in the ISeq implementation. Seqable returns itself because it iimplements
;;ISeq itself. Implementating clojures abstractions for custom expresso types
;;could be made simpler by a bit macro magic in the future

(deftype Expression [op args]
  clojure.lang.Sequential
  clojure.lang.Counted
  (count [this] (+ 1 (count args)))
  clojure.lang.ISeq
  (next [this] (next (list* op (map value args))))
  (first [this] op)
  (more [this] (.more (list* op (map value args))))
  (cons [this obj] (cons obj (list* op args)))
  (equiv [this that] (= (list* op (map value args)) that))
  (empty [this] false)
  clojure.lang.Seqable
  (seq [this] this);(seq (list* op (map value args))))
  java.lang.Object
  (hashCode [a]
    (.hashCode args))
  (toString [expr]
    (str (list* op args)))
  (equals [this that]
    (and (= op (expr-op that))
         (= args (expr-args that))))
  PExpression
  (expr-op [this] op)
  (expr-args [this] args)
  PProps
  ;;stub properties in metadata of operator is not the best idea
  (properties [this] (when-let [m (meta op)] (:properties m))))


;;PolynomialExpression
;;A polynomialExpression is represented as the main-variable v and the
;;coeff clojure vector. x is the represented as
;;PolynomialExpression 'x [0 1]
;;Multivariate polynomial are represented in a recursive way according to a
;;order on the variables. See polynomial.clj for details

(deftype PolynomialExpression [v coeffs]
  Object
  (equals [this other]
    (and (instance? PolynomialExpression other)
         (= v (.-v ^PolynomialExpression other))
         (= coeffs (.-coeffs ^PolynomialExpression other))))
  (toString [this]
    (str v coeffs))
  clojure.lang.Seqable
  (seq [this] this)
  clojure.lang.Sequential
  clojure.lang.ISeq
  (next [this] (next (to-sexp this)))
  (first [this] (first (to-sexp this)))
  (more [this] (.more (to-sexp this)))
  (cons [this obj] (cons obj (to-sexp this)))
  (equiv [this that] (or (.equals this that)
                         (= (to-sexp this) that)))
  (empty [this] false)
  PExpression
  (expr-op [this] `+)
  (expr-args [this] (vec (rest (to-sexp this))))
  PExprEvaluate
  ;;faster evaluate than evaluating the to-sexp representation
  (evaluate [poly sm]
    (if-let [vval (v sm)]
      (let [c (count coeffs)]
        (loop [^double res (first coeffs) i 1]
          (if (= i c) res
              (let [nres (+ res (* (nth coeffs i)
                                   (Math/pow vval i)))]
                (recur nres (inc i)))))))))

(defn make-poly [v coeff]
  (PolynomialExpression. v coeff))

;;BasicExtractor
;;Extractors are used in the rule based translator
;;They have their own implementation of match which lets them
;;bring their own matching semantics
;;for example (is? some-predicate ?x) can mean match the expression
;;if the predicate is true on it and unify it with ?x then

(deftype BasicExtractor [name args rel]
  java.lang.Object
  (toString [this] (str (list* name args)))
  PExpression
  (expr-op [this] name)
  (expr-args [this] args))

;;LetExpression
;;A custom type for a let expression. Is used for the optimizer to remove
;;common subexpresions from the expression tree. Mimicks the normal clojure
;;let expression in its ISeq implementation.
(deftype LetExpression [bindings code]
  java.lang.Object
  (toString [this] (str `(let ~bindings ~@code)))
  PExpression
  (expr-op [this] 'let)
  (expr-args [this] code)
  clojure.lang.Sequential
  clojure.lang.Counted
  (count [this] (+ 1 (count code)))
  clojure.lang.ISeq
  (next [this] (next `(let ~bindings ~@code)))
  (first [this] 'let)
  (more [this] (.more `(let ~bindings ~@code)))
  (cons [this obj] (cons obj `(let ~bindings ~@code)))
  (equiv [this that] (= `(let ~bindings ~@code) that))
  (empty [this] false)
  clojure.lang.Seqable
  (seq [this] this)
  PExprEvaluate
  ;;evaluate the first binding and merge the kv pair info the sm and then
  ;;evaluate the next. evaluate the body afterwards
  (evaluate [this sm]
    (let [nsm (->> bindings (partition 2)
                   (map (fn [[a b]] [a (evaluate b sm)])) (into {}))
          nnsm (merge sm nsm)]
      (last (map #(evaluate % nnsm) code)))))

;;The implementations for PValue. Mostly identity for know only matrix symbols
;;with mzero and midentity property evaluate to a real value at the moment.

(extend-protocol PValue
  nil
  (value [this] nil)
  clojure.lang.Symbol
  (value [this]
    (let [props (properties this)]
      (if (or (contains? props :midentity) (contains? props :mzero))
        (let [shape (shape this)]
          (if (not (or (lvar? shape) (expr-op shape)))
            (cond
             (props :midentity) (if (= [] shape) 1 (mat/identity-matrix
                                                    (first shape)))
             (props :mzero) (mat/new-array shape))
            this))
        this)))
  java.lang.Object
  (value [this]  this))

;;The implementations for PExpressions. Defaults to saying 'I'm a constant by
;;returning nil for expr-op. ISeq checks if it is a real expresso expression
;;by checking the mandatory part of the metadata added to the first symbol
;;which is :expression true
(extend-protocol PExpression
  nil
  (expr-op [obj] nil)
  java.lang.Object
  (expr-op [obj] nil)
  clojure.lang.ISeq
  (expr-op [obj]
    (let [f (first obj)]
      (cond
       (and f (symbol? f) (contains? (meta f) :expression)) f
       (and f (lvar? f)) f
        :else nil)))
  (expr-args [obj] (vec (rest obj))))

;;implementations for to-sexp for polynomial and default.
;;The polynomial implementation does some simplifications on the s-expressions
;;so that only the nonzero coefficients are shown in the sexp and also not
;;(** x 0) and (** x 1)
(extend-protocol PExprToSexp
  PolynomialExpression
  (to-sexp [poly]
    (let [v (.-v poly) coeffs (.-coeffs poly)
          r (->> (map #(let [s (to-sexp %1)
                             exp (if (clojure.core/== 0 %2)
                                   v
                                   (list '** v (inc %2)))]
                         (if (not (and (number? s) (clojure.core/== 0 s)))
                           (if (and (number? s) (clojure.core/== 1 s))
                             exp
                             (list '* s exp))))
                      (rest coeffs) (range))
                 (filter identity))]
      (if (and (number? (nth coeffs 0)) (clojure.core/== (nth coeffs 0) 0))
        (list* '+ r)
        (list* '+ (to-sexp (nth coeffs 0)) r))))
    java.lang.Object
  (to-sexp [expr]
    (if-let [op (expr-op expr)]
      (list* op (map to-sexp (expr-args expr)))
      (value expr))))

;;The execution function used when evaluating is currently stortd as :exec-func
;;in the metadata of the operator. If not it is tried to sesolve it
(extend-protocol PExprExecFunc
  java.lang.Object
  (exec-func [expr]
    (if-let [op (expr-op expr)]
      (or (and (meta op) (:exec-func (meta op))) (resolve op))
      (throw (Exception. (str "no excecution function found for " expr))))))

;;The default implementation for Evaluate differentiates between constants and
;;expressions. from expressions, the eval-func is obtained and invoked on the
;;evaluation of all its arguments.
;;If it is a constant, its value is obtained and returned it if is not a
;;symbol or lvar
(extend-protocol PExprEvaluate
  nil
  (evaluate [expr sm] nil)
  java.lang.Object
  (evaluate [expr sm]
    (if-let [op (expr-op (value expr))]
      (if-let [eval-func (:eval-func (meta op))]
        (eval-func expr sm)
        (apply (exec-func expr) (map #(evaluate (value %) sm) (expr-args expr))))
      (let [val (value expr)]
        (if (or (symbol? val) (lvar? val))
          (if-let [evaled (val sm)]
            evaled
            (throw (Exception. (str "No value specified for symbol " val))))
          val)))))

;;PVars implementation
;;the symbol in the operator position is ignored for vars. Vars also checks
;;the 'Value' of the expression if it is a symbol so that m-zero matrizes
;;with determined shapes are not mistaken as variables

(extend-protocol PVars
  PolynomialExpression
  (vars [expr] (apply set/union
                      (concat [#{(.-v expr)}] (map vars (.-coeffs expr)))))
  nil
  (vars [expr] #{})
  java.lang.Object
  (vars [expr]
    (if-let [op (and (seq? expr) (first expr))]
      (apply set/union (map vars (rest expr)))
      (if (or (symbol? (value expr)) (lvar? (value expr)))
        #{(value expr)}
        #{}))))


;;the core.logic extension to the custom datatypes
;;s is the substitution map. basically unify the expr-op and the expr-args
;;unsing the protocol function also enables matching Expression type and ISeq
;;representation. Unification is also done on the logical value.
;;the switch between u and v in the last line *is* neccesary, because
;;core.logic can end up in a stackoverflow if not.

(defn unify-with-expression* [u v s]
  (let [uop (expr-op u) vop (expr-op v)]
    (if uop
      (if vop
        (if-let [s (unify s uop vop)]
          (unify s (expr-args u) (expr-args v)))
        (unify s (value v) u))
      (unify s (value u) (value v)))))


(extend-protocol IUnifyTerms
  Expression
  (unify-terms [u v s]
    (unify-with-expression* u v s)))

;;An advantage one has with a custom datatype is having full control about
;;core.logic behaviour, so the walkTerm expression can splice in the sequential
;;matchers while walking the term. See rules.clj and matcher.clj
;;for more about seq-matchers

(defn expand-seq-matchers[args]
  (vec (mapcat #(if (and (sequential? %)
                         (= (first %) :numeric.expresso.construct/seq-match))
                  (vec (second %))
                  [%]) args)))

(defn walk-expresso-expression* [^Expression v f]
  (Expression. (walk-term (f (.-op v)) f)
                 (expand-seq-matchers (mapv #(walk-term (f %) f) (.-args v)))))


(extend-protocol IWalkTerm
  Expression
  (walk-term [v f]
    (walk-expresso-expression* v f)))

;;substituting an expression is just a postwalk-replace in case of ISeq
;;and a custom replacement in case of Expression

(defn substitute-expr* [expr repl]
  (if-let [sub (get repl expr)]
    sub
    (if-let [op (expr-op expr)]
      (Expression. (get repl op op)
                   (mapv #(substitute-expr* % repl) (expr-args expr)))
      (get repl (value expr) expr))))

(extend-protocol PSubstitute
  clojure.lang.Symbol
  (substitute-expr [this repl]
    (repl this this))
  clojure.lang.ISeq
  (substitute-expr [this repl]
    (let [res (walk/postwalk-replace repl this)]
      res))
  Expression
  (substitute-expr [this repl]
    (substitute-expr* this repl)))

(defn check-type [this type to-check]
  (if (= type to-check) this
      (throw (Exception. (str "Invalid Type " type "for "
                              this "excpected " to-check)))))

;;poc implementation of type protocol.

(extend-protocol PType
  Integer
  (type-of [this] :numeric.expresso.types/integer)
  (set-type [this type] (check-type this type :numeric.expresso.types/integer))
  Long
  (type-of [this] :numeric.expresso.types/long)
  (set-type [this type] (check-type this type :numeric.expresso.types/long))
  Double
  (type-of [this] :numeric.expresso.types/double)
  (set-type [this type] (check-type this type :numeric.expresso.types/double))
  java.lang.Number
  (type-of [this] :numeric.expresso.types/number)
  (set-type [this type] (check-type this type :numeric.expresso.types/number))
  Object
  (type-of [this]
    (if-let [type (and (meta this) (:type (meta this)))]
      type
      (if (mat/array? this)
        :numeric.expresso.types/matrix
        :Unknown)))
  (set-type [this type]
    (cond
     (mat/array? this) (check-type this type :numeric.expresso.types/matrix)
     (lvar? (:type (meta this)))
     (add-constraint
      (with-meta this (assoc (meta this) :type type :shape
                             (if (= type :numeric.expresso.types/matrix)
                               [(lvar 'lshape) (lvar 'rshape)] [])))
      [== (:type (meta this)) type])
     :else (if (isa? (:type (meta this)) type)
             this
             (throw (Exception. (str "invalid type " type " for "
                                     (:type (meta this)) " of " this)))))))


(defn all-execable [x]
  (if-let [op (expr-op x)]
    (and (or (exec-func x) (:eval-func (meta op)))
         (every? all-execable (expr-args x)))
    true))

(defn no-symbol [x]
  (and (empty? (vars x))
       (all-execable x)))

(defn eval-if-determined [expr]
  (if (expr-op expr)
    (if (no-symbol expr)
      (evaluate expr {})
      expr)
    expr))

;;The implementation for shape first checks for an inferred shape.
;;If not, it checks if its shape is an expression and evals it if it can
;;be evaluated.  otherwise it returns the expression
(extend-protocol PShape
  nil
  (shape [this] [])
  (set-shape [this shape]
    (if (= [] shape) this (throw (Exception.
                                  (str "invalid shape " shape "for nil")))))
  java.lang.Number
  (shape [this] [])
  (set-shape [this shape]
    (if (= [] shape) this (throw (Exception.
                                  (str "invalid shape " shape "for a number")))))
  clojure.lang.ISeq
  (shape [this]
    (or (inferred-shape this)
        (eval-if-determined (:shape (meta this)))))
  (set-shape [this shape]
    (with-meta this (assoc (meta this) :shape shape)))
  java.lang.Object
  (shape [this]
    (or (inferred-shape  this)
        (eval-if-determined (get (meta this) :shape
                                  (mat/shape this)))))
  (set-shape [this shape]
    (with-meta this (assoc (meta this) :shape shape))))
      
(extend-protocol PInferShape
  nil
  (inferred-shape [this] (shape this))
  java.lang.Number
  (inferred-shape [this] (shape this))
  (set-inferred-shape [this shape] (set-shape this shape))
  java.lang.Object
  (inferred-shape [this] (eval-if-determined (get (meta this) :inferred-shape)))
  (set-inferred-shape [this shape]
    (with-meta this (assoc (meta this) :inferred-shape shape))))

;;in the default case properites are in the properties key in the metadata
;;for numbers the properties can be :positive, :zero, or :negative
(extend-protocol PProps
  java.lang.Object
  (properties [this]
    (when-let [m (meta this)]
      (:properties m)))
  java.lang.Number
  (properties [this]
    (cond
     (> this 0) #{:positive}
     (= this 0) #{:zero}
     :else      #{:negative})))

(defn add-metadata [s m]
  (with-meta s (merge (meta s) m)))

;;the constraint is added to the constraints meta key
(defn add-constraint-normal [value constraint]
  (let [res (if-let [c (:constraints (meta value))]
              (add-metadata value {:constraints (set/union c #{constraint})})
              (add-metadata value {:constraints #{constraint}}))]
    res))

;;Constraints are currently not supported on BasicExtractors and
;;PolynomialExpressions
(extend-protocol PConstraints
  java.lang.Number
  (constraints [this] #{})
  (add-constraint [this constraint] this)
  java.lang.Object
  (constraints [this]
    (get (meta this) :constraints #{}))
  (add-constraint [this constraint]
    (add-constraint-normal this constraint))
  BasicExtractor
  (constraints [this] #{})
  (add-constraint [this constraint] this)
  PolynomialExpression
  (constraints [this] #{})
  (add-constraint [this constraint] this)
  ;;Constraints on expressions cascade upwards so they include all the
  ;;constraints of their arguments
  clojure.lang.ISeq
  (add-constraint [this constraint]
   (add-constraint-normal this constraint))
  (constraints [this]
    (let [cs (get (meta this) :constraints #{})]
      (if (not (empty? this))
        (apply (partial set/union cs) (map constraints this)))))
  Expression
  (add-constraint [this constraint]
    (Expression. (add-constraint-normal (expr-op this) constraint)
                 (expr-args this)))
  (constraints [this]
    (let [cs (get (meta this) :constraints #{})]
      (apply (partial set/union (set/union cs (constraints (expr-op this))))
             (map constraints (expr-args this))))))


;;Rearrange ad Differentiate dispatch to their appropriate dispatch multimethod
;;in case of Expression and ISeq
(extend-protocol PRearrange
  Expression
  (rearrange-step [lhs pos rhs]
    (let [op (expr-op lhs)]
      (rearrange-step-function [op (expr-args lhs) pos rhs])))
  clojure.lang.ISeq
  (rearrange-step [lhs pos rhs]
    (if-let [op (expr-op lhs)]
      (rearrange-step-function [op (vec (rest lhs)) pos rhs]))))

(extend-protocol PDifferentiate
  Number
  (differentiate-expr [this v] 0)
  clojure.lang.Symbol
  (differentiate-expr [this v]
    (if (= v this) 1 0))
  clojure.lang.ISeq
  (differentiate-expr [this v]
    (if-let [op (expr-op this)]
      (diff-function [this v]))))

;;the normal emit-code implementation emits just the (exec-func ops*) clojure
;;list. the let expression similary emits its normal clojure code
(extend-protocol PEmitCode
  java.lang.Object
  (emit-code [this]
    (if-let [op (expr-op this)]
      (if-let [ef (emit-func this)]
        (ef this)
        (list* (exec-func this) (map emit-code (expr-args this))))
      this))
  LetExpression
  (emit-code [this]
    `(let ~(.-bindings this) ~@(map emit-code (.-code this)))))

;;quick fix to be able to handle seqs as values in core.logic
;;without this sets make core.logic go into an infinite loop.
(extend-protocol IWalkTerm 
  clojure.lang.IPersistentSet 
  (walk-term [v f] (with-meta (set (walk-term (seq v) f)) (meta v))))



;;TODO protocol evaluable
