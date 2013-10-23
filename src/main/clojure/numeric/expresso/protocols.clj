(ns numeric.expresso.protocols)

;; This namespace defines the basic abstractions used in expresso
;; If you want to read and understand the code, this is the right place
;; to start

;;General
;;Expresso, while using clojure's standart datastructures to represent normal
;;expressions uses protocols for the underlying manipulations.
;;This makes it possible to have custom types as first class expressions where
;;normal ISeqs (with metadate) - expresso's standart expression type - aren't
;;adequate. A good example of that is a type for a PolynomialExpression which
;;would be wasteful and slow to encode as lists.
;;One important thing to keep in mind with the standart expressions based
;;on clojure's built in types is that metadata doesn't count on equality, so
;;Two symbols with the same name are equal even if they have different properties
;;assigned! This is important to keep in mind because it destroys mechanism like
;;memoization. Also be sure to have different names for differet variables in
;;the expression you manipulate with expresso.
;;However, playing well with clojures built in abstractions is *very* important
;;s-expressions aren't per chance the lisp way to represent expressions, so
;;every custom Expression type should also be a proper s-exp in the clojure sense
;;and should implement ISeq.
;;Most implementations of the protocols - if not noted otherwise - can be found
;;in numeric.expresso.impl.pimplementation.clj where also the custon types are
;;defined
;;Most protocols have implementations for ISeq which depend on multimethod about
;;their operator, which makes it easy to extend expresso to new operators
;;*without* having to introduce a new type


;;PExpression
;;The protocol that all expressions implement. expr-op and expr-args are the
;;first and rest of expressions. Constants are encoded as having no operator
;;so the test (if-let [op (expr-op expr-or-constant)] expr constant) can be
;;used to differentiate between expressions and constants.
;;If expr-op returns non-nil the argument is a valid expression for expresso.
;;expr-op should also be called first to check whether the argument is an
;;expression *before* calling expr-args which has no meaning for constants

(defprotocol PExpression
  "The abstraction for an expresso Expression"
  (expr-op [expr])
  (expr-args [expr]))


;;PProps
;;Defines one generic method properties, which returns the set of properties
;;known about expr. Properties are normally stored somewhere in the metadata
;;or in a field in a custom type, but this is implementation detail and hidden
;;behind this protocol.
;;There is no constraint about the element type of the properties set, although
;;expresso just uses keywords for it, like :mzero and :midentity for zero- and
;;identity-matrix properties


(defprotocol PProps
  "The abstraction to query properties of an Expression or Atom"
  (properties [expr]))

;;PVars
;;similar to properties, vars is the protocol to get the set of variables in the
;;expressions. Variables are symbols and lvars. Custom types can also define vars
;;on itself to mark them variables.
;;One important area where vars is called in expresso are the eval-rules, which
;;collect the (parts of) expressions which have no dependency on variables and
;;evaluate them.

(defprotocol PVars
  "generic method to get the set of variables in the expression"
  (vars [expr]))


;;PValue
;;In the presence of custom types it is not always the right idea to have rules
;;about the instances of this types. The value function is used to extract the
;;semantic value out of the argument. Could be for example stripping out a
;;wrapper type. For most standart expresso inputs this is the identity function.
;;An example where this is used is to get the value of a symbol which has the
;;property of being an identity- or a zero-matrix of known shape.

(defprotocol PValue
  "generic way to get the value of the argument."
  (value [atom]))

;;PMatch
;;Expresso is based on a rule based translator which runs on-top of core.logic
;;The rule based translator features semantic matching of rules instead of
;;syntactical matching. So for commutative-operators expressions match iff
;;one permutation of the expression arguments match the pattern.
;;This protocols match method provides the flexibility to extend the matching
;;process to knew types and operators. See also matcher.clj for the
;;implementation and properties.clj where the actual matching core.logic
;;relations are chosen for the operators

(defprotocol PMatch
  "The abstraction for matching in a rule based context"
  (match [this that]))

;;PExprToSexp
;;Does what it's name implies. Although expresso expressions are actual ISeq's
;;they are not actually seqs build on clojures standart types and could be
;;harder to manipulate if one expects an actual list representing an s-expression
;;This protocol is available for situations like these

(defprotocol PExprToSexp
  (to-sexp [expr]))

;;PExprEvaluate
;;Provides the evaluate method, which evaluates the given expression with the
;;values for the variables of the expression given in the symbol map sm.
;;Throws if not all variables are specified. Can be thought of as a better
;;version of eval to evaluate s-expressions for expresso, because it does
;;*not* depend on what symbols resolve to but is data driven from the knowledge
;;that expresso has of the operators.

(defprotocol PExprEvaluate
  (evaluate [expr sm]))

;;PexprExecFunc
;;gets the execution function to evaluate an expression. This is the standart
;;mechanism used in evaluate. See properties.clj where the execution functions
;;are given for the operators of expresso
(defprotocol PExprExecFunc
  (exec-func [expr]))

;;PSubstitute
;;Provides the substitute-expr method which substitutes the keys of the given
;;(symbol) map for its values in the expression. The map can also contain
;;expressions as keys. Normal clojure equality is used to test for substitution.
(defprotocol PSubstitute
  (substitute-expr [expr sm]))

;;PType
;;Provisional protocol for Type inference in expresso. Currently not used for
;;inferece in expresso. There are situations in which knowledge of the type
;;could lead to better optimizations. Currently differentiates between
;;numbers and matrixes (name mismatch - matrix should better be called ndarray
;;here), which can also be differentiates on theis shape

(defprotocol PType
  (type-of [this])
  (set-type [this type]))

;;PShape
;;The shape and set-shape methods are used to query and set the shape of the
;;given expressions. Expresso infers the shape of an expression from its
;;operator and the shapes of its arguments.
;;The shape can be an actual shape like core.matrix/shape gives you, or it can
;;be a logic variable or an expression containig logic variables.
;;This plus the constraints facility allow expresso to correctly infer the shape
;;even if the shape of one part is undetermined. With the added constraint for
;;the value of the undetermined shape, the other shapes in the expression can
;;be inferred. See add-constraint and construct.clj

(defprotocol PShape
  (shape [this])
  (set-shape [this shape]))

;;PInferShape
;;Like PShape but its method are for the inferred shape and not for the shape
;;resulting from the arguments of the expression. In the presence of implicit
;;broadcasting and simplification these two shapes can clash. The inferred shape
;;has priority above the shape and will be returned from calls to shape if
;;available.
;;An example where inferred shape is needed is this
;; (ex (+ a b (- a))) is simplified to b.
;;The shape of the expression is not affected by the simplification, but b now
;;has to have the inferred shape set to the shape of (ex (+ a b (- a))) because
;;b could be implicit broadcasted to the shape of a. So the correct shape of
;;b is not the shape of b like it would be without an inferred shape but it is
;;the longest shape of a and b, which is the shape of (ex (+ a b (- a)))

(defprotocol PInferShape
  (inferred-shape [this])
  (set-inferred-shape [this shape]))

;;Not all manipulations of expresso are based on the rule based translator.
;;Where it makes sense to stay away from a rule based approach expresso does so.
;;In case of rearranging and differentiating the manipulatios are determined
;;by the operators of the expressions alone and an open rule set would not get
;;any benefits.

;;PRearrange
;;The rearrange-step function is used to make a single step when rearraging the
;;equation consisting of lhs and rhs to x, which is in the pos part of the
;;current top level

(defprotocol PRearrange
  (rearrange-step [lhs pos rhs]))

;;PDifferentiate
;;the differentiate-expr function does symbolic differentiation of the expression
;;in regard to the specified variable. No simplifications on the output are done.
(defprotocol PDifferentiate
  (differentiate-expr [expr var]))

;;PConstraints
;;Expresso, because it is built on-top of core.logic has powerful mechanism to
;;declaratively handle constraints about expressions. Currently Constraits are
;;mostly used for shape inference, but they are more general than that.
;;an expression can have a set of constraints, which can be checked - see the
;;check-constraints method in pimplementation.clj - ad which result can alter
;;the expression. A constraint is a vector of [relation args*]. The constraints
;;are stored as a set in an expression and the constraints on the arguments are
;;also constraints on the parent expression.
(defprotocol PConstraints
  (constraints [expr])
  (add-constraint [expr constraint]))

;;PEmitCode
;;This protocol is used by the optimizer of expresso. The function emit-code
;;emits (fast) clojure code needed when compiling an expression to a non-over-
;;head clojure function. In the normal case this is (exec-fun args)
;;See also emit-func

(defprotocol PEmitCode
  (emit-code [expr]))

;;PTransformExpression
;;Protocol for a transformation of the expression according the the specified
;;rule vector, to the standart form encoded by the rule. Applies the rules
;;fully recursive bottom up. See rules.clj for the details
(defprotocol PTransformExpression
  (transform-expr [expr rules]))

;;To be able to compile patterns, we transform them to constraints (what
;;they conceptually are
(defprotocol PToConstraint
  (to-constraints [pat]))


(defmulti emit-constraints (fn [a b] a))

;;Multimethod used by the default implementation for ISeq of emit-code to emit
;;the function for the operator. defaults to the :emit-func key in the operator
(defmulti emit-func first)
(defmethod emit-func :default [expr] (:emit-func (meta (first expr))))

;;Multimethod for the actual function used in the default implementation of
;;rearrange step for ISeq
(defmulti rearrange-step-function first)

;;Multimethod for the actual function used in the default implementtaion of
;;differentiate for ISeq
(defmulti diff-function (comp first first))

