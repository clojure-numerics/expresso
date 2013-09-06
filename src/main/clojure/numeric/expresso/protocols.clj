(ns numeric.expresso.protocols
  (:refer-clojure :exclude [==])
  (:use [clojure.test]
        [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is]])
  (:require 
            [clojure.set :as set]
            [numeric.expresso.types :as types]
            [clojure.core.matrix :as mat]
            [clojure.walk :as walk]))
(defprotocol PExpression
  "The abstraction for an expresso Expression"
  (expr-op [expr])
  (expr-args [expr]))

(defprotocol PProps
  "The abstraction to query properties of an Expression or Atom"
  (properties [expr]))

(defprotocol PVars
  "generic method to get the set of variables in the expression"
  (vars [expr]))


(defprotocol PAtom
  "The abstraction for an Atom in a Expression. Can be ac actual
   constant or a variable"
  (value [atom]))

(defprotocol PMatch
  "The abstraction for matching in a rule based context"
  (match [this that]))

(defprotocol PExprToSexp
  (to-sexp [expr]))

(defprotocol PExprExecFunc
  (exec-func [expr]))

(defprotocol PExprEvaluate
  (evaluate [expr sm]))

(defprotocol PSubstitute
  (substitute-expr [expr sm]))

(defprotocol PType
  (type-of [this])
  (set-type [this type]))

(defprotocol PShape
  (shape [this])
  (set-shape [this shape]))

(defprotocol PRearrange
  (rearrange-step [lhs pos rhs]))

(defprotocol PDifferentiate
  (differentiate-expr [this var]))

(defprotocol PConstraints
  (constraints [this])
  (add-constraint [this constraint]))

(defprotocol PEmitCode
  (emit-code [this]))

(defmulti emit-func first)
(defmethod emit-func :default [_] (:emit-func (meta (first _))))

(defmulti rearrange-step-function first)

(defmulti diff-function (comp first first))

