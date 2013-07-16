(ns numeric.expresso.protocols
  (:refer-clojure :exclude [==])
  (:use [clojure.test])
  (:require [numeric.expresso.utils :as utils]))

(defprotocol PExpression
  "The abstraction for an expresso Expression"
  (expr-op [expr])
  (expr-args [expr]))

(defprotocol PProps
  "The abstraction to query properties of an Expression or Atom"
  (contains-var? [expr var])
  (properties [expr]))

(defprotocol PExprToSexp
  (to-sexp [expr]))

(defprotocol PExprExecFunc
  (exec-func [expr]))

(defprotocol PExprEvaluate
  (evaluate [expr sm]))

(deftype Expression [op args]
  PExpression
  (expr-op [this] op)
  (expr-args [this] args))

(deftype PolynomialExpression [v coeffs]
  PExpression
  (expr-op [this] `+)
  (expr-args [this] coeffs)
  PExprEvaluate
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
  
(defprotocol PAtom
  "The abstraction for an Atom in a Expression. Can be ac actual
   constant or a variable"
  (value [atom])
  (type-of [atom]))


(deftype AtomicExpression [^double value]
  PAtom
  (value [this] value)
  (type-of [this] (type value))
  PProps
  (contains-var? [this var] false)
  (properties [this] nil))

(extend-protocol PAtom
  java.lang.Object
  (value [this]  this)
  (type-of [this] (type this)))

(extend-protocol PExpression
  java.lang.Object
  (expr-op [obj] nil))

(extend-protocol PExprToSexp
  java.lang.Object
  (to-sexp [expr]
    (if-let [op (expr-op expr)]
      (list* op (map to-sexp (expr-args expr)))
      (value expr))))

(extend-protocol PExprExecFunc
  java.lang.Object
  (exec-func [expr]
    (if-let [op (expr-op expr)]
      (resolve op)
      (throw (Exception. (str "no excecution function found for " expr))))))

(extend-protocol PExprEvaluate
  java.lang.Object
  (evaluate [expr sm]
    (if-let [op (expr-op expr)]
      (apply (exec-func expr) (map #(evaluate % sm) (expr-args expr)))
      (let [val (value expr)]
        (if (symbol? val)
          (if-let [evaled (val sm)]
            evaled
            (throw (Exception. (str "No value specified for symbol " val))))
          val)))))