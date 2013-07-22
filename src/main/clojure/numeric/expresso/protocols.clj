(ns numeric.expresso.protocols
  (:refer-clojure :exclude [==])
  (:use [clojure.test]
        [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is]])
  (:require [numeric.expresso.utils :as utils]
            [clojure.set :as set]
            [clojure.walk :as walk]))

(defprotocol PExpression
  "The abstraction for an expresso Expression"
  (expr-op [expr])
  (expr-args [expr]))

(defprotocol PProps
  "The abstraction to query properties of an Expression or Atom"
  (vars [expr])
  (properties [expr]))

(defprotocol PExprToSexp
  (to-sexp [expr]))

(defprotocol PExprExecFunc
  (exec-func [expr]))

(defprotocol PExprEvaluate
  (evaluate [expr sm]))

(declare value) 
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
  (properties [this] (when-let [m (meta op)] (:properties m))))

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

(defprotocol PMatch
  "The abstraction for matching in a rule based context"
  (match [this that]))

(deftype AtomicExpression [ val]
  java.lang.Object
  (equals [this that]
    (= val (value that)))
  PAtom
  (value [this] val)
  (type-of [this] (type val))
  PProps
  (vars [this] #{})
  (properties [this] nil))

(deftype BasicExtractor [name args rel]
  java.lang.Object
  (toString [this] (str (list* name args)))
  PExpression
  (expr-op [this] name)
  (expr-args [this] args))

(extend-protocol PAtom
  java.lang.Object
  (value [this]  this)
  (type-of [this] (type this)))

(extend-protocol PExpression
  java.lang.Object
  (expr-op [obj] nil)
  clojure.lang.ISeq
  (expr-op [obj]
    (let [f (first obj)]
      (if (and f (or (lvar? f) (symbol? f)))
        f
        nil)))
  (expr-args [obj] (vec (rest obj))))

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

(extend-protocol PProps
  java.lang.Object
  (vars [expr]
    (if-let [op (expr-op expr)]
      (apply set/union (map vars (expr-args expr)))
      (if (symbol? (value expr))
        #{(value expr)}
        #{}))))

(defn expression? [exp]
  (or (not (sequential? exp)) (and (sequential? exp) (symbol? (first exp)))))


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
    (unify-with-expression* u v s))
  AtomicExpression
  (unify-terms [u v s]
    (unify-with-expression* u v s)))

(defn expand-seq-matchers [args]
  (vec (mapcat #(if (and (sequential? %) (= (first %) :numeric.expresso.construct/seq-match))
                  (vec (second %))
                  [%]) args)))

#_(defn walk-expresso-expression* [v f]
  (Expression. (walk-term (f (.-op v)) f)
                 (expand-seq-matchers (mapv #(walk-term (f %) f) (.-args v)))))

(defn walk-needed-terms [v f]
  (if-let [op (expr-op v)]
    (Expression. (if (lvar? op) (walk-term (f op) f) op)
                 (mapv (fn [v] (walk-needed-terms v f)) (expr-args v)))
    (if (or (sequential? v) (lvar? v))
      (walk-term (f v) f)
      v)))

(defn walk-expresso-expression* [v f]
  (walk-needed-terms v f))

(defn substitute-expr [expr smap]
  (if-let [op (expr-op expr)]
    (Expression. op (mapv #(substitute-expr % smap) (expr-args expr)))
    (get smap (value expr) expr)))

(defn symbols-in-expr [expr]
  (if-let [op (expr-op expr)]
    (apply set/union (map symbols-in-expr (expr-args expr)))
    (if (symbol? (value expr)) #{(value expr)} #{})))

(defn lvars-in-expr [expr]
  (walk/postwalk (fn [x] (if (sequential? x) (apply set/union x)
                             (if (lvar? (value x)) #{(value x)} #{}))) expr))

(defn lvars-in-expr [expr]
  (filter lvar? (symbols-in-expr expr)))

(extend-protocol IWalkTerm
  AtomicExpression
  (walk-term [v f] (AtomicExpression. (walk-term (f (value v)) f)))
  Expression
  (walk-term [v f]
    (let [res (walk-expresso-expression* v f)]
      res)))

