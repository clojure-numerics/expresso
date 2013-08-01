(ns numeric.expresso.construct
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [numeric.expresso.properties]
        [clojure.test])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [clojure.set :as set]
            [numeric.expresso.protocols :as protocols]
            [clojure.core.logic.unifier :as u]
            [numeric.expresso.utils :as utils]))
(defmulti create-special-expression first)
(defmethod create-special-expression :default [_] nil)


(defn add-metadata [s m]
  (with-meta s (merge (meta s) m)))

(defn expr-properties [s-exp]
  (:properties (meta (first s-exp))))

(defn expr-propertieso [s-exp q]
  (project [s-exp]
           (== q (expr-properties s-exp))))


(defn seq-matcher [data]
  [::seq-match data])

(defn matcher-args [seq-matcher]
  (if (and (sequential? seq-matcher) (= (first seq-matcher) ::seq-match))
    (second seq-matcher)
    [seq-matcher]))

(defn zip-sm
  [sm & colls]
  (apply (partial map (fn [& a] a) (matcher-args sm)) colls))

(defn map-sm [func & sm]
  (->> sm (map matcher-args) (apply (partial map func)) seq-matcher))

(defn first-sm [sm] (first (matcher-args sm)))
(defn rest-sm [sm] (seq-matcher (rest (matcher-args sm))))
(defn last-sm [sm] (last (matcher-args sm)))

(defn count-sm [sm] (count (vec (matcher-args sm))))
(defn split-in-pos-sm [sm pos]
  (let [args (vec (matcher-args sm))]
    [(seq-matcher (subvec args 0 pos))
     (nth args pos)
     (seq-matcher (subvec args (+ pos 1) (count args)))]))

(defn extract [c]
  (mapcat #(if (and (coll? %) (= (first %) ::seq-match)) (second %) [%]) c))


(defn splice-in-seq-matchers [expr]
  (walk/postwalk (fn [expr] (if (coll? expr) (extract expr) expr)) expr))


(defn create-expression [symbol args]
  (numeric.expresso.protocols.Expression. symbol (vec args)))

(defn create-extractor [symb args]
  (when-let [rel (extractor-rel symb)]
    (numeric.expresso.protocols.BasicExtractor. symb args rel)))

(defn ce
  "constructs an expression from the symbol with the supplied args"
  [symb & args]
  (or (create-special-expression [symb args])
      (create-extractor symb args)
      (list* (with-meta symb (add-information symb)) args)))

(defn matrix-symb
  ([s shape] (matrix-symb s shape #{}))
  ([s shape additional-props]
     (add-metadata s {:type :matrix
                      :properties (set additional-props)
                      :shape shape })))

(defn zero-matrix
  ([s] (zero-matrix s #{}))
  ([s additional-props]
     (matrix-symb (symbol (str "zeromat" (apply str (interpose "-" s))))
                  s
                  (set/union additional-props #{:mzero}))))

(defn identity-matrix
  ([s] (identity-matrix s #{}))
  ([s additional-props]
     (matrix-symb (symbol (str "identitymat" (apply str (interpose "-" [s s]))))
                  [s s]
                  (set/union additional-props #{:midentity}))))
     

(def °)

(defn expo 
  "Creates an expression with the given operator and parameters"
  ([op params exp]
    (conso op params exp)))

(derive 'e/ca+ 'e/ca-op)
(derive 'e/ca* 'e/ca-op)
(derive 'clojure.core/+ 'e/ca+)
(derive 'clojure.core/* 'e/ca*)
(derive 'clojure.core/- 'e/-)
(derive 'clojure.core// 'e/div)
(derive 'clojure.core.matrix.operators/+ 'e/ca-op)
(derive 'clojure.core.matrix/add 'e/ca-op)
(derive `° 'e/ao-op)


(defn var-to-symbol [v]
  (let [s (str v)
        erg (-> (.substring s 2 (.length s)) symbol)]
    erg))


(defn replace-with-expresso-sexp [s s-exp]
  (if (and (coll? s-exp) (s (first s-exp)))
    (let [f (first s-exp)
          symb (if-let [r (resolve f)] (var-to-symbol r) f)]
      (list* `ce (list 'quote symb) (rest s-exp)))
    s-exp))

(defn construct-with* [s & code]
  (let [s-set (set s)]
    `(do 
       ~@(clojure.walk/postwalk #(replace-with-expresso-sexp s-set %) code))))

(defmacro construct-with [s & code]
  (apply (partial construct-with* s) code))

(defmacro with-expresso [s & code]
  (let [s-set (set s)]
    `(do 
       ~@(clojure.walk/postwalk #(replace-with-expresso-sexp s-set %) code))))

(defn add-meta [symb args]
  (list* (with-meta symb {:properties (props symb)}) args))

(defn create-expression-with-values [s expr]
  (if (and (sequential? expr) (symbol? (first expr)) (not= 'quote (first expr)))
    (if (= (first expr) 'clojure.core/unquote)
      (second expr)
      (let [f (first expr)
            symb (if-let [r (resolve f)] (var-to-symbol r) f)]
        (list* `ce  (list 'quote symb) (rest expr))))
    expr))

(defn ex'* [& expr]
  (let [[s expr]
        (if (= (count expr) 1)
          [#{} (first expr)]
          [(into #{} (first expr)) (second expr)])
        expr (walk/postwalk #(if (s %) (list 'quote %) %) expr)]
    (walk/prewalk #(create-expression-with-values s %) expr)))

(defmacro ex'
  [& expr]
  (let [[s expr]
        (if (= (count expr) 1)
          [#{} (first expr)]
          [(into #{} (first expr)) (second expr)])
        expr (walk/postwalk #(if (s %) (list 'quote %) %) expr)]
    (walk/prewalk #(create-expression-with-values s %) expr)))

(defn resolve-op [f]
  (if-let [r (resolve f)] (var-to-symbol r) f))

(defn exnright [expr]
  (if (and (sequential? expr) (symbol? (first expr)))
    (if (= 'clojure.core/unquote (first expr))
      (second expr)
      (list* `ce (list 'quote (resolve-op (first expr)))
            (map exnright (rest expr))))
    (list 'quote expr)))

(defn construct-ex [expr]
  (exnright expr))

(defmacro ex [expr]
  (exnright expr))

(defn ex* [expr]
  (exnright expr))

(defn exn*right [expr]
  (if (and (sequential? expr) (symbol? (first expr)))
    (if (= 'clojure.core/unquote (first expr))
      (second expr)
      (apply (partial ce (resolve-op (first expr)))
             (map exn*right (rest expr))))
    (list 'quote expr)))

(defn let-expr [bindings code]
  (numeric.expresso.protocols.LetExpression. bindings code))


(defn to-expression [expr]
  (if-let [op (protocols/expr-op expr)]
    expr
    (walk/postwalk #(if (and (seq? %) (symbol? (first %)))
                      (apply (partial ce (first %))  (rest %))
                      %) expr)))