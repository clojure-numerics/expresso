(ns numeric.expresso.construct
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [clojure.test])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [clojure.core.logic.unifier :as u]
            [numeric.expresso.utils :as utils]))


(defn properties [s-exp]
  (:properties (meta (first s-exp))))

(defn propertieso [s-exp q]
  (project [s-exp]
           (== q (properties s-exp))))

(defmulti props identity)
(defmethod props :default [_] nil)
(defmethod props 'clojure.core/* [_] [:associative :commutative :n-ary])
(defmethod props 'clojure.core/+ [_] [:associative :commutative :n-ary])
(defmethod props 'clojure.core/- [_] [:n-ary [:inverse-of 'clojure.core/+]])
(defmethod props 'clojure.core// [_] [:n-ary [:inverse-of 'clojure.core/*]])

(defn seq-matcher [data]
  [::seq-match data])

(defn matcher-args [seq-matcher]
  (second seq-matcher))

(defn extract [c]
  (mapcat #(if (and (coll? %) (= (first %) ::seq-match)) (second %) [%]) c))


(defn splice-in-seq-matchers [expr]
  (walk/postwalk (fn [expr] (if (coll? expr) (extract expr) expr)) expr))

(defn ce [symb & args]
  (list* (with-meta symb {:properties (props symb)}) args))

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

(defmacro with-expresso [s & code]
  (let [s-set (set s)]
    `(do 
       ~@(clojure.walk/postwalk #(replace-with-expresso-sexp s-set %) code))))

(defn add-meta [symb args]
  (list* (with-meta symb {:properties (props symb)}) args))

(defn create-expression [v]
  (cond
   (and (sequential? v) (symbol? (first v)))
   (if (= (first v) 'clojure.core/unquote)
     (eval (second v))
     (let [f (first v)
           symb (if-let [r (resolve f)] (var-to-symbol r) f)]
       (add-meta symb (rest v))))
   :else v))

(defn ex* [expr]
  (walk/postwalk #(create-expression %) expr))

(defmacro ex [expr]
   (list 'quote (walk/postwalk #(create-expression %) expr)))

(defn create-expression-with-values [s expr]
  (if (and (sequential? expr) (symbol? (first expr)) (not= 'quote (first expr)))
    (if (= (first expr) 'clojure.core/unquote)
      (second expr)
      (let [f (first expr)
            symb (if-let [r (resolve f)] (var-to-symbol r) f)]
        (list* `ce  (list 'quote symb) (rest expr))))
    (if (s expr)
      (list 'quote expr)
      expr)))

(defn quote-if-not-unquote [args]
  (prn "hihihihihih args" args)
  (map #(if (and (sequential? %) (= (first %) 'clojure.core/unquote))
          (do (prn "vs " % )(second %))
          (if (and (sequential? %) (symbol? (first %)))
            (do (prn "hiiiiiier " %) %)
            (do (prn "vlq " %) (list 'quote %)))) args))

(defn create-expression-with-quoted-values [s expr]
  (if (and (sequential? expr) (symbol? (first expr)) (not= 'clojure.core/unquote (first expr)))
    (do (prn "hier" expr)(list* `ce (list 'quote (first expr)) (quote-if-not-unquote (rest expr))))
    (do (prn "daa " ) expr)))

(defn ex'* [& expr]
  (let [[s expr]
        (if (= (count expr) 1)
          [#{} (first expr)]
          [(into #{} (first expr)) (second expr)])]
    (eval (walk/prewalk #(create-expression-with-values s %) expr))))

(defmacro ex'
  [& expr]
  (let [[s expr]
        (if (= (count expr) 1)
          [#{} (first expr)]
          [(into #{} (first expr)) (second expr)])]
    (walk/prewalk #(create-expression-with-values s %) expr)))

(defmacro exn [expr]
  (walk/postwalk #(create-expression-with-quoted-values #{} %) expr))