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
            [numeric.expresso.impl.pimplementation :as impl]
            [clojure.core.logic.unifier :as u]
            [numeric.expresso.types :as types]
            [clojure.core.matrix :as mat]
            [clojure.core.matrix.operators :as mop]
            [numeric.expresso.utils :as utils])
  (:import [numeric.expresso.impl.pimplementation PolynomialExpression
            BasicExtractor]))
(declare ce cev)

;;(experimental) shape inference

(defn add-constraints [x constraints]
  (reduce (fn [l r] (protocols/add-constraint l r)) x constraints))

(declare create-normal-expression)

(defn first-last-pos-mshape [args]
  (let [args (vec args)
        n (count args)
        f (loop [i 0] (if (< i n) (if (< (count (nth args i)) 2)
                                    (recur (inc i)) i) nil))
        l (loop [i (dec n)] (if (<= 0 i) (if (< (count (nth args i)) 2)
                                           (recur (dec i)) i) nil))]
    (and f l [f l])))



(defn inner-product-shape [& symb]
  (if-let [[f l] (first-last-pos-mshape symb)]
    (if (= f l) (if (or (= 0 f) (= (dec (count symb)) f))
                  (nth symb f) [])
        (vec (concat (butlast (nth symb f)) (rest (nth symb l)))))
    (let [vs (remove empty? symb)]
      (if (even? (count vs)) [] (last vs)))))

(defn create-inner-product [[symb args]]
  (let [shapes (map protocols/shape args)
        expr (create-normal-expression symb args)]
    (-> expr (protocols/set-shape 
              (impl/eval-if-determined
               (create-normal-expression
                `inner-product-shape shapes))))))


(defn create-elemwise-operation [symb args]
  (if (empty? args)
    (create-normal-expression symb args)
    (let [lv (lvar 'shape)]
      (protocols/add-constraint
       (protocols/set-shape
        (->> args
             (map #(protocols/add-constraint % [utils/suffixo
                                                (protocols/shape %) lv]))
           (create-normal-expression symb)) lv)
       [utils/longest-shapo (mapv protocols/shape args) lv]))))

(defn longest-shape [& args]
  (first (sort-by (comp - count) args)))

(defn create-elemwise-operation [symb args]
  (let [se (create-normal-expression `longest-shape (map protocols/shape args))
        se (if (impl/no-symbol se) (protocols/evaluate se {}) se)]
    (-> (create-normal-expression symb args)
        (protocols/set-shape se))))

;;constructing dispatch for known symbols to expresso
      
(defmulti create-special-expression first)
(defmethod create-special-expression :default [_]  nil)
(defmethod create-special-expression 'inner-product [x]
  (create-inner-product x))
(defmethod create-special-expression 'mmul [x]
  (create-inner-product x))
(defmethod create-special-expression 'negate [[symb args]]
  (create-elemwise-operation '- args))
(defmethod create-special-expression 'add [[symb args]]
  (create-elemwise-operation '+ args))
(defmethod create-special-expression 'sub [[symb args]]
  (create-elemwise-operation '- args))
(defmethod create-special-expression 'emul [[symb args]]
  (create-elemwise-operation '* args))
(defmethod create-special-expression 'mul [[symb args]]
  (create-elemwise-operation '* args))
(defmethod create-special-expression 'div [[symb args]]
  (create-elemwise-operation '/ args))
(defmethod create-special-expression '+ [[symb args]]
  (create-elemwise-operation '+ args))
(defmethod create-special-expression '- [[symb args]]
  (create-elemwise-operation '- args))
(defmethod create-special-expression '* [[symb args]]
  (create-elemwise-operation '* args))
(defmethod create-special-expression '/ [[symb args]]
  (create-elemwise-operation '/ args))
(defmethod create-special-expression 'sum [[symb args]]
  (let [args (vec args)]
    (case (count args)
      3 (create-normal-expression 'sum args)
      4 (create-normal-expression 'sum [(nth args 0)
                                        (create-normal-expression
                                         '<= [(nth args 1) (nth args 0)
                                              (nth args 2)])
                                        (nth args 3)]))))
      


(defmulti expresso-name identity)
(defmethod expresso-name :default [s]
  (if (= (str s) "clojure.core//") '/ s))
(defmethod expresso-name 'clojure.core/* [_] '*)
(defmethod expresso-name 'clojure.core/+ [_] '+)
(defmethod expresso-name 'clojure.core/- [_] '-)
(defmethod expresso-name 'clojure.core// [_] '/)
(defmethod expresso-name `= [_] '=)
(defmethod expresso-name 'numeric.expresso.core/** [_] '**)
(defmethod expresso-name `mop/* [_] '*)
(defmethod expresso-name `mop/+ [_] '+)
(defmethod expresso-name `mop/- [_] '-)
(defmethod expresso-name `mat/emul [_] '*)
(defmethod expresso-name `mat/div [_] '/)
(defmethod expresso-name `mat/add [_] '+)
(defmethod expresso-name `mat/sub [_] '-)
(defmethod expresso-name 'Math/abs [_] 'abs)
(defmethod expresso-name 'Math/acos [_] 'acos)
(defmethod expresso-name 'Math/asin [_] 'asinc)
(defmethod expresso-name 'Math/atan [_] 'atan)
(defmethod expresso-name 'Math/cos [_] 'cos)
(defmethod expresso-name 'Math/cosh [_] 'cosh)
(defmethod expresso-name 'Math/exp [_] 'exp)
(defmethod expresso-name 'Math/log [_] 'log)
(defmethod expresso-name 'Math/log10 [_] 'log)
(defmethod expresso-name 'Math/sin [_] 'sin)
(defmethod expresso-name 'Math/sinh [_] 'sinh)
(defmethod expresso-name 'Math/sqrt [_] 'sqrt)
(defmethod expresso-name 'Math/tan [_] 'tan)
(defmethod expresso-name 'Math/tanh [_] 'tanh)
(defmethod expresso-name 'mat/negate [_] '-)
(defmethod expresso-name `mat/mul [_] 'mul)
(defmethod expresso-name `mat/inner-product [_] 'inner-product)

;;single expression creation
(defn create-expression [symbol args]
  (numeric.expresso.impl.pimplementation.Expression. symbol (vec args)))

(defn create-extractor [symb args]
  (when-let [rel (extractor-rel symb)]
    (numeric.expresso.impl.pimplementation.BasicExtractor. symb args rel)))

(defn construct-symbol [arg]
  (let [type (cond (:matrix (meta arg)) types/matrix
                   (:number (meta arg)) types/number
                   (:double (meta arg)) types/double
                   (:long   (meta arg)) types/long
                   (:int    (meta arg)) types/integer
                   :else (if (sequential? (:shape (meta arg)))
                                          types/matrix
                                          types/number))
        shape (cond (isa? type types/number) []
                    (= type types/matrix) (or (:shape (meta arg))
                                              (lvar 'shape))
                    :else (lvar 'shape))]
    (with-meta arg (merge {:type type :shape shape} (meta arg)))))

(defn create-normal-expression [symb args]
  (into '() (concat (reverse args) [(with-meta symb (add-information symb))])))

(defn ce
  "constructs an expression from the symbol with the supplied args"
  [symb & args]
  (let [symb (expresso-name symb)
        args (map #(if (symbol? %) (construct-symbol %) %) args)]
    (or (create-special-expression [symb args])
        (create-extractor symb args)
        (create-normal-expression symb args))))

(defn cev [symb args]
  (apply (partial ce symb) args))
;;experimental!! matrix-symb will probably not have an own type but reuse symbols with metadata


(defn expresso-symb [symb & {:keys [shape type properties]
                             :or {shape (lvar 'shape)
                                  type types/number
                                  properties #{}}}]
  (let [meta
        (cond
         (= type types/number)
         (if (or (lvar? shape) (= shape []))
           {:shape [] :type type :properties properties}
           {:shape shape :type types/matrix :properties properties})
         :else {:shape shape :type type :properties properties})]
    (construct-symbol (with-meta symb meta))))


(defn matrix-symb [symb &{:keys [shape properties]
                          :or {shape (lvar 'shape)
                               properties #{}}}]
  (expresso-symb symb :shape shape :properties properties :type types/matrix))

(defn zero-matrix [& {:keys [shape symb properties]
                   :or {shape (lvar 'shape)
                        symb (gensym "zeromat")
                        properties #{:mzero}}}]
  (expresso-symb symb :shape shape :type types/matrix
                 :properties (set/union #{:mzero} properties)))

(defn identity-matrix [& {:keys [shape symb properties]
                       :or {shape (lvar 'shape)
                            symb (gensym "identitymat")
                            properties #{:midentity}}}]
  (expresso-symb symb :shape shape :type types/matrix
                 :properties (set/union #{:midentity} properties)))

(derive 'e/ca+ 'e/ca-op)
(derive 'e/ca* 'e/ca-op)
(derive 'e/+   'e/ca+)
(derive 'e/*   'e/ca*)
(derive 'e/add   'e/ca-op)
(derive 'clojure.core/+ 'e/ca+)
(derive 'clojure.core/* 'e/ca*)
(derive 'clojure.core/- 'e/-)
(derive 'clojure.core// 'e/div)
(derive 'clojure.core.matrix.operators/+ 'e/ca-op)
(derive 'clojure.core.matrix/add 'e/ca-op)
(derive `° 'e/ao-op)

;;constructing and manipulation functions for sequential-matchers
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

;;code for high level constructing macros

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
  (apply ex'* expr))

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

(defn ex* [expr]
  (exnright expr))

(defmacro ex [expr]
  (ex* expr))


(defn let-expr [bindings code]
  (numeric.expresso.impl.pimplementation.LetExpression. bindings code))


(defn to-expression [expr]
  (if-let [op (protocols/expr-op expr)]
    expr
    (walk/postwalk #(if (and (seq? %) (symbol? (first %)))
                      (apply (partial ce (first %))  (rest %))
                      %) expr)))

(defn extractor? [x]
  (instance? BasicExtractor x))