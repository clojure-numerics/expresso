(ns numeric.expresso.properties
  (:refer-clojure :exclude [== record?])
  (:use [clojure.core.logic])
  (:require [numeric.expresso.impl.pimplementation])
  (:import [numeric.expresso.impl.pimplementation
            Expression])
  (:require [clojure.walk :as walk]
            [clojure.core.matrix :as mat]
            [clojure.core.matrix.linear :as lin]
            [numeric.expresso.types :as types]
            [numeric.expresso.impl.matcher :as match]
            [numeric.expresso.protocols :as protocols]))

(declare evaluate-sum emit-sum emit-arithmetic)

(defn- corrected-sub [& s]
  (if (= 1 (count s))
    (mat/negate (first s))
    (apply mat/sub s)))

;;The props multimethod is used to assign the right metadata to the symbols
;;during construction of expressions. Many protocol implementation are driven
;;by the functions in the metadata.
(defmulti props "gets the metadata associated with the given operator"
  identity)
(defmethod props :default [_] {})
(defmethod props '* [_] {:exec-func mat/emul
                         :emit-func (emit-arithmetic '* mat/emul)
                         :properties #{:associative
                                      :commutative
                                      :n-ary}
                         })
(defmethod props '+ [_] {:exec-func mat/add
                         :emit-func (emit-arithmetic '+ mat/add)
                         :properties #{:associative :commutative :n-ary}})
(defmethod props '- [_] {:exec-func corrected-sub
                         :emit-func (emit-arithmetic '- corrected-sub)
                         :properties [:n-ary [:inverse-of '+]]})
(defmethod props '/ [_] {:exec-func mat/div
                         :emit-func (emit-arithmetic '/ corrected-sub)
                         :properties #{:n-ary} :inverse-of '*})
(defmethod props 'e/ca-op [_] {:properties [:commutative]})
(defmethod props '** [_] {:exec-func (fn [a b]
                                       (Math/pow a b))})
(defmethod props 'emul [_] {:exec-func mat/emul})
(defmethod props 'div [_] {:exec-func mat/div})
(defmethod props 'add [_] {:exec-func mat/add
                           :properties #{:associative :commutative}})
(defmethod props 'sub [_] {:exec-func mat/sub})
(defmethod props 'inner-product [_] {:exec-func mat/inner-product :properties #{:associative}})
(defmethod props 'scale [_] {:exec-func mat/scale })
(defmethod props 'mul [_] {:exec-func mat/mul})
(defmethod props 'add-product [_] {:exec-func mat/add-product})
(defmethod props 'add-scaled [_] {:exec-func mat/add-scaled})
(defmethod props 'add-scaled-product [_] {:exec-func mat/add-scaled-product})
(defmethod props 'scale [_] {:exec-func mat/scale})
(defmethod props 'normalise [_] {:exec-func mat/normalise})
(defmethod props 'dot [_] {:exec-func mat/dot})
(defmethod props 'outer-product [_] {:exec-func mat/outer-product})
(defmethod props 'cross [_] {:exec-func mat/cross})
(defmethod props 'distance [_] {:exec-func mat/distance})
(defmethod props 'det [_] {:exec-func mat/det})
(defmethod props 'inverse [_] {:exec-func mat/inverse})
(defmethod props 'negate [_] {:exec-func mat/negate})
(defmethod props 'trace [_] {:exec-func mat/trace})
(defmethod props 'length [_] {:exec-func mat/length})
(defmethod props 'length-squared [_] {:exec-func mat/length-squared})
(defmethod props 'pow [_] {:exec-func mat/pow})
(defmethod props 'log [_] {:exec-func mat/log
                           })
(defmethod props 'sum [_] {:eval-func evaluate-sum
                           :emit-func emit-sum})
(defmethod props 'sqrt [_] {:exec-func mat/sqrt
                            })
(defmethod props 'log [_] {:exec-func mat/log
                           })
(defmethod props 'asin [_] {:exec-func mat/asin})
(defmethod props 'acos [_] {:exec-func mat/acos})
(defmethod props 'atan [_] {:exec-func mat/atan})
(defmethod props 'sin [_] {:exec-func mat/sin})
(defmethod props 'cos [_] {:exec-func mat/cos})
(defmethod props 'tan [_] {:exec-func mat/tan})
(defmethod props 'abs [_] {:exec-func mat/abs})
(defmethod props 'exp [_] {:exec-func mat/exp})
(defmethod props 'norm [_] {:exec-func lin/norm})
(defmethod props 'rank [_] {:exec-func lin/rank})
(defmethod props 'qr [_] {:exec-func lin/qr})
(defmethod props 'cholesky [_] {:exec-func lin/cholesky})
(defmethod props 'lu [_] {:exec-func lin/lu})
(defmethod props 'svd [_] {:exec-func lin/svd})
(defmethod props 'eigen [_] {:exec-func lin/eigen})
(defmethod props 'solve [_] {:exec-func lin/solve})
(defmethod props 'least-squares [_] {:exec-func lin/least-squares})


(defmulti matcher "gets the matching relation for the extractor-expression"
  first)

(defmethod matcher :default [_]
  (if (contains? (:properties (second _)) :commutative)
    {:match-rel match/match-commutativeo}
    {:match-rel match/expression-matcho}))
(defmethod matcher 'e/ca-op [_] {:match-rel match/match-commutativeo})


;;These predicates are contributed to core.matrix and the core.matrix predicates
;;will be used when they become available in a core.matrix release

(defn zero-matrix?
  "checks whether expr represents a zero-matrix"
  [expr]
  (if (symbol? expr)
    (if (contains? (protocols/properties expr) :mzero) true false)
    (loop [elem (mat/eseq expr)]
      (if (seq elem)
        (if (and (number? (first elem)) (clojure.core/== 0 (first elem)))
          (recur (rest elem))
          false)
        true))))

(defn identity-matrix?
  "checks whether expr represents an identity-matrix"
  [expr]
  (try 
  (if (symbol? expr) false
      (let [d (mat/dimensionality expr)]
        (cond
         (clojure.core/== d 0) (clojure.core/== expr 1)
         (clojure.core/== d 1) (and (clojure.core/== (count expr) 1)
                                    (clojure.core/== (first expr) 1))
         (clojure.core/== d 2)
         (let [rc (mat/row-count expr)
               cc (mat/column-count expr)]
           (loop [i 0]
             (if (< i rc)
               (if (nil? (loop [j 0]
                           (if (< j cc)
                             (let [elem (mat/mget expr i j)]
                               (when-not (symbol? elem)
                                 (cond
                                  (clojure.core/== elem 0) (if (clojure.core/== i j)
                                                             false
                                                             (recur (inc j)))
                                  (clojure.core/== elem 1) (if (clojure.core/== i j)
                                                             (recur (inc j))
                                                             false)
                                  :else false))))))
                 (recur (inc i))
                 false)
               true))))))
  (catch Exception e false)))
      
(defn- extract-mzero [pargs expr]
  (project [pargs expr]
           (let [x (first pargs)]
             (if (contains? (protocols/properties expr) :mzero)
               (== x expr)
               (if (zero-matrix? expr)
                 (== x expr)
                 fail)))))

(defn- extract-midentity [pargs expr]
  (project [pargs expr]
           (let [x (first pargs)]
             (if (contains? (protocols/properties expr) :midentity)
               (== x expr)
               (if (identity-matrix? expr)
                 (== x expr)
                 fail)))))

(defn- extract-as [pargs expr]
  (project [pargs expr]
           (let [x (first pargs)
                 y (second pargs)]
             (fresh []
                    (protocols/match x expr)
                    (== y expr)))))

(defn- extract-shape [pargs expr]
  (project [pargs expr]
           (let [x (first pargs)
                 y (second pargs)]
             (fresh []
                    (protocols/match x expr)
                    (== y (protocols/shape expr))))))

(defmulti extractor-rel
  "associates extracting relations with extractor symbols"
  identity)
(defmethod extractor-rel :default [_] nil)
(defmethod extractor-rel 'is? [_] match/extract-is)
(defmethod extractor-rel 'cons? [_] match/extract-cons)
(defmethod extractor-rel 'mzero? [_] extract-mzero)
(defmethod extractor-rel 'midentity? [_] extract-midentity)
(defmethod extractor-rel 'as? [_] extract-as)
(defmethod extractor-rel 'shape? [_] extract-shape)

(defn add-information
  "adds the metadata to op for further manipulation with expresso"
  [op]
  (let [p (props op)
        m (matcher [op p])]
    (merge {:expression true} p m)))

(defn is-number?
  "checks if x represents a number"
  [x]
  (or (number? x) (isa? (protocols/type-of x) types/number)))

(defn is-symbol?
  "checks if x represents a symbol"
  [x]
 (symbol? x))


(defn- evaluate-sum [sum sm]
  (let [[_ k i expr] sum
        i (protocols/substitute-expr i sm)]
    (if (and (or (= (first i) '<=) (= (first i) '<)) (= k (nth i 2)))
      (let [start (if (= (first i) '<=) (second i) (inc (second i)))
            end   (if (= (first i) '<=) (nth i 3)  (dec (nth i 3)))]
        (loop [n start res 0]
          (if (<= n end)
            (recur (inc n) (mat/add res
                                    (-> expr
                                        (protocols/evaluate (merge sm {k n})))))
            res)))
      (throw (Exception. (str "Can't evaluate sum of the range " i))))))

(defn- emit-sum [sum]
  (let [[_ k i expr] sum]
    (if (and (or (= (first i) '<=) (= (first i) '<)) (= k (nth i 2)))
      (let [start (if (= (first i) '<=) (second i) `(inc ~(second i)))
            end   (if (= (first i) '<=) (nth i 3)  `(dec ~(nth i 3)))]
        `(loop [n# (long ~start) res# 0]
           (if (<= n# ~end)
             (let [~k n#]
               (recur (inc n#) (mat/add res# ~(protocols/emit-code expr))))
               res#)))
      (throw (Exception. (str "Can't emit code for sum of the range " i))))))


(defn- emit-arithmetic
  "emits code for clojure.core/op literally when all args of the expression
   are numbers"
  [op  exec-func]
  (fn [expr]
    (let [args (protocols/expr-args expr)]
      (if (every? #{[]} (map protocols/shape args))
        (list* op (map protocols/emit-code args))
        (list* exec-func (map protocols/emit-code args))))))
