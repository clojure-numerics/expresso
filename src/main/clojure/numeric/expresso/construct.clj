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
            [numeric.expresso.types :as types]
            [clojure.core.matrix :as mat]
            [numeric.expresso.utils :as utils])
  (:import [numeric.expresso.protocols PolynomialExpression]))

(defn add-constraints [x constraints]
  (reduce (fn [l r] (protocols/add-constraint l r)) x constraints))

(declare create-matrix-inner-product
         create-normal-expression)


(defmulti create-special-expression first)
(defmethod create-special-expression :default [_]  nil)
(defmethod create-special-expression 'inner-product [x]
  (create-matrix-inner-product x))
(defmethod create-special-expression 'negate [_]
  (if (is-number? (first (second _)))
    (create-normal-expression '- (second _))
    (create-normal-expression 'negate (second _))))

(defmethod create-special-expression 'add [[symb args]]
  (if (is-number? (first args))
    (create-normal-expression '+ args)
    (let [constraints (map (fn [x] [== (protocols/shape (first args))
                                       (protocols/shape x)]) (rest args))]
      (create-normal-expression 'add (map #(add-constraints % constraints)
                                          args)))))



(defmulti expresso-symb identity)
(defmethod expresso-symb :default [s]
  (if (= (str s) "clojure.core//") '/ s))
(defmethod expresso-symb 'clojure.core/* [_] '*)
(defmethod expresso-symb 'clojure.core/+ [_] '+)
(defmethod expresso-symb 'clojure.core/- [_] '-)
(defmethod expresso-symb 'clojure.core// [_] '/)
(defmethod expresso-symb 'numeric.expresso.core/** [_] '**)
(defmethod expresso-symb `mat/emul [_] 'emul)
(defmethod expresso-symb `mat/div [_] 'div)
(defmethod expresso-symb `mat/add [_] 'add)
(defmethod expresso-symb `mat/sub [_] 'sub)
(defmethod expresso-symb 'Math/abs [_] 'abs)
(defmethod expresso-symb 'Math/acos [_] 'acos)
(defmethod expresso-symb 'Math/asin [_] 'asinc)
(defmethod expresso-symb 'Math/atan [_] 'atan)
(defmethod expresso-symb 'Math/cos [_] 'cos)
(defmethod expresso-symb 'Math/cosh [_] 'cosh)
(defmethod expresso-symb 'Math/exp [_] 'exp)
(defmethod expresso-symb 'Math/log [_] 'log)
(defmethod expresso-symb 'Math/log10 [_] 'log)
(defmethod expresso-symb 'Math/sin [_] 'sin)
(defmethod expresso-symb 'Math/sinh [_] 'sinh)
(defmethod expresso-symb 'Math/sqrt [_] 'sqrt)
(defmethod expresso-symb 'Math/tan [_] 'tan)
(defmethod expresso-symb 'Math/tanh [_] 'tanh)
(defmethod expresso-symb 'mat/negate [_] 'negate)
(defmethod expresso-symb `mat/mul [_] 'mul)
(defmethod expresso-symb `mat/inner-product [_] 'inner-product)
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

(defn create-normal-expression [symb args]
  (list* (with-meta symb (add-information symb)) args))

(defn ce
  "constructs an expression from the symbol with the supplied args"
  [symb & args]
  (let [symb (expresso-symb symb)]
    (or (create-special-expression [symb args])
        (create-extractor symb args)
        (create-normal-expression symb args))))

(defn matrix-symb
  ([s] (matrix-symb s #{}))
  ([s additional-props] (matrix-symb s #{} [(lvar 'srows) (lvar 'scols)]))
  ([s additional-props shape]     
     #_(add-metadata s {:type :matrix
                      :properties (set additional-props)
                        :shape shape })
     (numeric.expresso.protocols.MatrixSymbol. s shape additional-props)))

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


(defn create-matrix-inner-product [[symb args]]
  (if (> (count args) 1)
    (let [nargs (reduce (fn [processed new]
                          (let [lp (last processed)
                                l (second (protocols/shape lp))
                                r (first (protocols/shape new))]
                (concat (butlast processed)
                        [(protocols/add-constraint lp [== l r])]
                        [(protocols/add-constraint new [== l r])])))
                        [(first args)] (rest args))]
      (list* symb nargs))
    (list* symb args)))


(defn main-var [^PolynomialExpression poly]
  (.-v poly))

(defn coef [^PolynomialExpression poly ^long i]
  (nth (.-coeffs poly) i))

(defn degree [^PolynomialExpression poly]
  (- (count (.-coeffs poly)) 1))

(defn poly [x & coeffs]
  (protocols/make-poly x (into [] coeffs)))

(defn new-poly [x degree]
  (loop [i 0 coeffs (transient [])]
    (if (<= i degree)
      (recur (+ i 1) (conj! coeffs 0))
      (protocols/make-poly x (persistent! coeffs)))))

(defn set-main-var [^PolynomialExpression poly v]
  (protocols/make-poly v (.-coeffs poly)))

(defn set-coef [^PolynomialExpression poly i val]
  (protocols/make-poly (.-v poly) (assoc (.-coeffs poly) i val)))


(defn var= [x y] (= x y))
(defn var> [x y] (< 0 (compare x y)))

(declare poly+poly normalize-poly poly*poly)

(defn p== [x y]
  (if (and (number? x) (number? y))
    (clojure.core/== x y)
    (= x y)))

(defn poly**n [p ^long n]
  (cond
   (p== n 0) (do (assert (not (= p 0))) 1)
   (integer? p) (Math/pow p n)
   :else (poly*poly p (poly**n p (- n 1)))))
   

(defn normalize-poly [p]
  (if (number? p) p
      (let [coeffs (.-coeffs p)
            pdeg (loop [i (degree p)]
                   (if (or (>= 0 i) (not (p== (nth coeffs i) 0)))
                     i (recur (dec i))))]
        (cond (<= pdeg 0) (normalize-poly (coef p 0))
              (< pdeg (degree p))
              (protocols/make-poly (.-v p) (subvec (.-coeffs p) 0 pdeg))
              :else p))))

(defn poly*same [p q]
  (let [r-degree (+ (degree p) (degree q))
        r (new-poly (main-var p) r-degree)
        q-degree (degree q) p-degree (degree p)]
    (loop [i 0 r r]
      (if (<= i p-degree)
        (if (not (clojure.core/= (coef p i) 0))
          (recur (inc i)
                 (loop [j 0 r r]
                   (if (<= j q-degree)
                     (recur
                      (inc j) (set-coef r (+ i j)
                                        (poly+poly (coef r (+ i j))
                                                   (poly*poly (coef p i)
                                                              (coef q j)))))
                     r)))
          (recur (inc i) r))
        r))))

(defn polydk [^PolynomialExpression p k]
  (cond
   (p== k 0) :error
   (and (number? k) (number? p)) (/ p k)
   (number? k)
   (let [nc (mapv #(polydk % k) (.-coeffs p))]
     (if (some #{:error} nc)
       :error
       (protocols/make-poly (main-var p) nc)))
   :else :error))

(defn k*poly [k ^PolynomialExpression p]
  (cond
   (p== k 0) 0 (p== k 1) p
   (and (number? k) (number? p)) (* k p)
   :else
   (protocols/make-poly (main-var p) (mapv #(poly*poly k %) (.-coeffs p)))))


(defn poly*poly [p q]
  (normalize-poly
   (cond
    (number? p) (k*poly p q)
    (number? q) (k*poly q p)
    (var= (main-var p) (main-var q)) (poly*same p q)
    (var> (main-var q) (main-var p)) (k*poly q p)
    :else (k*poly p q))))

(defn poly+same [p q]
  (if (> (degree p) (degree q))
    (poly+same q p)
    (let [d (degree p)]
      (loop [i 0 res q]
        (if (<= i d)
          (recur (inc i) (set-coef res i (poly+poly (coef res i) (coef p i))))
          res)))))

(defn k+poly [k p]
  (cond (= k 0) p
        (and (number? k) (number? p)) (+ k p)
        :else (set-coef p 0 (poly+poly (coef p 0) k))))

(defn poly+poly [p q]
  (normalize-poly
   (cond
    (number? p) (k+poly p q)
    (number? q) (k+poly q p)
    (var= (main-var p) (main-var q)) (poly+same p q)
    (var> (main-var q) (main-var p)) (k+poly q p)
    :else (k+poly p q))))

(declare poly+poly poly*poly)

(defn poly+ [& args]
  (reduce poly+poly args))

(defn poly- [& args]
  (if (= (count args) 1)
    (poly*poly -1 (first args))
    (apply
     (partial poly+ (first args)) (map #(poly*poly -1 %) (rest args)))))

(defn poly*polyc [& args]
  (reduce poly*poly args))

(defn polydkc [& args]
  (reduce polydk args))

(defn poly**nc [& args]
  (poly**n (first args) (second args)))

(defmulti construct-poly identity)
(defmethod construct-poly :default [_] (fn [& a] :error))
(defmethod construct-poly '+ [_] poly+)
(defmethod construct-poly `+ [_] poly+)
(defmethod construct-poly '- [_] poly-)
(defmethod construct-poly `- [_] poly-)
(defmethod construct-poly `/ [_] polydkc)
(defmethod construct-poly '/ [_] polydkc)
(defmethod construct-poly '* [_] poly*polyc)
(defmethod construct-poly `* [_] poly*polyc)
(defmethod construct-poly '** [_] poly**nc)


(defn to-poly-normal-form [expr]
  (if (and (seq? expr) (symbol? (first expr)))
    (let [args (map to-poly-normal-form  (rest expr))]
      (if (some #{:error} args)
        :error
        (apply (construct-poly (first expr)) args)))
    (if (symbol? expr) (poly expr 0 1)
        (if (number? expr) expr :error))))

(defn poly-to-sexp [poly]
  (if (number? poly) poly
      (let [v (.-v poly)
            coeffs (.-coeffs poly)]
        (list* '+ (map #(list '* (poly-to-sexp %1) (list '** v %2))
                      coeffs (range))))))


(defmethod protocols/type-of-function :default [_] :Unknown)
(defmethod protocols/type-of-function '+ [_] types/number)
(defmethod protocols/type-of-function '- [_] types/number)
(defmethod protocols/type-of-function '* [_] types/number)
(defmethod protocols/type-of-function '/ [_] types/number)
(defmethod protocols/type-of-function 'div [_] types/matrix)
(defmethod protocols/type-of-function 'sub [_] types/number)
(defmethod protocols/type-of-function '** [_] types/number)
(defmethod protocols/type-of-function 'emul [_] types/matrix)
(defmethod protocols/type-of-function 'add [_] types/matrix)
(defmethod protocols/type-of-function 'negate [_] types/matrix)


(defn split-in-pos-args [args pos]
  (let [args (vec args)]
    [(subvec args 0 pos) (nth args pos) (subvec args (inc pos))]))


(defmethod protocols/rearrange-step-function '+ [[op args pos rhs]]
  (let [[left x right] (split-in-pos-args args pos)]
    (apply (partial ce '-) (concat [rhs] left right))))

