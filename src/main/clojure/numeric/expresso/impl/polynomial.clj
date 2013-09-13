(ns numeric.expresso.impl.polynomial
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [numeric.expresso.properties]
        [numeric.expresso.construct]
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
  (:import [numeric.expresso.impl.pimplementation PolynomialExpression]))

(declare coef main-var poly poly+poly)
;;polynomial canonical form code inspired by PAIP chapter 15. but extended and immutable

(defn main-var [^PolynomialExpression poly]
  (if (number? poly) nil
      (.-v poly)))

(defn coef [^PolynomialExpression poly ^long i]
  (if (number? poly) 0
      (nth (.-coeffs poly) i)))

(defn degree [^PolynomialExpression poly]
  (if (number? poly) 0
      (- (count (.-coeffs poly)) 1)))

(defn poly [x & coeffs]
  (impl/make-poly x (into [] coeffs)))

(defn new-poly [x degree]
  (loop [i 0 coeffs (transient [])]
    (if (<= i degree)
      (recur (+ i 1) (conj! coeffs 0))
      (impl/make-poly x (persistent! coeffs)))))

(defn set-main-var [^PolynomialExpression poly v]
  (impl/make-poly v (.-coeffs poly)))

(defn set-coef [^PolynomialExpression poly i val]
  (impl/make-poly (.-v poly) (assoc (.-coeffs poly) i val)))

;;these functions define the order of variables which in turns define the
;;normal form of the recursive implementation. (bigger variables become the
;;coefficients)
;;dynamic rebindable to let the (power) user specify the exact form of the
;;polynomial
(defn ^:dynamic var= [x y] (= x y))
(defn ^:dynamic var> [x y] (< 0 (compare x y)))

(declare poly+poly normalize-poly poly*poly)

(defn p== [x y]
  (if (and (number? x) (number? y))
    (clojure.core/== x y)
    (= x y)))

(defn poly**n [p  n]
  (if (integer? n)
    (cond
     (p== n 0) (do (assert (not (= p 0))) 1)
     (integer? p) (Math/pow p n)
     :else (poly*poly p (poly**n p (- ^long n 1))))
    :error))
   

(defn normalize-poly [p]
  (if (number? p) p
      (let [coeffs (.-coeffs ^PolynomialExpression p)
            pdeg (loop [i (degree p)]
                   (if (or (>= 0 i) (not (p== (nth coeffs i) 0)))
                     i (recur (dec i))))]
        (cond (<= pdeg 0) (normalize-poly (coef p 0))
              (< pdeg (degree p))
              (impl/make-poly (.-v ^PolynomialExpression p)
                                   (subvec (.-coeffs ^PolynomialExpression p)
                                           0 (inc pdeg)))
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
       (impl/make-poly (main-var p) nc)))
   :else :error))

(defn k*poly [k ^PolynomialExpression p]
  (cond
   (p== k 0) 0 (p== k 1) p
   (and (number? k) (number? p)) (* k p)
   :else
   (impl/make-poly (main-var p) (mapv #(poly*poly k %) (.-coeffs p)))))


(defn poly*poly [p q]
  (normalize-poly
   (cond
    (number? p) (k*poly p q)
    (number? q) (k*poly q p)
    (some #{:error} [p q]) :error
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
  (if (or (> (count args) 2)
          (not (number? (second args))))
    :error
    (poly**n (first args) (second args))))

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


(defn to-poly-normal-form*
  ([expr]
     (let [res (if (and (seq? expr) (symbol? (first expr)))
                 (let [args (map to-poly-normal-form*  (rest expr))]
                   (if (some #{:error} args)
                     :error
                     (apply (construct-poly (first expr)) args)))
                 (if (symbol? expr) (poly expr 0 1)
                     (if (number? expr) expr :error)))]
       res))
  ([expr v>]
     (binding [var> v>]
       (to-poly-normal-form* expr))))


(defn to-poly-normal-form
  ([expr] (when-let [res (to-poly-normal-form* expr)]
            (when (not= res :error) res)))
  ([expr v>] (when-let [res (to-poly-normal-form* expr v>)]
               (when (not= res :error) res))))


(defn poly-in [x poly]
  (when poly
    (to-poly-normal-form (protocols/to-sexp poly)
                         (fn [v y] (if (= v x)
                                     false
                                     (if (= y x)
                                       true
                                       (< 0 (compare v y))))))))


(defn pd [u v]
  (let [m (- (count u) 1) n (- (count v) 1)]
    (loop [k (- m n) u u q (mat/new-vector (+ (- m n) 1))]
      (if (>= k 0)
        (let [q (assoc q k (/ (nth u (+ n k)) (nth v n)))
              u (loop [u u j (+ n k )]
                  (if (>= j k)
                    (recur
                     (let []
                       (assoc u j (- (nth u j) (* (nth q k) (nth v (- j k))))))
                     (dec j))
                    u))]
          (recur (dec k) u q))
        [q (subvec u 0 n)]))))


(defn poly-division [^PolynomialExpression u ^PolynomialExpression v]
  (and (= (main-var u) (main-var v))
       (let [[q r] (pd (.-coeffs u) (.-coeffs v))]
         [(normalize-poly (impl/make-poly (main-var u) q))
          (normalize-poly (impl/make-poly (main-var u) r))])))

(defn factors [n] (map #(/ n %) (filter #(zero? (rem n %)) (range 1 (+ n 1)))))

(defn ratio-root-guesses [^PolynomialExpression poly]
  (if (every? #(and (number? %) (or (integer? %) (utils/num= (utils/round %) %)))
                    (.-coeffs poly))
    (apply concat (for [n (factors (Math/abs ^double (coef poly 0)))
                        d (factors (Math/abs ^double (coef poly (degree poly))))]
                    [(/ n d) (/ (- n) d)]))
    '()))

(defn ratio-root [poly]
  (reduce (fn [factors guess]
            (let [p (first factors)
                  div (to-poly-normal-form (ce '- (main-var poly) guess))
                  [quot r] (poly-division p div)]
              (if (or (= r 0) (= r 0.0))
                (list* quot div (rest factors))
                factors))) (list poly) (ratio-root-guesses poly)))