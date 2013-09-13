(ns numeric.expresso.utils
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [numeric.expresso.protocols]
        [numeric.expresso.impl.pimplementation]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.walk :as walk])
  (:require [clojure.core.logic.unifier :as u]))

(def debug-mode true)

(defmacro debug
  "debugging macro fore core.logic"
  [vars & message]
  `(project ~vars
            (do (when debug-mode
                  (prn ~@message)) (== 1 1))))

(defn mapo
  "core.logic version of map"
  [fo vs rs]
  (conda
    [(emptyo vs) (emptyo rs)]
    [(fresh [v r restvs restrs]
            (conso v restvs vs)
            (conso r restrs rs)
            (fo v r)
            (mapo fo restvs restrs))]))

(defn lifto-with-inverse
  "Lifts a unary function and its inverse into a core.logic relation."
  ([f g]
    (fn [& vs]
      (let [[x y] vs]
        (conda 
          [(pred x number?) (project [x] (== y (f x)))]
          [(pred y number?) (project [y] (== x (g y)))])))))


(defn constant?
  "checks whether expr is constant"
  [expr]
  (number? expr))


(defn resolve-opo 
  "Resolves an operator to an actual function"
  ([op resolved-fn]
    (fresh []
      (project [op]
           (== resolved-fn @(resolve op)))))) 

(defn applyo 
  "Applies a logic function to a set of parameters."
  ([fo params result]
    (fresh []
           (project [params]
                    (apply fo (concat params (list result)))))))


(defn inco
  "core.logic non-relational inc"
  [a res]
  (project [a]
           (== res (inc a))))




(defn without-symbol?
  "true if expr does not have any occurrences of sym"
  [sym expr]
  (cond
    (and (symbol? expr) (= sym expr)) false
    (sequential? expr) (every? #(without-symbol? sym %) expr)
    :else true))


(defn expo 
  "Creates an expression with the given operator and parameters"
  ([op params exp]
     (conso op params exp)))


(defn- extract [c]
  (let [res 
        (mapcat
         #(if (and (coll? %) (= (first %) :numeric.expresso.construct/seq-match))
            (second %) [%]) c)]
    (if (vector? c) (into [] res)
        res)))


(defn splice-in-seq-matchers
  "eliminates all seq-matchers in the expression by embedding the data 
   the expression"
  [express]
  (let [nexpress
        (cond
         (vector? express) (mapv splice-in-seq-matchers express)
         (list? express) (apply list (map splice-in-seq-matchers express))
         (seq? express) (doall (map splice-in-seq-matchers express))
         :else express)
              expr (if (instance? clojure.lang.IObj nexpress)
                     (with-meta nexpress (meta express)) nexpress)]
    (if (and (coll? expr))
      (with-meta (extract expr) (meta expr))
      expr)))
    

(defn validate-eq
  "validates that expr is an equation"
  [expr]
  (if (and (not= '= (first expr)) (= (count expr) 3))
    (throw (Exception. "Input is no Equation"))
    expr))

(defn lasto
  "y is the last element of x"
  [x y]
  (fresh [a] (appendo a [y] x)))

(defn butlasto
  "y ist butlast from x"
  [x y]
  (fresh [a]
         (appendo y [a] x)))


(defn get-in-expression
  "gets the subexpression in pos posv in expr"
  [expr posv]
  (loop [expr expr posv posv]
    (if (empty? posv)
      expr
      (recur (nth expr (inc (first posv))) (rest posv)))))

(defn- set-elem-in-pos
  [l pos sub]
  (apply list (concat (take pos l) [sub] (drop (inc pos) l))))

(defn set-in-expression
  "assocs sub in the position posv in the expression"
  [expr posv sub]
  (loop [posv posv sub sub]
    (if (< (count posv) 2)
      (set-elem-in-pos expr (inc (first posv)) sub)
      (let [p (get-in-expression expr (butlast posv))
            nsub (set-elem-in-pos p (inc (last posv)) sub)]
        (recur (butlast posv) nsub)))))

(defn substitute-in-positions
  "substitutes the expression giving the pos -> subexpression map"
  [expr pos-map]
  (reduce (fn [expr [k v]]
            (set-in-expression expr k v)) expr pos-map))

(defn only-one-occurrence
  "checks if there is at most one occurrence ov v in equation"
  [v equation]
  (>= 1 (->> equation flatten (filter #{v}) count)))

(defn positions-of
  "returns the positions of v in equation"
  ([v equation] (positions-of v equation []))
  ([v equation pos]
     (if-let [op (expr-op equation)]
       (filter identity
               (mapcat #(positions-of v %1 (conj pos %2))
                       (rest equation) (range)))
       (if (= v equation) [pos] nil))))
                  
(defn swap-sides
  "swaps the sides of the equation"
  [[eq lhs rhs]]
  (list eq rhs lhs))

(def combine-solutions mapcat)



(def ^:dynamic *treshold* 1e-9)

(defn num=
  "equals operation applicable on all expression types. compares numbers with
   == other types with =. Does not throw. Also succeeds if a and b are a very
   near numerically according to *treshold*"
  [a b]
  (or (= a b) (and (number? a) (number? b)
                   (or (clojure.core/== a b)
                       (< (Math/abs (- (Math/abs (double a))
                                       (Math/abs (double b)))) *treshold*)))))

(defn eq-lhs
  "returns the lhs of equation"
  [equation]
  (second equation))

(defn eq-rhs
  "returns the rhs of equation"
  [equation]
  (nth equation 2))

(defn solved?
  "checks if equation is already solved in regard to v"
  [v equation]
  (and (= (nth equation 1) v)
       (not= v (nth equation 2))
       (= 0 (->> (nth equation 2) flatten (filter #{v}) count))))

(defn submap
  "returns the reduced map m which contains only keys in keys"
  [keys m]
  (into {} (reduce (fn [kvs symb]
                     (if (contains? m symb)
                       (conj kvs [symb (get m symb)])
                       kvs)) [] keys)))

(defn common-prefix
  "returns the common-prefix of the position vectors in positions"
  [positions]
  (let [minl (apply min (map count positions))]
    (loop [l minl]
      (if (> l 0)
        (if (every? #{(subvec (first positions) 0 l)}
                    (map #(subvec % 0 l) (rest positions)))
          (subvec (first positions) 0 l)
          (recur (dec l)))
        []))))


(defn gcd
  "calculates gcd of m and n"
  [m n]
  (loop [m (long m) n (long n)]
    (if (> n 0)
      (recur n (rem m n))
      m)))

(defn round
  "rounds m if m is not an integer"
  [m]
  (if (integer? m)
    m (Math/round (double m))))