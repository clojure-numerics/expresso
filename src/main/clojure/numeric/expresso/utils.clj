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

(defmacro debug [vars & message]
  `(project ~vars
            (do (when debug-mode
                  (prn ~@message)) (== 1 1))))

(defn mapo [fo vs rs]
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


(defn constant? [expr]
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


(defn inco [a res]
  (project [a]
           (== res (inc a))))




(defn without-symbol? [sym expr]
  (cond
    (and (symbol? expr) (= sym expr)) false
    (sequential? expr) (every? #(without-symbol? sym %) expr)
    :else true))


(defn expo 
  "Creates an expression with the given operator and parameters"
  ([op params exp]
     (conso op params exp)))


(defn expo 
  "Creates an expression with the given operator and parameters"
  ([op params exp]
     (conso op params exp)))


(defn extract [c]
  (let [res 
        (mapcat
         #(if (and (coll? %) (= (first %) :numeric.expresso.construct/seq-match))
            (second %) [%]) c)]
    (if (vector? c) (into [] res)
        res)))


(defn splice-in-seq-matchers [express]
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
    

(defn validate-eq [expr]
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


(defn inner-product-shape [sl sr s]
  (fresh [a b]
         (butlasto sl a)
         (resto sr b)
         (appendo a b s)))


(defn suffixo [a b]
  (fresh [c]
         (appendo c a b)))

(defne all-suffixes [v l]
  ([[?a . ?r] _] (suffixo ?a l) (all-suffixes ?r l))
  ([[] _]))

(defn longest-shapo [v l]
  (fresh []
         (membero l v)
         (all-suffixes v l)))

(defn get-in-expression [expr posv]
  (loop [expr expr posv posv]
    (if (empty? posv)
      expr
      (recur (nth expr (inc (first posv))) (rest posv)))))

(defn set-elem-in-pos [l pos sub]
  ;;todo use cev here and resolve cyclic dependency
  (apply list (concat (take pos l) [sub] (drop (inc pos) l))))

(defn set-in-expression [expr posv sub]
  (loop [posv posv sub sub]
    (if (< (count posv) 2)
      (set-elem-in-pos expr (inc (first posv)) sub)
      (let [p (get-in-expression expr (butlast posv))
            nsub (set-elem-in-pos p (inc (last posv)) sub)]
        (recur (butlast posv) nsub)))))

(defn substitute-in-positions [expr pos-map]
  (reduce (fn [expr [k v]]
            (set-in-expression expr k v)) expr pos-map))

(defn only-one-occurrence [v equation]
  (>= 1 (->> equation flatten (filter #{v}) count)))

(defn positions-of
  ([v equation] (positions-of v equation []))
  ([v equation pos]
     (if-let [op (expr-op equation)]
       (filter identity
               (mapcat #(positions-of v %1 (conj pos %2))
                       (rest equation) (range)))
       (if (= v equation) [pos] nil))))
                  
(defn swap-sides [[eq lhs rhs]]
  (list eq rhs lhs))

(def combine-solutions mapcat)



(def ^:dynamic *treshold* 1e-6)

(defn num= [a b]
  (or (= a b) (and (number? a) (number? b)
                   (or (clojure.core/== a b)
                       (< (Math/abs (- (Math/abs (double a))
                                       (Math/abs (double b)))) *treshold*)))))

(defn eq-lhs [equation]
  (second equation))

(defn eq-rhs [equation]
  (nth equation 2))

(defn solved? [v equation]
  (and (= (nth equation 1) v)
       (not= v (nth equation 2))
       (= 0 (->> (nth equation 2) flatten (filter #{v}) count))))

(defn submap [keys m]
  (into {} (reduce (fn [kvs symb]
                     (if (contains? m symb)
                       (conj kvs [symb (get m symb)])
                       kvs)) [] keys)))

(defn common-prefix [positions]
  (let [minl (apply min (map count positions))]
    (loop [l minl]
      (if (> l 0)
        (if (every? #{(subvec (first positions) 0 l)}
                    (map #(subvec % 0 l) (rest positions)))
          (subvec (first positions) 0 l)
          (recur (dec l)))
        []))))

(defn remove-dublicated-fracs [frac]
  (into #{}
        (map (fn [x] [x (:pos (meta x))])
             (into #{} (map #(with-meta (first %) {:pos (second %)}) frac)))))

(defn gcd [m n]
  (loop [m (long m) n (long n)]
    (if (> n 0)
      (recur n (rem m n))
      m)))

(defn round [m]
  (if (integer? m)
    m (Math/round (double m))))