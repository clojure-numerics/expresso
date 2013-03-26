(ns mikera.expresso.core
  (:use [mikera.cljutils error])
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.logic.unifier :as u]))

(set! *warn-on-reflection* true)
(set! *unchecked-math* true)

(declare ex*)

;; ========================================
;; Expression datatype
;; node is either: 
;;  - a constant value
;;  - a lvar
;;  - a list of (Operation Expression+)
(deftype Expression [node vars]
  java.lang.Object
    (hashCode [a]
      (.hashCode node))
    (equals [a b]
      (and (instance? Expression b) 
           (let [^Expression b b] 
             (and (= (.node a) (.node b)) (= (.vars a) (.vars b))))))
    (toString [this]
      (str node)))

(defn expression? [a]
  (instance? Expression a))

(defn unify-with-expression* [^Expression u v s]
   (cond 
     (and (sequential? v) (sequential? (.node u)))
       (loop [ns (.node u) v v s s]
         (if (empty? v)
           s
           (when-let [s (unify s (first v) (first ns))]
             (recur (next ns) (next v) s))))
     (expression? v)
       (let [^Expression v v]
         (unify s (.node u) (.node v)))))

(extend-type mikera.expresso.core.Expression
  IUnifyTerms
   (unify-terms [u v s]
     (unify-with-expression* u v s)))


(defn constant? [^Expression x]
  (not (sequential? (.node x))))

(defn- express-list 
  ([[op & exprs]]
    (cons op (map ex* exprs))))

(defn ex* 
  ([expr]
    (cond 
      ;; an operation with child expressions
      (sequential? expr)
        (let [childs (express-list expr)]
          (Expression. childs 
                      (reduce (fn [s ^Expression x] (into s (.vars x))) #{} (rest childs))))
      ;; a symbol
      (symbol? expr)
        (Expression. expr #{expr})
      ;; else must be a constant
      :else
        (Expression. expr nil))))

(defmacro ex 
  "Constructs an Expression."
  ([expr]
    (ex* expr)))

;; logic stuff

(defn lifto
  "Lifts a function into a core.logic relation."
  ([f]
    (fn [& vs]
      (project [vs] (== (last vs) (apply f (butlast vs)))))))

(def NO_MATCH (Object.))

(defn lifto-with-inverse
  "Lifts a unary function into a core.logic relation."
  ([f g]
    (fn [& vs]
      (let [[x y] vs]
        (conda 
          [(project [x] (== y (if (number? x) (f x) NO_MATCH)))]
          [(project [y] (== x (if (number? y) (g y) NO_MATCH)))])))))

(defn mapo [fo vs rs]
  (conda
    [(emptyo vs) (emptyo rs)]
    [(fresh [v r restvs restrs]
            (conso v restvs vs)
            (conso r restrs rs)
            (fo v r)
            (mapo fo restvs restrs))]))


(defn expo 
  "Creates an expression with the given operator and parameters"
  ([op params exp]
    (== (ex* (cons op params)) exp)))


(defn simplifico 
  "Determines the simplified form of an expression."
  ([a b]
    nil))

(defn resulto 
  "Computes the arithmetical result of an expression. Not relational."
  ([exp v]
    (conda 
      [(pred exp constant? ) (project [exp] (== v (.node ^Expression exp)))]
      [(fresh [op params eparams]
              (expo op params exp)
              (mapo resulto params eparams)
              ((lifto op) eparams v))])))

(defn equivo [a b]
  (let [diff (ex (- a b))]
    (conda 
      [(fresh [s] (== 0 (simplifico s diff)))]
      [(resulto diff 0)])))

(comment
  (run* [q] 
        (fresh [a b]
          (== (ex [+ 2 4]) [a b q] )))
  
  (run* [q]
        (expo + [1 2] q))
  
  (run* [q] (resulto (ex (+ 2 3)) q))
  
  )