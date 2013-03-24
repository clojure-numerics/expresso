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

(defn unify-with-expression* [^Expression u v s]
   (cond 
     (and (sequential? v) (sequential? (.node u)))
       (loop [ns (.node u) v v s s]
         (if (empty? v)
           s
           (when-let [s (unify s (first v) (first ns))]
             (recur (next ns) (next v) s))))))

(extend-type mikera.expresso.core.Expression
  IUnifyTerms
   (unify-terms [u v s]
     (unify-with-expression* u v s)))


(defn constant? [^Expression x]
  (not (seq? (.node x))))

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

(comment
  (run* [q] 
        (fresh [a b]
          (== (ex [+ 2 4]) [a b q] )))
  
  )