(ns numeric.expresso.impl.compiler
  (:refer-clojure :exclude [==])
  (:use [numeric.expresso.construct]
        [numeric.expresso.properties]
        [clojure.core.logic]
        [numeric.expresso.protocols]
        [numeric.expresso.impl.pimplementation]
        [numeric.expresso.rules])
  (:require [clojure.walk :as walk]
            [numeric.expresso.utils :as utils]
            [clojure.set :as set]))


(defn get-partial-match [s]
  (:partial-match (:s s)))

(defn set-partial-match [s pm]
  (assoc s :s (assoc (get s :s) :partial-match pm)))

(def r
  [(rule (ex (+ ?a ?b)) :=> 0)
   (rule (ex (* ?a ?b)) :=> 1)
   (rule (ex (+ ?a 0)) :=> 2)
   (rule (ex (* 0 ?a)) :=> 3)
   (rule (ex (* 1 ?a)) :=> 4)
   (rule (ex (* ?a (+ ?b ?c))) :=> 5)])

(def pats (map first
               [(rule (ex (+ ?a ?b)) :=> 0)
                (rule (ex (* ?a ?b)) :=> 1)
                (rule (ex (+ ?a 0)) :=> 2)
                (rule (ex (* 0 ?a)) :=> 3)
                (rule (ex (* 1 ?a)) :=> 4)
                (rule (ex (* ?a (+ ?b ?c))) :=> 5)]))
                        

(ns-unmap *ns* 'to-decision-tree)
(defn to-decision-tree [rules]
  (cev `or (map #(cev `and (concat %1 [['finalize-match %2 %3]]))
                (map (comp to-constraints first) rules) rules (range))))
  

(def dt-rules
  [(rule (ex (and ?&*1 (and ?&*2) ?&*3)) :=> (ex (and ?&*1 ?&*2 ?&*3)))
   (rule (ex (or ?&*1 (or ?&*2) ?&*3)) :=> (ex (or ?&*1 ?&*2 ?&*3)))
   (rule (ex (and ?x)) :=> ?x)
   (rule (ex (or ?x)) :=> ?x)
   (rule (ex (or ?&*0 (and ?x ?&*1) ?&*4 (and ?x ?&*2) ?&*3))
         :=> (ex (or ?&*0 ~?&*4 (and ~?x (or (and ~?&*1) (and ~?&*2))) ~?&*3)))])

(defn ==patho [lhs rhs path]
  (fn [a]
    (when (= lhs rhs)
      (let [pm (get-partial-match a)]
        (set-partial-match a (assoc pm path rhs))))))


(defmulti compile-pattern #(if (sequential? %) (first %) %))
(defmethod compile-pattern :default [x]
   `(fn [~'a] (unify ~'a ~'q (assoc (get-partial-match ~'a) :x ~x))))

(defn compile-path [p]
  `[~@p])
(defmethod compile-pattern 'symbol [[_ path eq]]
  `(== (let [~'s (utils/get-in-expression ~'expr ~(compile-path path))]
           (and (sequential? ~'s) (first ~'s))) ~(list 'quote eq)))

(defmethod compile-pattern '== [[_ path eq]]
  `(==patho (utils/get-in-expression ~'expr ~(compile-path path)) ~eq ~(compile-path path)))

(defmethod compile-pattern 'count [[_ path eq]]
  `(== (let [~'s (utils/get-in-expression ~'expr ~(compile-path path))]
           (and (sequential? ~'s) (count ~'s))) (+ 1 ~eq)))

(defmethod compile-pattern `and [[_ & r]]
  (map compile-pattern r))

(defmethod compile-pattern `or [[_ & r]]
  (let [compiled
        (map (fn [s]
               (let [compiled (compile-pattern s)
                     res (if (seq? (first compiled))
                           compiled (list compiled))]
                 res)) r)]
    `(conde ~@compiled)))

(defn to-constr [lv]
  `(lvar ~(list 'quote (symbol (:name lv))) false))

(defmethod compile-pattern 'finalize-match [[_ rule i]]
  (let [[pat trans guard] rule
        lv-pos (lvar-positions pat)]
    `(all
      ~@(concat (map (fn [[lv pos]]
                       `(== ~(to-constr lv)
                            (utils/get-in-expression ~'expr ~(compile-path pos))))
                     lv-pos)
                [`(check-guardo (nth (nth ~'r ~i) 2))
                 `(apply-transformationo (second (nth ~'r ~i)) ~'q)]))))
      

;;IDEA to avoid issues with core.logics lack of environment trimming add the bindings , then do the transformations and then delete! the bindings again from the substitution
(defn rules-to-code [rules]
  (->> rules
      walk/macroexpand-all
; (map first)
; (#(do (prn %) %))
      to-decision-tree
      (#(do (prn %) %))
      (transform-expression dt-rules)
      (#(do (prn %) %))
       compile-pattern))

(defn compile-rules [rules]
  (let [code (rules-to-code rules)
        c `(fn [~'expr ~'q]
             ~(rules-to-code rules))
        _ (prn c)]
    ;;metadata is evil when there are functions in it
    ;;so strip the metadata here. In future a dedicated
    ;;function should do it so that one doesn't need a reader
    (eval (read-string (str c)))))


(defn test-hacko []
  (fn [a]
    (let [pm (or (get-partial-match a) {})]
      (prn "hi, pm ist " pm)
      (set-partial-match a
                         (assoc pm :succeed-1 "yes")))))

(defn fl [expr q]
  (clojure.core.logic/conde
 ((clojure.core.logic/==
   (clojure.core/let
    [s (numeric.expresso.utils/get-in-expression expr [])]
    (clojure.core/and
     (clojure.core/sequential? s)
     (clojure.core/first s)))
   '+)
  (clojure.core.logic/==
   (clojure.core/let
    [s (numeric.expresso.utils/get-in-expression expr [])]
    (clojure.core/and
     (clojure.core/sequential? s)
     (clojure.core/count s)))
   (clojure.core/+ 1 2))
  (clojure.core.logic/conde
   ((clojure.core.logic/all
     (clojure.core.logic/==
      (clojure.core.logic/lvar '?a false)
      (numeric.expresso.utils/get-in-expression expr [0]))
     (clojure.core.logic/==
      (clojure.core.logic/lvar '?b false)
      (numeric.expresso.utils/get-in-expression expr [1]))
     (numeric.expresso.rules/check-guardo
      (clojure.core/nth (clojure.core/nth r 0) 2))
     (numeric.expresso.rules/apply-transformationo
      (clojure.core/second (clojure.core/nth r 0))
      q)))
   ((numeric.expresso.impl.compiler/==patho
     (numeric.expresso.utils/get-in-expression
 expr [1])
     0
     [1])
    (clojure.core.logic/all
     (clojure.core.logic/==
      (clojure.core.logic/lvar '?a false)
      (numeric.expresso.utils/get-in-expression expr [0]))
     (numeric.expresso.rules/check-guardo
      (clojure.core/nth (clojure.core/nth r 2) 2))
     (numeric.expresso.rules/apply-transformationo
      (clojure.core/second (clojure.core/nth r 2))
      q)))))
 ((clojure.core.logic/==
   (clojure.core/let
    [s (numeric.expresso.utils/get-in-expression expr [])]
    (clojure.core/and
     (clojure.core/sequential? s)
     (clojure.core/first s)))
   '*)
  (clojure.core.logic/==
   (clojure.core/let
    [s (numeric.expresso.utils/get-in-expression expr [])]
    (clojure.core/and
     (clojure.core/sequential? s)
     (clojure.core/count s)))
   (clojure.core/+ 1 2))
  (clojure.core.logic/conde
   ((clojure.core.logic/all
     (clojure.core.logic/==
      (clojure.core.logic/lvar '?a false)
      (numeric.expresso.utils/get-in-expression expr [0]))
     (clojure.core.logic/==
      
(clojure.core.logic/lvar '?b false)
      (numeric.expresso.utils/get-in-expression expr [1]))
     (numeric.expresso.rules/check-guardo
      (clojure.core/nth (clojure.core/nth r 1) 2))
     (numeric.expresso.rules/apply-transformationo
      (clojure.core/second (clojure.core/nth r 1))
      q)))
   ((numeric.expresso.impl.compiler/==patho
     (numeric.expresso.utils/get-in-expression expr [0])
     0
     [0])
    (clojure.core.logic/all
     (clojure.core.logic/==
      (clojure.core.logic/lvar '?a false)
      (numeric.expresso.utils/get-in-expression expr [1]))
     (numeric.expresso.rules/check-guardo
      (clojure.core/nth (clojure.core/nth r 3) 2))
     (numeric.expresso.rules/apply-transformationo
      (clojure.core/second (clojure.core/nth r 3))
      q)))
   ((numeric.expresso.impl.compiler/==patho
     (numeric.expresso.utils/get-in-expression expr [0])
     1
     [0])
    (clojure.core.logic/all
     (clojure.core.logic/==
      (clojure.core.logic/lvar '?a false)
      (numeric.expresso.utils/get-in-expression
 expr [1]))
     (numeric.expresso.rules/check-guardo
      (clojure.core/nth (clojure.core/nth r 4) 2))
     (numeric.expresso.rules/apply-transformationo
      (clojure.core/second (clojure.core/nth r 4))
      q)))
   ((clojure.core.logic/==
     (clojure.core/let
      [s (numeric.expresso.utils/get-in-expression expr [1])]
      (clojure.core/and
       (clojure.core/sequential? s)
       (clojure.core/first s)))
     '+)
    (clojure.core.logic/==
     (clojure.core/let
      [s (numeric.expresso.utils/get-in-expression expr [1])]
      (clojure.core/and
       (clojure.core/sequential? s)
       (clojure.core/count s)))
     (clojure.core/+ 1 2))
    (clojure.core.logic/all
     (clojure.core.logic/==
      (clojure.core.logic/lvar '?a false)
      (numeric.expresso.utils/get-in-expression expr [0]))
     (clojure.core.logic/==
      (clojure.core.logic/lvar '?b false)
      (numeric.expresso.utils/get-in-expression expr [1 0]))
     (clojure.core.logic/==
      (clojure.core.logic/lvar '?c false)
      
(numeric.expresso.utils/get-in-expression expr [1 1]))
     (numeric.expresso.rules/check-guardo
      (clojure.core/nth (clojure.core/nth r 5) 2))
     (numeric.expresso.rules/apply-transformationo
      (clojure.core/second (clojure.core/nth r 5))
      q)))))))