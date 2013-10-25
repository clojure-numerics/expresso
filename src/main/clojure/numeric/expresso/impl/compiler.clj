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
   (rule (ex (* ?a ?b)) :=> 0)
   (rule (ex (+ ?a 0)) :=> 0)
   (rule (ex (* 0 ?a)) :=> 0)
   (rule (ex (* 1 ?a)) :=> 1)
   (rule (ex (* ?a (+ ?b ?c))) :=> 0)])

(def pats (map first
               [(rule (ex (+ ?a ?b)) :=> 0)
                (rule (ex (* ?a ?b)) :=> 0)
                (rule (ex (+ ?a 0)) :=> 0)
                (rule (ex (* 0 ?a)) :=> 0)
                (rule (ex (* 1 ?a)) :=> 1)
                (rule (ex (* ?a (+ ?b ?c))) :=> 0)]))

(ns-unmap *ns* 'to-decision-tree)
(defn to-decision-tree [pats]
  (cev `or (map #(cev `and (concat %1 [%2])) (map to-constraints pats) (range))))
  


(def dt-rules
  [(rule (ex (and ?&*1 (and ?&*2) ?&*3)) :=> (ex (and ?&*1 ?&*2 ?&*3)))
   (rule (ex (or ?&*1 (or ?&*2) ?&*3)) :=> (ex (or ?&*1 ?&*2 ?&*3)))
   (rule (ex (and ?x)) :=> ?x)
   (rule (ex (or ?x)) :=> ?x)
   (rule (ex (or ?&*0 (and ?x ?&*1) ?&*4 (and ?x ?&*2) ?&*3))
         :=> (ex (or ?&*0 ~?&*4 (and ~?x (or (and ~?&*1) (and ~?&*2))) ~?&*3)))])


(defmulti compile-pattern #(if (sequential? %) (first %) %))
(defmethod compile-pattern :default [x]
   `(== ~'q ~x))

(defn compile-path [p]
  `[~@p])
(defmethod compile-pattern 'symbol [[_ path eq]]
  `(== (let [~'s (utils/get-in-expression ~'expr ~(compile-path path))]
           (and (sequential? ~'s) (first ~'s))) ~(list 'quote eq)))

(defmethod compile-pattern '== [[_ path eq]]
  `(== (utils/get-in-expression ~'expr ~(compile-path path)) ~eq))

(defmethod compile-pattern 'count [[_ path  eq]]
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


(defn rules-to-code [rules]
  (->> rules
       walk/macroexpand-all
       (map first)
       (#(do (prn %) %))
       to-decision-tree
       (transform-expression dt-rules)
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