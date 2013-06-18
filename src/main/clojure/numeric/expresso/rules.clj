(ns numeric.expresso.rules
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd]
    ;        [clojure.core.logic.unifier :as u]
            [numeric.expresso.utils :as utils]
            [numeric.expresso.construct :as c]))

(comment syntax ist
         (rule ['+ 0 x] :=> x)
         )

; constructs a simple clause using matche-syntax
(defmacro rule [lhs _ rhs]
  (let [eq (gensym "eq")
        eq1 (gensym "eq1")]
    `(fn [~eq ~eq1]
       (matche [~eq]
               ([~lhs] (== ~eq1 ~rhs))))))
    

(defn apply-ruleo [rule equation new-equation]
  (project [rule equation new-equation]
           (rule equation new-equation)))

(defn apply-ruleso [rules equation nequation]
  (matche [rules]
          ([[?r . ?rs]] (conda
                         ((apply-ruleo ?r equation nequation))
                         ((apply-ruleso ?rs equation nequation))))))
