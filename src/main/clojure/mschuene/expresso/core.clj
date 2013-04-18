(ns mschuene.expresso.core
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.logic.unifier :as u]))

(run* [q]
      (fresh [a b] 
             (== [a q b] '(1 2 3))))

(defn expo [op params ex]
  (conso op params ex))
;; (run* [q] (fresh [a b] (expo '+ [a b] q)))
;; => ((+ _0 _1))

(defn inco [a res]
  (project [a]
           (== res (inc a))))

(defn atom? [x] (not (sequential? x)))


(defn mapo [fo vs rs]
  (conda
    [(emptyo vs) (emptyo rs)]
    [(fresh [v r restvs restrs]
            (conso v restvs vs)
            (conso r restrs rs)
            (fo v r)
            (mapo fo restvs restrs))]))
;; (run* [q] (mapo inco [1 2] q))

(defn resulto 
  "Computes the arithmetical result of an expression. Not relational."
  ([exp v]
    (conda 
      [(pred exp number? ) (== v exp)]
      [(fresh [op params eparams]
              (expo op params exp)
              (mapo resulto params eparams)
              (project [eparams op] (== v (apply (resolve op) eparams))))])))
;; (run* [q] (resulto 10 q))
;; => 10
;;
;; (run* [q] (resulto [+ 5 6] q))
;; => 11

(defn equivo [a b]
  (resulto [- a b] 0 ))


;; (run* [q] (equivo [+ 4 5] [+ 1 [* 2 4]]))
;; => (_0) ;; success!


(declare no-variablo)

(defn no-variablo [eq]
  (conda
   ((pred eq atom?)  (!= 'x eq))
   ((matche [eq]
            ([[?op ?lhs ?rhs]] (no-variablo ?lhs) (no-variablo ?rhs))))))


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
    
(defn calculo [eq eq1]
  (no-variablo eq)
  (resulto eq eq1))


; A rule is a clause which gets an expression and returns a modified expression
; If a rule is not applicable, it fails
(def simp-rules
  [(rule ['+ 0 x] :=> x)
   (rule ['+ x 0] :=> x)
   (rule ['* 0 x] :=> 0)
   (rule ['* x 0] :=> 0)
   (rule ['* 1 x] :=> x)
   (rule ['* x 1] :=> x)
   calculo
   ])

(defn apply-ruleo [rule equation new-equation]
  (project [rule equation new-equation]
           (rule equation new-equation)))

(defn apply-ruleso [rules equation nequation]
  (matche [rules]
          ([[?r . ?rs]] (conda
                         ((apply-ruleo ?r equation nequation))
                         ((apply-ruleso ?rs equation nequation))))))

(declare simplifyo)

(defn simp-ruleso [expression nexpression]
  (fresh [a]
         (conda
          ((apply-ruleso simp-rules expression a) (simplifyo a nexpression))
          ((== expression nexpression)))))


(defn simplifyo
  "simplifies the expression according to simp-rules"
  [expression nexpression]
  (conda
   ((pred expression atom?) (== nexpression expression))
   ((fresh [a]
          (mapo simplifyo expression a)
          (simp-ruleso a nexpression)))))


                                        ; test cases


(comment
  "simple example"
  (run* [q] (simplifyo '(+ x 0) q))
  ;=> (x)
  "rules are applied recursively"
  (run* [q] (simplifyo '(* x (+ 0 (* 3 (* x 0)))) q))
  ;=> (0)

  "calculate is also just a rule, which checks if there is no variable in expression and calculates it"
  (run* [q] (simplifyo '(+ (* 3 4) (+ (* x 0) 7)) q))
  ;=> (19)
 )
  
  
  

  