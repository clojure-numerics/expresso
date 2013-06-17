(ns numeric.expresso.solve
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd]
    ;        [clojure.core.logic.unifier :as u]
            [numeric.expresso.utils :as utils]
            [numeric.expresso.construct :as c]
            [numeric.expresso.rules :as r]))

(defn atom? [x] (not (sequential? x)))

(declare lifto)
(defn resulto 
  "Computes the arithmetical result of an expression. Not relational."
  ([exp v]
    (conda 
      [(pred exp number?) 
       (== v exp)]
      [(pred exp sequential?)
       (fresh [op rop params]
              (c/expo op params exp)
              (utils/resolve-opo op rop) 
              (utils/applyo (lifto rop) params v))])))

(defn lifto
  "Lifts a function into a core.logic relation."
  ([f]
    (fn [& vs]
      (fresh [res args]
        (== res (last vs))
        (utils/mapo resulto (butlast vs) args)
        (project [f args]
             (== res (apply f args)))))))





(defn no-variablo [eq]
  (conda
   ((pred eq atom?)  (pred eq number?))
   ((matche [eq]
            ([[?op ?lhs ?rhs]] (no-variablo ?lhs) (no-variablo ?rhs))))))



(defn calculo [eq eq1]
  (no-variablo eq)
  (resulto eq eq1))


; A rule is a clause which gets an expression and returns a modified expression
; If a rule is not applicable, it fails
(def simp-rules
  [(r/rule ['+ 0 x] :=> x)
   (r/rule ['+ x 0] :=> x)
   (r/rule ['* 0 x] :=> 0)
   (r/rule ['* x 0] :=> 0)
   (r/rule ['* 1 x] :=> x)
   (r/rule ['* x 1] :=> x)
   (r/rule ['- 0 x] :=> x)
   (r/rule ['- x 0] :=> x)
   (r/rule ['- x x] :=> 0)
   (r/rule ['* y ['+ 'x z]] :=> ['+ ['* y 'x] ['* y z]])
   (r/rule ['* ['+ 'x z] y] :=> ['+ ['* y 'x] ['* y z]])
   (r/rule ['+ x x] :=> ['* 2 x])
   (r/rule ['+ ['* y 'x] ['* z 'x]] :=> ['* ['+ z y] 'x])
   (r/rule ['+ ['* y 'x] ['* 'x z]] :=> ['* ['+ z y] 'x])
   (r/rule ['+ ['* 'x y] ['* z 'x]] :=> ['* ['+ z y] 'x])
   (r/rule ['+ ['* 'x y] ['* 'x z]] :=> ['* ['+ z y] 'x])
   calculo
   ])


(declare simplifyo)

(defn simp-ruleso [expression nexpression]
  (fresh [a]
         (conda
          ((r/apply-ruleso simp-rules expression a) (simplifyo a nexpression))
          ((== expression nexpression)))))


(defn simplifyo
  "simplifies the expression according to simp-rules"
  [expression nexpression]
  (conda
   ((pred expression atom?) (== nexpression expression))
   ((fresh [a]
          (utils/mapo simplifyo expression a)
          (simp-ruleso a nexpression)))))


(declare findo isolateo calc-rhso)



(defn solveo [eq new-eq]
  (fresh [pos neq nneq]
         (findo eq 'x pos)
         (isolateo 'x eq pos neq)
         (calc-rhso neq nneq)
         (== eq new-eq)))

(defn flato
  "non-relational flat"
  [coll flat-coll]
  (fresh []
         (project [coll flat-coll]
                  (== (flatten coll) flat-coll))))

(defn symb-ino [x eq]
  (fresh [feq]
         (utils/debug [x eq] "symb-ino " x eq)
         (conda [(pred eq atom?) (== x eq)]
                [(flato eq feq)
                 (membero x feq)])))


(defn poso [x eq pos]
  (fresh [op lhs rhs]
         (utils/debug [x eq pos] "x " x "eq " eq "pos " pos)
         (conda
          [(pred eq atom?) (utils/debug [] "atom") (== pos 0)]
          [(c/expo op [lhs rhs] eq) 
           (conde
            [(symb-ino x lhs) (fresh [npos]
                                     (poso x lhs npos)
                                     (conso 1 npos pos))]
            [(symb-ino x rhs) (fresh [npos]
                                     (poso x rhs npos)
                                     (conso 2 npos pos))])])))


(defn findo [x eq pos]
  (conda
   [(pred eq atom?) succeed]))


(def isolate-rules
  [
   (r/rule [1 ['= ['+ x y] z]] :=> ['= x ['- z y]])
   (r/rule [2 ['= ['+ y x] z]] :=> ['= x ['- z y]])
   (r/rule [1 ['= ['* x y] z]] :=> ['= x ['/ z y]])
   (r/rule [2 ['= ['* y x] z]] :=> ['= x ['/ z y]])
   (r/rule [1 ['= ['- x y] z]] :=> ['= x ['+ z y]])
   (r/rule [2 ['= ['- y x] z]] :=> ['= ['- 0 x] ['- z y]])
   ])

(defn isolato [eq pos neq]
  (fresh []
  (utils/debug [eq pos] "eq " eq "pos " pos)
  (matcha [pos]
          ([0] (utils/debug [] "rest ist " ) (fresh [op lhs rhs nrhs nlhs]
                                              (c/expo op [lhs rhs] eq)
                                              (simplifyo rhs nrhs)
                                              (simplifyo lhs nlhs)
                                              (c/expo op [nlhs nrhs] neq)))
          ([(y . x)] (fresh [a req]
                            (utils/debug [y x] "y " y "x " x)
                           (== a [y eq])
                           (r/apply-ruleso isolate-rules a req)
                           (isolato req x neq))))))

(defn solve-diffo [eq symb neq]
  (fresh [ rpos pos fpos]
         (poso symb eq rpos)
         (utils/debug [rpos] "rpos ist " rpos)
         (conso fpos pos rpos)
        ; (resto rpos pos)
         (isolato eq pos neq)))


(defn solveo [eq symb neq]
  (fresh [a lhs rhs seq]
         (c/expo '= [lhs rhs] eq)
         (== a ['= ['- lhs rhs] 0])
         (simplifyo a seq)
         (solve-diffo seq symb neq)))