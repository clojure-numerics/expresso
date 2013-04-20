(ns numeric.expresso.core
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.logic.unifier :as u]))

(set! *warn-on-reflection* true)
(set! *unchecked-math* true)

(declare ex* mapo resulto)

(defn- express-list 
  ([[op & exprs]]
    (cons op (map ex* exprs))))

(defn ex* 
  ([expr]
    (cond 
      ;; an operation with child expressions
      (sequential? expr)
        (let [childs (express-list expr)]
          childs)
        
      ;; a symbol
      (symbol? expr)
        expr
        
      ;; else must be a constant
      :else
        expr)))

(defmacro ex 
  "Constructs an Expression."
  ([expr]
    `(quote ~(ex* expr))))

;;logic stuff


(defn lifto
  "Lifts a function into a core.logic relation."
  ([f]
    (fn [& vs]
      (fresh [res args]
        (== res (last vs))
        (mapo resulto (butlast vs) args)
        (project [f args]
             (== res (apply f args)))))))

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

(defn expo 
  "Creates an expression with the given operator and parameters"
  ([op params exp]
    (conso op params exp)))

(defn resolve-opo 
  "Resolves an operator to an actual function"
  ([op resolved-fn]
    (fresh []
      (project [op]
           (== resolved-fn @(resolve op)))))) 
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


(defn applyo 
  "Applies a logic function to a set of parameters."
  ([fo params result]
    (fresh []
           (project [params]
             (apply fo (concat params (list result)))))))


(defn resulto 
  "Computes the arithmetical result of an expression. Not relational."
  ([exp v]
    (conda 
      [(pred exp number?) 
       (== v exp)]
      [(pred exp sequential?)
       (fresh [op rop params]
              (expo op params exp)
              (resolve-opo op rop) 
              (applyo (lifto rop) params v))])))


;; (run* [q] (resulto 10 q))
;; => 10
;;
;; (run* [q] (resulto [+ 5 6] q))
;; => 11


(defn without-symbol? [sym expr]
  (cond
    (and (symbol? expr) (= sym expr)) false
    (sequential? expr) (every? #(without-symbol? sym %) expr)
    :else true))

(defn simplifico 
  "Determines the simplified form of an expression."
  ([a b]
    (conda
      [(pred a number?) (== a b)]
      [(resulto a b)]
      [(== a b)])))


(defn equivo [a b]
  (let [diff `(- ~a ~b)]
    (conda 
      [(fresh [s] (== 0 (simplifico s diff)))]
      [(resulto diff 0)])))

(defn rearrangeo 
  "Re-arranges and simplifies an equality expression."
  ([orig res]
    (conde 
      [(fresh [s x simp] 
              (== orig ['= x s]) 
              (simplifico s simp)
              (== res ['= x simp]))])))

(defn expresso 
  "Expresses a symbol as a formula"
  ([sym expr result]
    (fresh [r]
           (rearrangeo expr r)
           (== ['= sym result] r)
           (pred result #(without-symbol? sym %)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; a little proof of concept rule based translator

(def debug-mode nil)

(defmacro debug [vars & message]
  `(project ~vars
            (do (when debug-mode
                  (prn ~@message)) (== 1 1))))

(defn no-variablo [eq]
  (conda
   ((pred eq atom?)  (pred eq number?))
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
   (rule ['- 0 x] :=> x)
   (rule ['- x 0] :=> x)
   (rule ['- x x] :=> 0)
   (rule ['* y ['+ 'x z]] :=> ['+ ['* y 'x] ['* y z]])
   (rule ['* ['+ 'x z] y] :=> ['+ ['* y 'x] ['* y z]])
   (rule ['+ x x] :=> ['* 2 x])
   (rule ['+ ['* y 'x] ['* z 'x]] :=> ['* ['+ z y] 'x])
   (rule ['+ ['* y 'x] ['* 'x z]] :=> ['* ['+ z y] 'x])
   (rule ['+ ['* 'x y] ['* z 'x]] :=> ['* ['+ z y] 'x])
   (rule ['+ ['* 'x y] ['* 'x z]] :=> ['* ['+ z y] 'x])
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
         (debug [x eq] "symb-ino " x eq)
         (conda [(pred eq atom?) (== x eq)]
                [(flato eq feq)
                 (membero x feq)])))


(defn poso [x eq pos]
  (fresh [op lhs rhs]
         (debug [x eq pos] "x " x "eq " eq "pos " pos)
         (conda
          [(pred eq atom?) (debug [] "atom") (== pos 0)]
          [(expo op [lhs rhs] eq) 
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
   (rule [1 ['= ['+ x y] z]] :=> ['= x ['- z y]])
   (rule [2 ['= ['+ y x] z]] :=> ['= x ['- z y]])
   (rule [1 ['= ['* x y] z]] :=> ['= x ['/ z y]])
   (rule [2 ['= ['* y x] z]] :=> ['= x ['/ z y]])
   (rule [1 ['= ['- x y] z]] :=> ['= x ['+ z y]])
   (rule [2 ['= ['- y x] z]] :=> ['= ['- 0 x] ['- z y]])
   ])

(defn isolato [eq pos neq]
  (fresh []
  (debug [eq pos] "eq " eq "pos " pos)
  (matcha [pos]
          ([0] (debug [] "rest ist " ) (fresh [op lhs rhs nrhs nlhs]
                                              (expo op [lhs rhs] eq)
                                              (simplifyo rhs nrhs)
                                              (simplifyo lhs nlhs)
                                              (expo op [nlhs nrhs] neq)))
          ([(y . x)] (fresh [a req]
                            (debug [y x] "y " y "x " x)
                           (== a [y eq])
                           (apply-ruleso isolate-rules a req)
                           (isolato req x neq))))))

(defn solve-diffo [eq symb neq]
  (fresh [ rpos pos fpos]
         (poso symb eq rpos)
         (debug [rpos] "rpos ist " rpos)
         (conso fpos pos rpos)
        ; (resto rpos pos)
         (isolato eq pos neq)))


(defn solveo [eq symb neq]
  (fresh [a lhs rhs seq]
         (expo '= [lhs rhs] eq)
         (== a ['= ['- lhs rhs] 0])
         (simplifyo a seq)
         (solve-diffo seq symb neq)))