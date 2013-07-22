(ns numeric.expresso.core
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [numeric.expresso.construct]
        [numeric.expresso.rules]
        [clojure.test])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [clojure.core.logic.unifier :as u]
            [numeric.expresso.utils :as utils]
            [numeric.expresso.solve :as s]
            [numeric.expresso.construct :as c]))

(defn ^:dynamic ** [a b]
  (Math/pow a b))

(def disjunctive-normal-form-rules
  (with-expresso [not and or]
    [(rule (not (not ?x)) :=> ?x :syntactical)
     (rule (not (or ?a ?b)) :=> (and (not ?a) (not ?b)) :syntactical)
     (rule (not (and ?a ?b)) :=> (or (not ?a) (not ?b)) :syntactical)
     (rule (and ?a (or ?b ?c)) :=> (or (and ?a ?b) (and ?a ?c)) :syntactical)
     (rule (and (or ?a ?b) ?c) :=> (or (and ?a ?c) (and ?b ?c)) :syntactical)
     (rule (and (and ?a ?b) ?c) :=> (and ?a (and ?b ?c)) :syntactical)
     (rule (or (or ?a ?b) ?c) :=> (or ?a (or ?b ?c)) :syntactical)]))

(with-expresso [and not or]
  (transform-with-rules disjunctive-normal-form-rules
    (or 'a (not (or 'b (and 'c (not 'd)))))))



(with-expresso [+ - * / ** ln diff sin cos]


(defn not-nullo [x]
  (project [x] (== true (!= x 0))))


(defn calc-reso [x]
  (fn [res]
    (project [x]
             (== (eval x) res))))

(defn no-symbol [x]
  (if (and (sequential? x) (symbol? (first x)))
    (and (resolve (first x)) (every? no-symbol (rest x)))
    (not (symbol? x))))

(defn no-symbolso [x]
  (project [x]
           (== true (no-symbol x))))
 
(defn zip [& colls]
  (apply (partial map (fn [& a] a)) colls))

(defn contains-no-var? [x]
  (let [res (if (and (not (symbol? x)) (no-symbol x)) true false)]
    res))

(defn collabse-arguments-commutative [xs args]
  (let [gb (group-by contains-no-var? args)
        fix (concat (gb nil) (gb true))
        var (gb false)]
    (if (or (empty? fix) (< (count fix) 2))
            (list* xs args)
            (list* xs (eval (list* xs fix)) var))))

(defn collabse-arguments-associative [xs args]
  (let [parts (partition-by contains-no-var? args)
        eval-parts (fn [part]
                     (if (and (and (coll? part) (> (count part) 1))
                              (or (= nil (contains-no-var? part)) (contains-no-var? part)))
                       [(eval (list* xs part))]
                       part))
        mc (mapcat eval-parts parts)]
    (list* xs mc)))

(defn compute-subexpression [expr]
  (if (coll? expr)
    (let [[xs & args] expr]
      (cond (isa? xs 'e/ca-op) (collabse-arguments-commutative xs args)
            (isa? xs 'e/ao-op) (collabse-arguments-associative xs args)
            :else expr))
    expr))
                                                        
(defn compute-subexpressiono [x]
  (fn [res]
    (project [x]
             (let [tmp (compute-subexpression x)]
               (if (= tmp x)
                 fail
                 (== res tmp))))))


(defn symbolo [x] (project [x] (== true (symbol? x))))

(def simp-rules
  [(rule ?x :=> (calc-reso ?x) :if (no-symbolso ?x))
   (rule ?x :=> (compute-subexpressiono ?x))
   (rule (+) :=> 0)
   (rule (*) :=> 1)
   (rule (+ ?x) :=> ?x)
   (rule (* ?x) :=> ?x)
   (rule (+ ?&* (+ ?&*1)) :=> (+ ?&* ?&*1))
   (rule (+ 0 ?&*) :=> (+ ?&*))
   (rule (+ ?x ?x ?&*) :=> (+ (* 2 ?x) ?&*))
   (rule (- ?x 0 ?&*) :=> (- ?x ?&*))
   (rule (- 0 ?x) :=> (- ?x))
   (rule (- ?x ?x) :=> 0)
   (rule (- ?x ?&*a ?x ?&*b) :=> (- 0 ?&*a ?&*b))
   (rule (- 0) :=> 0)
   (rule (* ?&* (* ?&*1)) :=> (* ?&* ?&*1))
   (rule (* 1 ?&*) :=> (* ?&*))
   (rule (* 0 ?&*) :=> 0)
   (rule (* ?x ?x ?&*) :=> (* (** ?x 2) ?&*))
   (rule (+ (* ?x ?&*1) (* ?x ?&*2) ?&*) :=> (+ (* ?x (+ ?&*1 ?&*2)) ?&*)
         :if (symbolo ?x))
   (rule (+ (* ?x ?&*1) ?x ?&*) :=> (+ (* ?x (+ ?&*1 1)) ?&*))
   (rule (/ ?x ?&* 0 ?&*a) :=> 'div-by-zero-error :if (not-nullo ?x))
   (rule (/ 0 ?&*) :=> 0)
   (rule (/ ?x ?x) :=> 1)
   (rule (/ ?x ?&* ?x ?&*2) :=> (/ 1 ?&* ?&*2))
   (rule (** 0 0) :=> 'undefined)
   (rule (** ?x 0) :=> 1)
   (rule (** 0 ?x) :=> 0)
   (rule (** 1 ?x) :=> 1)
   (rule (** ?x 1 ) :=> ?x)
   (rule (** ?x -1) :=> (/ 1 ?x))
   (rule (* ?x (/ ?&+ ?x ?&*2) ?&*) :=> (* (/ ?&+ ?&*2) ?&*))
   (rule (/ (* ?x ?&*) ?x) :=> (* ?&*))
   (rule (/ ?x (* ?x ?&*)) :=> (* ?&*))
   (rule (+ ?x (- ?x) ?&*) :=> (+ ?&*))
   (rule (ln 1) :=> 0)
   (rule (ln 0) :=> 'undefined)
   (rule (ln 'e) :=> 1)
   (rule (sin 0) :=> 0)
   (rule (sin 'pi) :=> 0)
   (rule (cos 0) :=> 1)
   (rule (cos 'pi) :=> -1)
   (rule (sin (/ 'pi 2)) :=> 1)
   (rule (cos (/ 'pi 2)) :=> 0)
   (rule (ln (** 'e ?x)) :=> ?x)
   (rule (** 'e (ln ?x)) :=> ?x)
   (rule (* (** ?x ?y) (** ?x ?z) ?&*) :=> (* (** ?x (+ ?y ?z)) ?&*))
   (rule (/ (** ?x ?y) (** ?x ?z)) :=> (** ?x (- ?y ?z)))
   (rule (+ (ln ?x) (ln ?y)) :=> (ln (* ?x ?y)))
   (rule (- (ln ?x) (ln ?y)) :=> (ln (/ ?x ?y)))
   (rule (+ (** (sin ?x) 2) (** (cos ?x) 2) ?&*) :=> (+ 1 ?&*))
   (rule (diff ?x ?x) :=> 1)
   (rule (diff (+ ?u ?v) ?x) :=> (+ (diff ?u ?x) (diff ?v ?x)))
   (rule (diff (+ ?u ?&*) ?x) :=> (+ (diff ?u ?x) (diff (+ ?&*) ?x)))
   (rule (diff (- ?u ?v) ?x) :=> (- (diff ?u ?x) (diff ?v ?x)))
   (rule (diff (- ?u) ?x) :=> (- (diff ?u ?x)))
   (rule (diff (* ?u ?v) ?x) :=> (+ (* (diff ?u ?x) ?v) (* (diff ?v ?x) ?u)))
   (rule (diff (* ?u ?&*) ?x) :=> (+ (* (diff ?u ?x) ?&*) (* (diff (* ?&*) ?x) ?u)))
   (rule (diff (/ ?u ?v) ?x) :=> (/ (- (* (diff ?u ?x) ?v) (* (diff ?v ?x) ?u)) (** ?v 2)))
   (rule (diff (** ?u ?n) ?x) :=> (* ?n (** ?u (- ?n 1)) (diff ?u ?x)))
   (rule (diff (ln ?u) ?x) :=> (/ (diff ?u ?x) ?u))
   (rule (diff (sin ?u) ?x) :=> (* (cos ?u) (diff ?u ?x)))
   (rule (diff (cos ?u) ?x) :=> (* (- (sin ?u)) (diff ?u ?x)))
   (rule (diff (** 'e ?u) ?x) :=> (* (** 'e ?u) (diff ?u ?x)))
   (rule (diff ?u ?x) :=> 0)
   ])
)
(defn simplify [expr]
  (transform-expression simp-rules expr))



(with-expresso [+ - * / ** diff ln sin cos]

(def universal-rules
  [(rule (+) :=> 0)
   (rule (*) :=> 1)
   (rule (+ ?x) :=> ?x)
   (rule (* ?x) :=> ?x)
   (rule (+ 0 ?&*) :=> (+ ?&*))
   (rule (* 0 ?&*) :=> 0)
   (rule (* 1 ?&*) :=> (* ?&*))
   (rule (** ?x 1) :=> ?x)
   (rule (* (* ?&*) ?&*r) :=> (* ?&* ?&*r))
   (rule (+ (+ ?&*) ?&*r) :=> (+ ?&* ?&*r))
   (rule (- 0 ?x) :=> (- ?x))
   (rule (+ (* ?x ?y) (* ?z ?y) ?&*) :=> (+ (* (+ ?x ?z) ?y) ?&*)
         :if (guard (and (number? ?x) (number? ?z))))
   ])

(def eval-rules
  [(rule ?x :=> (calc-reso ?x) :if (no-symbolso ?x))
   (rule ?x :=> (compute-subexpressiono ?x))])
  
(def normal-form-rules
  (concat universal-rules
   [(rule (* ?x ?x ?&*) :=> (* (** ?x 2) ?&*))
   (rule (* ?x (/ ?x) ?&*) :=> (* ?&*))
   (rule (+ (* ?x ?n1) (* ?x ?n2) ?&*) :==>
         (+ (* ?x (clojure.core/+ ?n1 ?n2)) ?&*) :if
         (guard (and (number? ?n1) (number? ?n2))))
   (rule (- ?x ?&+) :=> (trans (+ ?x (map-sm #(- %) ?&+))))
   (rule (/ ?x ?&+) :=> (trans (* ?x (map-sm #(/ %) ?&+))))
   (rule (* (+ ?&+1) (+ ?&+2) ?&*) :==>
         (let [args1 (matcher-args ?&+1)
               args2 (matcher-args ?&+2)]
           (* ?&* (+ (seq-matcher (for [a args1 b args2] (* a b)))))))
   (rule (* (+ ?&+) ?x ?&*) :==>
         (* (+ (seq-matcher (for [a (matcher-args ?&+)] (* a ?x)))) ?&*))]))

(def simplify-rules
  [(rule (* ?x ?x ?&*) :=> (* (** ?x 2) ?&*))
   (rule (* ?x (/ ?x) ?&*) :=> (* ?&*))
   (rule (+ ?x (- ?x) ?&*) :=> (+ ?&*))])

(def to-inverses-rules
  [(rule (- ?x ?&+) :=> (trans (+ ?x (map-sm #(- %) ?&+))))
   (rule (- (+ ?&+)) :==> (+ (map-sm #(- %) ?&+)))
   (rule (- (* ?&+)) :=> (* -1 ?&+))
   (rule (/ ?x ?&+) :=> (trans (* ?x (map-sm #(/ %) ?&+))))])

(declare multinomial)
(def multiply-out-rules
  [(rule (* (+ ?&+1) (+ ?&+2) ?&*) :==>
         (let [args1 (matcher-args ?&+1)
               args2 (matcher-args ?&+2)]
           (* ?&* (+ (seq-matcher (for [a args1 b args2] (* a b)))))))
   (rule (* (+ ?&+) ?x ?&*) :==>
         (* (+ (seq-matcher (for [a (matcher-args ?&+)] (* a ?x)))) ?&*))
   (rule (** (* ?&+) ?n) :==> (* (map-sm #(** % ?n) ?&+)))
   (rule (** (** ?x ?n1) ?n2) :==> (** ?x (clojure.core/* ?n1 ?n2)))
   (rule (** (+ ?&+) ?n) :==> (multinomial ?n (matcher-args ?&+)))
   (rule (* ?x (/ ?x) ?&*) :=> (* ?&*))]
)
(def diff-rules
  [(rule (diff ?x ?x) :=> 1)
   (rule (diff (+ ?&+) ?x) :==> (+ (map-sm #(diff % ?x) ?&+)))
   (rule (diff (* ?&+) ?x) :==>
         (+ (seq-matcher
             (for [i (range (count-sm ?&+)) :let [[bv ith af] (split-in-pos-sm ?&+ i)]]
               (* (diff ith ?x) bv af)))))
   (rule (diff (- ?a) ?x) :=> (- (diff ?a ?x)))
   (rule (diff (/ ?a) ?x) :=> (- (* (diff ?a ?x) (/ (** ?a 2)))))
   (rule (diff (** ?a ?n) ?x) :==> (* ?n (** ?a (clojure.core/- ?n 1)) (diff ?a ?x))
         :if (guard (number? ?n)))
   (rule (diff (ln ?a) ?x) :=> (* (diff ?a ?x) (/ ?a)))
   (rule (diff (sin ?a) ?x) :=> (* (cos ?a) (diff ?a ?x)))
   (rule (diff (cos ?a) ?x) :=> (* (- (sin ?a)) (diff ?a ?x)))
   (rule (diff (** 'e ?n) ?x) :=> (* (** 'e ?n) (diff ?n ?x)))
   (rule (diff ?u ?x) :=> 0)])
)
(defn- binom [n k]
  (let [rprod (fn [a b] (reduce * (range a (inc b))))]
    (/ (rprod (- n k -1) n) (rprod 1 k))))

(defn factorial [n]
  (loop [n (long n) acc (long 1)]
    (if (<= n 1)
      acc
      (recur (- n 1) (* acc n)))))

(defn- multinomial-indices [m n]
  (if (= n 0)
    (list (repeat m 0))
    (if (= m 1)
      (list (list n))
      (for [i (range (inc n))
            j (multinomial-indices (- m 1) (- n i)) ]
        (list* i j)))))

(defn multinomial-coeff [n indices]
  (quot (factorial n) (reduce * (map factorial indices))))

(defn to-factors [args index]
  (loop [i 0 index index ret []]
    (if (= i (count args))
      ret
      (recur (inc i) (rest index)
             (cond
              (= (first index) 0) ret
              (= (first index) 1) (conj ret (nth args i))
               :else (conj ret (ex' (** ~(nth args i) ~(first index)))))))))

(defn multinomial [n args]
  (let [args (vec args)
        m (count args)
        indices (multinomial-indices m n)]
    (ce `+ (seq-matcher (for [index indices]
                          (let [factors (seq-matcher (to-factors args index))
                                coeff (multinomial-coeff n index)]
                            (if (= 1 coeff)
                              factors
                              (ex' (* coeff factors)))))))))
    

(with-expresso [+ - * / **]
  (def transform-to-polynomial-normal-form-rules
    (concat universal-rules
            [(rule (+ [?x ?y] [?z ?y] ?&*)
                   :==> (+ [(+ ?x ?z) ?y] ?&*)
                   :if (guard (and  (number? ?y))))
             (rule (* [?x ?y] [?z ?a] ?&*)
                   :==>  (* [(* ?x ?z) (clojure.core/+ ?y ?a)] ?&*)
                   :if (guard (and (number? ?y)
                                    (number? ?a))))
             (rule (- [?x ?y]) :==> [(- ?x) ?y]
                   :if (guard (and (number? ?y))))
             (rule (/ [?x ?y]) :==>[(/ ?x) ?y]
                   :if (guard (and  (number? ?y))))
             (rule (ce ?op [?x 0]) :=> [(ce ?op ?x) 0])])))

(defn- transform-to-coefficients-form [v expr]
  (if (sequential? expr)
    (if (= (first expr) `**)
      [1 (second (rest  expr))]
      (apply (partial ce (first expr)) (map (partial transform-to-coefficients-form v) (rest expr))))
    (if (= v expr) [1 1] [expr 0])))

(defn expression? [exp]
  (or (and (sequential? exp) (symbol? (first exp))) (number? exp)))


(defn translate-back [v expr]
  (list* (first expr)
         (walk/postwalk #(if (and (sequential? %) (= (count %) 2) (expression? (first %)) (number? (second %)))
                           (if (= 0 (second %)) (first %)
                               (ex' (* ~(first %) (** v ~(second %)))))
                           %) (sort #(> (second %1) (second %2)) (rest expr)))))



(defn dbg
  ([x] (prn x) x)
  ([m x] (prn m x) x))


(defn to-polynomial-normal-form [v expr]
  (->> expr
       (transform-expression (concat eval-rules
                                     universal-rules
                                     to-inverses-rules
                                     multiply-out-rules))
 ;      (dbg "simplified")
       (transform-to-coefficients-form v)
       (transform-expression transform-to-polynomial-normal-form-rules)
  ;     (dbg "poly-form")
       (#(ce `+ %))
       (apply-rules [(rule (ex (+ (+ ?&*) ?&*r)) :=> (ex (+ ?&* ?&*r)))])
       (translate-back v)
   ;    (dbg "translate-back")
       (transform-expression (concat eval-rules
                                     universal-rules
                                     to-inverses-rules
                                     multiply-out-rules))))

(defn only-one-occurrence-of [v expr]
  (= (count (filter #{v} (flatten expr))) 1))

(def c= =)

(with-expresso [+ cons? nth-arg? = - / * ]
(def rearrange-rules
  [(rule [(cons? ?p ?ps) (= (+ ?&+) ?rhs)]
         :==> (let [[left x right] (split-in-pos-sm ?&+ ?p)]
                [?ps (= x (- ?rhs left right))]))
   (rule [(cons? ?p ?ps) (= (* ?&+) ?rhs)]
         :==> (let [[left x right] (split-in-pos-sm ?&+ ?p)]
                [?ps (= x (/ ?rhs (* left right)))]))
   (rule [(cons? ?p ?ps) (= (- ?&+) ?rhs)]
         :==> (let [[left x right] (split-in-pos-sm ?&+ ?p)]
                [?ps (= x (if (c= ?p 0)
                            (+ ?rhs right)
                            (- (+ (- ?rhs (first-sm left))
                                  (rest-sm left) right))))]))
   (rule [(cons? ?p ?ps) (= (/ ?&+) ?rhs)]
         :==> (let [[left x right] (split-in-pos-sm ?&+ ?p)]
                [?ps (= x (if (c= ?p 0)
                            (* ?rhs right)
                            (/ (* (/ ?rhs (first-sm left))
                                  (rest-sm left) right))))]))]))
                  
(defn position-in-equation
  ([v equation] (position-in-equation v equation []))
  ([v equation pos]
     (if (and (sequential? equation) (symbol? (first equation)))
       (some identity (map #(position-in-equation v %1 (conj pos %2))
                           (rest equation) (range)))
       (if (= v equation) pos nil))))

(defn swap-sides [[eq lhs rhs]]
  (list eq rhs lhs))

(defn rearrange [v equation]
  (if-let [pos (position-in-equation v equation)]
    (->> (apply-to-end rearrange-rules
                      [(subvec pos 1) (if (= (first pos) 1)
                                        (swap-sides equation)
                                        equation)])
         second)
    equation))

(defn simp-expr [expr]
  (prn "simp-expr " expr)
  (transform-expression
   (concat eval-rules universal-rules to-inverses-rules
           multiply-out-rules simplify-rules)
   expr))

(def simplify-eq (fn [eq] (ce `= (simp-expr (nth eq 1))  (nth eq 2))))

(def simplify-rhs (fn [eq] (ce `= (nth eq 1) (transform-expression (concat universal-rules eval-rules) (nth eq 2)))))


(defn substitute [repl-map expr]
  (walk/postwalk-replace repl-map expr))

(defn lhs-rhs=0 [equation]
  (ce `= (ce `- (nth equation 1) (nth equation 2)) 0))

(defn to-poly-nf [v equation]
  (ce `= (to-polynomial-normal-form v (nth equation 1)) (nth equation 2)))

(defn report-res [v eq]
  (if (= (nth eq 1) v)
    eq
    (if (and (no-symbol (nth eq 1)) (no-symbol (nth eq 2)))
      (if (= (eval (nth eq 1)) (eval (nth eq 2)))
        '_0
        '())
      eq)))

(defn solve [v equation]
  (->> equation
       lhs-rhs=0
       (dbg "lhs-rhs=0")
   ;    (to-poly-nf v)
       (dbg "poly-nf ")
       simplify-eq
       (dbg "simpl")
       (rearrange v)
       simplify-rhs
       (report-res v)))

(defn differentiate [v expr]
  (->> expr
       (transform-expression (concat eval-rules universal-rules to-inverses-rules multiply-out-rules))
       (dbg "simplified")
       (#(ce 'diff % v))
       (transform-expression diff-rules)
       (dbg "derivatived")
       (transform-expression (concat eval-rules universal-rules))))