(ns numeric.expresso.solve
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [numeric.expresso.construct]
        [numeric.expresso.properties :as props]
        [numeric.expresso.protocols]
        [numeric.expresso.rules]
        [clojure.test])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [clojure.core.logic.unifier :as u]
            [numeric.expresso.utils :as utils]
            [numeric.expresso.solve :as s]
            [clojure.core.matrix :as matrix]
            [clojure.core.matrix.operators :as mop]
            [numeric.expresso.matcher :as m]
            [numeric.expresso.construct :as c]))


(defn calc-reso [x]
  (fn [res]
    (project [x]
             (== (evaluate x nil) res))))

(defn no-symbol [x]
  (let [res (if (and (sequential? x) (symbol? (first x)))
              (and (exec-func x) (every? no-symbol (rest x)))
              (not (symbol? x)))]
    res))
    
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



(with-expresso [+ - * / numeric.expresso.core/** diff ln sin cos]

(def universal-rules
  [(rule (+) :=> 0)
   (rule (*) :=> 1)
   (rule (+ ?x) :=> ?x)
   (rule (* ?x) :=> ?x)
   (rule (+ 0 ?&*) :=> (+ ?&*))
   (rule (* 0 ?&*) :=> 0)
   (rule (* 1 ?&*) :=> (* ?&*))
   (rule (numeric.expresso.core/** ?x 1) :=> ?x)
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
   [(rule (* ?x ?x ?&*) :=> (* (numeric.expresso.core/** ?x 2) ?&*))
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
  [(rule (* ?x ?x ?&*) :=> (* (numeric.expresso.core/** ?x 2) ?&*))
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
   (rule (numeric.expresso.core/** (* ?&+) ?n) :==> (* (map-sm #(numeric.expresso.core/** % ?n) ?&+)))
   (rule (numeric.expresso.core/** (numeric.expresso.core/** ?x ?n1) ?n2) :==> (numeric.expresso.core/** ?x (clojure.core/* ?n1 ?n2)))
   (rule (numeric.expresso.core/** (+ ?&+) ?n) :==> (multinomial ?n (matcher-args ?&+)))
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
   (rule (diff (/ ?a) ?x) :=> (- (* (diff ?a ?x) (/ (numeric.expresso.core/** ?a 2)))))
   (rule (diff (numeric.expresso.core/** ?a ?n) ?x) :==> (* ?n (numeric.expresso.core/** ?a (clojure.core/- ?n 1)) (diff ?a ?x))
         :if (guard (number? ?n)))
   (rule (diff (ln ?a) ?x) :=> (* (diff ?a ?x) (/ ?a)))
   (rule (diff (sin ?a) ?x) :=> (* (cos ?a) (diff ?a ?x)))
   (rule (diff (cos ?a) ?x) :=> (* (- (sin ?a)) (diff ?a ?x)))
   (rule (diff (numeric.expresso.core/** 'e ?n) ?x) :=> (* (numeric.expresso.core/** 'e ?n) (diff ?n ?x)))
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
               :else (conj ret (ex' (numeric.expresso.core/** ~(nth args i) ~(first index)))))))))

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
    

(with-expresso [+ - * / numeric.expresso.core/**]
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
    (if (= (first expr) `numeric.expresso.core/**)
      [1 (second (rest  expr))]
      (apply (partial ce (first expr)) (map (partial transform-to-coefficients-form v) (rest expr))))
    (if (= v expr) [1 1] [expr 0])))

#_(defn expression? [exp]
  (or (and (sequential? exp) (symbol? (first exp))) (number? exp)))


(defn translate-back [v expr]
  (list* (first expr)
         (walk/postwalk #(if (and (sequential? %) (= (count %) 2) (expression? (first %)) (number? (second %)))
                           (if (= 0 (second %)) (first %)
                               (ex' (* ~(first %) (numeric.expresso.core/** v ~(second %)))))
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
       (transform-to-coefficients-form v)
       (transform-expression transform-to-polynomial-normal-form-rules)
       (#(ce `+ %))
       (apply-rules [(rule (ex (+ (+ ?&*) ?&*r)) :=> (ex (+ ?&* ?&*r)))])
       (translate-back v)
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
       simplify-eq
       (rearrange v)
       simplify-rhs
       (report-res v)))

(defn differentiate [v expr]
  (->> expr
       (transform-expression (concat eval-rules universal-rules to-inverses-rules multiply-out-rules))
       (#(ce 'diff % v))
       (transform-expression diff-rules)
       (transform-expression (concat eval-rules universal-rules))))
