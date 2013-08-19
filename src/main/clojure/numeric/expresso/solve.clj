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
            [clojure.set :as set]
            [numeric.expresso.symbolic :as symb]
            [numeric.expresso.solve :as s]
            [clojure.core.matrix :as matrix]
            [clojure.core.matrix.operators :as mop]
            [numeric.expresso.matcher :as m]
            [numeric.expresso.construct :as c]))
(set! *warn-on-reflection* true)

(defn calc-reso [x]
  (fn [res]
    (project [x]
             (== (evaluate x nil) res))))

#_(defn no-symbol [x]
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
      (cond #_(isa? xs 'e/ca-op)
            (contains? (:properties (meta xs)) :commutative)
            (collabse-arguments-commutative xs args)
            (contains? (:properties (meta xs)) :associative)
            (collabse-arguments-associative xs args)
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



(construct-with [+ - * / ** diff ln sin cos]

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
   (rule (- ?x 0) :=> ?x)
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
   (rule (+ ?x (- ?x) ?&*) :=> (+ ?&*))
   (rule (+ ?x ?x ?&*) :=> (+ (* 2 ?x) ?&*))
   (rule (+ (* ?x ?&*) (- ?x) ?&*2) :=> (+ (* ?x (- ?&* 1)) ?&*2))
   (rule (+ (* ?x ?&*) (* ?x ?&*2) ?&*3) :=> (+ (* ?x (+ ?&* ?&*2)) ?&*3))
   (rule (+ (* ?x ?&*) ?x ?&*2) :=> (+ (* ?x (+ ?&* 1)) ?&*2))
   (rule (- (- ?x)) :=> ?x)
   (rule (* ?x (** ?x ?n) ?&*) :=> (* (** ?x (+ ?n 1)) ?&*))])

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
    

(construct-with [+ - * / **]
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
    (if (= (first expr) '**)
      [1 (second (rest  expr))]
      (apply (partial ce (first expr)) (map (partial transform-to-coefficients-form v) (rest expr))))
    (if (= v expr) [1 1] [expr 0])))

#_(defn expression? [exp]
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
  (<= (count (filter #{v} (flatten expr))) 1))

(def c= =)

(construct-with [+ cons? nth-arg? = - / * mop/+ mop/- mop/* matrix/div]
(def rearrange-rules
  [(rule [(cons? ?p ?ps) (= (+ ?&+) ?rhs)]
         :==> (let [[left x right] (split-in-pos-sm ?&+ ?p)]
                [?ps (= x (- ?rhs left right))]))
   (rule [(cons? ?p ?ps) (= (mop/+ ?&+) ?rhs)]
         :==> (let [[left x right] (split-in-pos-sm ?&+ ?p)]
                [?ps (= x (mop/- ?rhs left right))]))
   (rule [(cons? ?p ?ps) (= (* ?&+) ?rhs)]
         :==> (let [[left x right] (split-in-pos-sm ?&+ ?p)]
                [?ps (= x (/ ?rhs (* left right)))]))
   (rule [(cons? ?p ?ps) (= (mop/* ?&+) ?rhs)]
         :==> (let [[left x right] (split-in-pos-sm ?&+ ?p)]
                [?ps (= x (matrix/div ?rhs (mop/* left right)))]))
   (rule [(cons? ?p ?ps) (= (- ?&+) ?rhs)]
         :==> (if (c= (count-sm ?&+) 1)
                [?ps (= ?&+ (- ?rhs))]
                (let [[left x right] (split-in-pos-sm ?&+ ?p)]
                  [?ps (= x (if (c= ?p 0)
                              (+ ?rhs right)
                              #_(- left right ?rhs)
                              (+ (- ?rhs (first-sm left)) (rest-sm left)
                                 right)))])))
   (rule [(cons? ?p ?ps) (= (mop/- ?&+) ?rhs)]
         :==> (let [[left x right] (split-in-pos-sm ?&+ ?p)]
                [?ps (= x (if (c= ?p 0)
                            (mop/+ ?rhs right)
                            (mop/- left right ?rhs)))]))
   (rule [(cons? ?p ?ps) (= (/ ?&+) ?rhs)]
         :==> (let [[left x right] (split-in-pos-sm ?&+ ?p)]
                [?ps (= x (if (c= ?p 0)
                            (* ?rhs right)
                            (/ left right ?rhs)))]))]))

(defn only-one-occurrence [v equation]
  (>= 1 (->> equation flatten (filter #{v}) count)))
                  
(defn position-in-equation
  ([v equation] (position-in-equation v equation []))
  ([v equation pos]
     (if (and (sequential? equation) (symbol? (first equation)))
       (some identity (map #(position-in-equation v %1 (conj pos %2))
                           (rest equation) (range)))
       (if (= v equation) pos nil))))

(defn swap-sides [[eq lhs rhs]]
  (list eq rhs lhs))

#_(defn rearrange [v equation]
  (assert (only-one-occurrence v equation)
          "cant rearrange an equation with multiple occurrences of the variable")
  (if-let [pos (position-in-equation v equation)]
    (->> (apply-to-end rearrange-rules
                      [(subvec pos 1) (if (= (first pos) 1)
                                        (swap-sides equation)
                                        equation)])
         second)
    equation))

#_(defn rearrange [v equation]
  (assert (only-one-occurrence v equation)
          "cant rearrange an equation with multiple occurrences of the variable")
  (if-let [pos (position-in-equation v equation)]
    (loop [[lhs rhs]
           [(nth (if (= (first pos) 1) (swap-sides equation) equation) 1)
            (nth (if (= (first pos) 1) (swap-sides equation) equation) 2)]
           pos (subvec pos 1)]
      (if (seq pos)
        (recur (rearrange-step lhs (first pos) rhs) (rest pos))
        (ce `= lhs rhs)))
    equation))

(defn rearrange [v equation]
  (assert (only-one-occurrence v equation)
          "cant rearrange an equation with multiple occurrences of the variable")
  (if-let [pos (position-in-equation v equation)]
    (loop [sols [(vec (rest (if (= (first pos) 1)
                              (swap-sides equation) equation)))]
           pos (subvec pos 1)]
      (if (seq pos)
        (recur (mapcat (fn [[lhs rhs]]
                         (rearrange-step lhs (first pos) rhs)) sols)
               (rest pos))
        (map (fn [[lhs rhs]] (ce `= lhs rhs)) sols)))
    [equation]))
(defn simp-expr [expr]
  (->> expr 
       (transform-expression
        (concat eval-rules universal-rules to-inverses-rules
                multiply-out-rules ))
       (transform-expression (concat universal-rules
                                     eval-rules simplify-rules))))
   

(def simplify-eq (fn [eq] (ce `= (simp-expr (nth eq 1))  (nth eq 2))))

(def simplify-rhs (fn [eq] (ce `= (nth eq 1) (simp-expr (nth eq 2)))))


(defn substitute [repl-map expr]
  (walk/postwalk-replace repl-map expr))

(defn lhs-rhs=0 [equation]
  (ce `= (ce `- (nth equation 1) (nth equation 2)) 0))

(defn to-poly-nf [v equation]
  (ce `= (to-polynomial-normal-form v (nth equation 1)) (nth equation 2)))

(defn report-res [v eq]
  (if (= (nth eq 1) v)
    (nth eq 2)
    (if (and (no-symbol (nth eq 1)) (no-symbol (nth eq 2)))
      (if (= (eval (nth eq 1)) (eval (nth eq 2)))
        '_0
        '())
      (nth eq 2))))

(defn check-if-can-be-solved [v eq]
  (assert (only-one-occurrence v eq)
          (str "Couldn't reduce the number of occurrences of " v " to one."))
  eq)

(defn polynomial? [x]
  (not= :error (to-poly-normal-form x)))

(defn solve-factors [factors])

(defn solve-polynomial [poly])

(defn solve-x [v equation])

(def solve-rules
  [(rule (ex (* ?&*)) :==> (solve-factors ?&*))
   (rule ?x :==> (solve-polynomial ?x)
         :if (guard (polynomial? ?x)))])

(defn solve [v equation]
  (if (and (= (nth equation 1) v)
           (not= v (nth equation 2))
           (= 0 (->> (nth equation 2) flatten (filter #{v}) count)))
    (->> [(report-res v (simplify-rhs equation))]
         (remove #{'()})
         (#(if (some #{'_0} %)
             '_0
             %)))
    (->> equation
         lhs-rhs=0
         simplify-eq
         (check-if-can-be-solved v)
         (rearrange v)
         (map simplify-rhs)
         (mapv #(report-res v %))
         (remove #{'()})
         (#(if (some #{'_0} %)
             '_0
             %)))))

(defn differentiate [v expr]
  (->> expr
     ;;  (transform-expression (concat eval-rules universal-rules to-inverses-rules multiply-out-rules))
      ;; (#(ce 'diff % v))
      ;;; (transform-expression diff-rules)
       (#(differentiate-expr % v))
       (transform-expression (concat eval-rules universal-rules
                                     simplify-rules))))


(defn infer-shape-zero-mat [sf x sl]
  (let [series (concat (matcher-args sf) [x] (matcher-args sl))]
    (if (= (count series) 1)
      x
      (let [s (filter identity [(first (shape (first series)))
                                       (last (shape (last series)))])]
        (if (some symbol? series)
          (zero-matrix s)
          (matrix/broadcast 0 s))))))

(defn identity-right-shape [a]
  (let [s (shape a)]
    (cond
     (empty? s) 1
     (symbol? a) (identity-matrix (first s))
     :else (matrix/identity-matrix (first s)))))

(def matrix-simplification-rules
  [(rule (ex (matrix/add (mzero? ?x) ?&*)) :=> (ex (matrix/add ?&*)))
   (rule (ex (matrix/sub ?x ?x)) :==> (let [s (shape ?x)]
                                        (if (symbol? ?x)
                                          (zero-matrix s)
                                          (matrix/broadcast 0 s))))
   (rule (ex (matrix/mul ?&*1 (mzero? ?x) ?&*2))
         :==> (infer-shape-zero-mat ?&*1 ?x ?&*2))
   (rule (ex (matrix/mul ?&*1 (midentity? ?x) ?&*2))
         :=> (ex (matrix/mul ?&*1 ?&*2)))
   (rule (ex (matrix/div ?a ?a)) :==> (identity-right-shape ?a))
   (rule (ex (matrix/mul ?a (matrix/div ?a) ?&*)) :=> (ex (matrix/mul ?&*)))])

(defn simplify-matrix-expression [expr]
  (transform-expression matrix-simplification-rules expr))

#_(-run {:occurs-check true :n false :reify-vars 
         (fn [v s] s) }
        [q] (== q [1 (lvar 'b) 2]))


(defn update-expr [aa l r]
  (-run {:occurs-check true :n false :reify-vars 
         (fn [v s] s) }
        [q] (== l r) (== q aa)))


(def matvec ['a (lvar 'matvecs1 false) (lvar 'matvecs2 false)])

(def matvec2 ['b (lvar 'matvec2s1 false) (lvar 'matvec2s2 false)])

(def r (rule (ex (matrix/mul ~matvec 0 ~matvec2)) :==> [0 (second matvec) (nth matvec2 2)]))


(def x (matrix-symb 'x))
(def y (matrix-symb 'y))
(def res (ex' (matrix/inner-product x y)))

(def res (add-constraint res [== (second (shape x)) 3]))


#_(solve-system [(ex (= (+ x y z) 3))
				      (ex (= (- (* x 5) y z) 2))
				      (ex (= (+ (* 4 z) (* -2 y) y) 1))]
                '[x y z])

(defn poly-const [poly]
  (cond (number? poly) poly
        (number? (coef poly 0)) (coef poly 0)
        :else (poly-const (coef poly 0))))

(defn lhs-to-poly [eq]
  (let [lhs (nth eq 1) rhs (nth eq 2)
        polylhs (to-poly-normal-form (ex (- ~lhs ~rhs)))
        const (poly-const polylhs)
        nlhs (to-poly-normal-form (ex (- ~polylhs ~const)))
        _ (prn "nlhs " nlhs)]
    (ex (= ~nlhs ~(* -1 const)))))

(defn search-coef [lhs v]
  (cond (number? lhs) 0
        (var= (main-var lhs) v) (coef lhs 1)
        (not (var> (main-var lhs) v)) (search-coef (coef lhs 0) v)
        :else 0))

(defn collect-params [eq vars]
  (let [lhs (nth eq 1)
        rhs (nth eq 2)]
    (ce `= (for [v vars]
             (search-coef lhs v)) rhs)))

(defn build-matrix [eqs]
  (mapv #(conj (vec (nth %1 1)) (nth %1 2)) eqs))

(defn simp-sols [sols]
  (cond (= '() sols) sols
        (some expr-op sols) (mapv simp-expr sols)
        :else sols))

(defn add-needed-vars [vars eqs]
  (let [eqv (map (fn [a] [a (vars a)]) eqs)
        needed-vars (filter (fn [a]
                                      (if (some vars (second a))
                                        (set/difference (second a) vars))) eqv)]
    (set/union vars (apply set/union needed-vars))))
        
(defn solve-linear-system
  "solves a system of equations for the variables in the variable vector"
  [eqv vars]
  (let [vars vars ];;(add-needed-vars (into #{} vars) eqv)]
    (->> eqv
         (map lhs-to-poly)
         dbg
         (map #(collect-params % vars))
         (dbg "collected ")
         build-matrix
         dbg
         symb/ff-gauss-echelon
         symb/report-solution
         dbg
         simp-sols)))

(def rres (to-expression '(clojure.core// (clojure.core/+ (clojure.core/- _2) (clojure.core/- (clojure.core// (clojure.core/+ -1 (clojure.core/* -4 _2)) -1)) -3) 1)))

(def F1 (ex (= Y (+ X Z))))
(def F2 (ex (= X [1 2 3])))
(def F3 (ex (= Z (* 2.0 X))))

(defn not-in-existing-sols [sol-map var-set]
  (into #{} (remove sol-map var-set)))

(defn solve-system*
  ([v eqs] (solve-system* v eqs [{}]))
  ([v eqs existing-sols]
     (if (v (first existing-sols))
       existing-sols
       ;;v is variable and eqs set of equations
       (let [eqv (map (fn [a] [a (vars a)]) eqs)
             equation-containing-v (some (fn [a]
                                           (if (contains? (second a) v)
                                             a nil)) eqv)]
         (if equation-containing-v
           (let [depends-on (not-in-existing-sols
                             (first existing-sols)
                             (set/difference (second equation-containing-v)
                                             #{v}))
                 other-eqs (set/difference eqs #{(first equation-containing-v)})
                 other-sols (reduce (fn [sols r]
                                      (let [ss (solve-system* r other-eqs sols)]
                                        (for [l sols s ss]
                                          (merge l s))))
                                    existing-sols depends-on)]
             (mapcat (fn [os]
               (let [equation-without-deps (substitute-expr
                                            (first equation-containing-v)
                                            os)
                     sol (solve v equation-without-deps)]
                 (for [s sol]
                   (assoc os v s)))) other-sols))
           existing-sols)))))

(defn submap [keys m]
  (into {} (reduce (fn [kvs symb]
                      (conj kvs [symb (get m symb)])) [] keys)))

(defn solve-system [symbv eqs]
  (let [eqs (into #{} eqs)]
    (map #(submap (into #{} symbv) %1)
         (reduce (fn [ls r]
                   (for[l ls s (solve-system* r eqs ls)]
                     (merge l s))) [{}] symbv))))

(construct-with [+ * -]
                (def diff-simp-rules
                  (concat eval-rules
                          [(rule (+) :=> 0)
                           (rule (*) :=> 1)
                           (rule (+ ?x) :=> ?x)
                           (rule (* ?x) :=> ?x)
                           (rule (+ 0 ?&*) :=> (+ ?&*))
                           (rule (* 0 ?&*) :=> 0)
                           (rule (* 1 ?&*) :=> (* ?&*))
                           (rule (- 0) :=> 0)
                           (rule (+ ?x (- ?x) ?&*) :=> (+ ?&*))
                           (rule (* (* ?&*) ?&*r) :=> (* ?&* ?&*r))
                           (rule (+ (+ ?&*) ?&*r) :=> (+ ?&* ?&*r))]
                          simplify-rules)))
   #_(rule (- 0 ?x) :=> (- ?x))
   #_(rule (- ?x 0) :=> ?x)
   

(defmethod diff-function '+ [[expr v]]
  (let [args (expr-args expr)]
    (cev '+ (map #(differentiate-expr % v) args))))

(defmethod diff-function '* [[expr v]]
  (let [args (vec (expr-args expr))
        c (count args)]
    (cev '+ (loop [i 0 exprs []]
                   (if (< i c)
                     (recur (inc i)
                            (conj exprs
                                  (cev '* (concat (subvec args 0 i)
                                                       [(differentiate-expr
                                                         (nth args i) v)]
                                                       (subvec args (inc i))))
                                       ))
                      exprs)))
         ))


(defmethod diff-function '- [[expr v]]
  (let [args (vec (expr-args expr))]
    (if (= 1 (count args))
      (ce '- (differentiate-expr (first args) v))
      (differentiate-expr
       (cev '+ (concat [(first args)] (map #(ce '- %) (rest args)))) v))))

(defmethod diff-function '/ [[expr v]]
  (let [args (vec (expr-args expr))]
    (if (= 1 (count args))
      (differentiate-expr (ce '** (first args) -1) v)
      (differentiate-expr
       (cev '* (concat [(first args)] (map #(ce '/ %) (rest args)))) v))))

(defmethod diff-function '** [[expr v]]
  (let [args (vec (expr-args expr))]
    (if (= (count args) 2)
      (if (= (nth args 0) v)
        (ce '* (nth args 1) (ce '** (nth args 0)
                                     (apply-rules eval-rules
                                                  (ce '- (nth args 1) 1)))
                 (differentiate-expr (nth args 0) v))
        (differentiate-expr
         (ce 'exp (ce '* (nth args 1) (ce 'log (nth args 0)))) v))
      (differentiate-expr
       (cev '** (concat [(ce '** (nth args 0) (nth args 1))] (subvec args 2)))
       v))))

(defmethod diff-function 'log [[expr v]]
  (ce '* (ce '/ (second expr)) (differentiate-expr (second expr) v)))

(defmethod diff-function 'sin [[expr v]]
  (ce '* (ce 'cos (second expr)) (differentiate-expr (second expr) v)))

(defmethod diff-function 'cos [[expr v]]
  (ce '* (ce '- (ce 'sin (second expr))) (differentiate-expr (second expr) v)))

(defmethod diff-function 'exp [[expr v]]
  (ce '* (cev 'exp (rest expr)) (differentiate-expr (second expr) v)))



(defn split-in-pos-args [args pos]
  (let [args (vec args)]
    [(subvec args 0 pos) (nth args pos) (subvec args (inc pos))]))


(defmethod rearrange-step-function '+ [[op args pos rhs]]
  (let [[left x right] (split-in-pos-args args pos)]
    [[x (cev '- (concat [rhs] left right))]]))

(defmethod rearrange-step-function '- [[op args pos rhs]]
  (if (= (count args) 1)
    [[(first args) (ce '- rhs)]]
    (let [[left x right] (split-in-pos-args args pos)]
      [[x (if (= pos 0)
           (cev '+ (concat [rhs] right))
           (cev '- (concat left right [rhs])))]])))

(defmethod rearrange-step-function '* [[op args pos rhs]]
  (let [[left x right] (split-in-pos-args args pos)]
    [[x (cev '/ (concat [rhs] left right))]]))

(defmethod rearrange-step-function '/ [[op args pos rhs]]
  (if (= (count args) 1)
    [[(first args) (ce '/ rhs)]]
    (let [[left x right] (split-in-pos-args args pos)]
      [[x (if (= pos 0)
           (cev '* (concat [rhs] right))
           (cev '/ (concat left right [rhs])))]])))


(defn unary-rearrange-step [op invop args rhs]
  [[(first args) (ce invop rhs)]])

(defmethod rearrange-step-function 'sin [[op args pos rhs]]
  (unary-rearrange-step 'sin 'arcsin args rhs))

(defmethod rearrange-step-function 'arcsin [[op args pos rhs]]
  (unary-rearrange-step 'arcsin 'sin args rhs))

(defmethod rearrange-step-function 'cos [[op args pos rhs]]
  (unary-rearrange-step 'cos 'arccos args rhs))

(defmethod rearrange-step-function 'arccos [[op args pos rhs]]
  (unary-rearrange-step 'arccos 'cos args rhs))

(defmethod rearrange-step-function 'exp [[op args pos rhs]]
  (unary-rearrange-step 'exp 'log args rhs))

(defmethod rearrange-step-function 'log [[op args pos rhs]]
  (unary-rearrange-step 'log 'exp args rhs))

(defmethod rearrange-step-function '** [[op args pos rhs]]
  (if (= pos 0)
    (let [nrhs (ce '** rhs (ce '/ (second args)))]
      (if (and (number? (second args)) (even? (second args)))
          [[(first args) nrhs]
           [(first args) (ce '- nrhs)]]
          [[(first args) nrhs]]))
    (rearrange-step (ce 'exp (ce '* (second args) (ce 'log (first args))))
                    pos rhs)))
        