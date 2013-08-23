(ns numeric.expresso.solve
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [numeric.expresso.construct]
        [numeric.expresso.properties :as props]
        [numeric.expresso.protocols]
        [numeric.expresso.rules]
        [numeric.expresso.simplify]
        [numeric.expresso.examples]
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


(defn only-one-occurrence [v equation]
  (>= 1 (->> equation flatten (filter #{v}) count)))
                  
(defn position-in-equation
  ([v equation] (position-in-equation v equation []))
  ([v equation pos]
     (if (and (seq? equation) (symbol? (first equation)))
       (some identity (map #(position-in-equation v %1 (conj pos %2))
                           (rest equation) (range)))
       (if (= v equation) pos nil))))

(defn swap-sides [[eq lhs rhs]]
  (list eq rhs lhs))

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

(def simplify-eq (fn [eq] (ce `= (simp-expr (nth eq 1))  (nth eq 2))))

(def simplify-rhs (fn [eq] (ce `= (nth eq 1) (simp-expr (nth eq 2)))))

(defn lhs-rhs=0 [equation]
  (ce `= (ce `- (nth equation 1) (nth equation 2)) 0))

(defn to-poly-nf [v equation]
  (ce `= (poly-in-x v (nth equation 1)) (nth equation 2)))

(defn report-res [v eq]
  (if (= '() eq)
    eq
    (if (= (nth eq 1) v)
      (nth eq 2)
      (if (and (no-symbol (nth eq 1)) (no-symbol (nth eq 2)))
        (if (= (evaluate (nth eq 1) {}) (evaluate (nth eq 2) {}))
          '_0
          '())
        (nth eq 2)))))

(defn check-if-can-be-solved [v eq]
  (assert (only-one-occurrence v eq)
          (str "Couldn't reduce the number of occurrences of " v " to one."))
  eq)


(declare solve solve-by-simplification-rules)

(defn solve-factors [v factors]
  (->> (mapcat #(solve v (ce `= % 0)) (matcher-args factors))
       (map #(ce `= v %))))

(defn solve-constant [v poly]
  (if (number? poly)
    (if (clojure.core/== poly 0)
      [(ex' (= v 0))]
      [])
    ::undetermined))

(defn solve-linear [v poly]
  [(ce `= v (simp-expr (ce '/ (ce '- (coef poly 0)) (coef poly 1))))])

(defn solve-quadratic [v poly]
  (let [a (simp-expr (to-expression (to-sexp (coef poly 2))))
        b (simp-expr (to-expression (to-sexp (coef poly 1))))
        c (simp-expr (to-expression (to-sexp (coef poly 0))))]
    (mapv simp-expr
          [(ce `= v (ex' (/ (+ (- b) (sqrt(- (** b 2) (* 4 a c)))) (* 2 a))))
           (ce `= v (ex' (/ (- (- b) (sqrt(- (** b 2) (* 4 a c)))) (* 2 a))))])))

(defn solve-polynomial [x polyeq]
  (when-let [poly (poly-in-x x (to-poly-normal-form (nth polyeq 1)))]
    (let [vs (vars poly)
          deg (degree poly)]
      (if (vs x)
        (cond
         (= deg 2) (solve-quadratic x poly)
         :else nil)))))
  
(defn solve-by-simplification-rules [v expr]
  (->> expr
       simplify-eq
       (check-if-can-be-solved v)
       (rearrange v)
       (map simplify-rhs)))
       

(def solve-rules
  [(rule [?v (ex (= (* ?&*) 0))] :==> (solve-factors ?v ?&*))
   (rule [?v ?x] :==> (solve-polynomial ?v ?x))
   (rule [?v ?x] :==> (solve-by-simplification-rules ?v ?x))])

(defn apply-solve-rules [v expr]
  (let [res (apply-rules solve-rules [v expr])]
    (when (not= res [v expr])
      res)))

(defn report-solution [v sols]
  (if sols
    (->> sols
         (mapv #(report-res v %))
         (remove #{'()})
         (into #{})
         (#(if (some #{'_0} %)
             '_0
             %)))
    ::could-not-be-solved))
       
(defn solved? [v equation]
  (and (= (nth equation 1) v)
       (not= v (nth equation 2))
       (= 0 (->> (nth equation 2) flatten (filter #{v}) count))))

(defn transform-one-level-lhs [rules eq]
  (ce `= (transform-one-level rules (nth eq 1)) (nth eq 2)))

(defn solve [v equation]
  (if (solved? v equation)
    (report-solution v [(simplify-rhs equation)])
    (->> equation
         lhs-rhs=0
         (transform-one-level-lhs universal-rules)
         (apply-solve-rules v)
         (report-solution v))))    


(defn poly-const [poly]
  (cond (number? poly) poly
        (number? (coef poly 0)) (coef poly 0)
        :else (poly-const (coef poly 0))))

(defn lhs-to-poly [eq]
  (let [lhs (nth eq 1) rhs (nth eq 2)
        polylhs (to-poly-normal-form (ex (- ~lhs ~rhs)))]
    (if polylhs
      (let [const (poly-const polylhs)
            nlhs (to-poly-normal-form (ex (- ~polylhs ~const)))]
        (ex (= ~nlhs ~(* -1 const))))
      nil)))

(defn search-coef [lhs v]
  (cond (number? lhs) 0
        (var= (main-var lhs) v) (when (<= (degree lhs) 1) (coef lhs 1))
        (not (var> (main-var lhs) v)) (search-coef (coef lhs 0) v)
        :else 0))

(defn to-vec [pos-coeffs]
  (->> pos-coeffs (sort-by first) (mapv second)))

(defn collect-params [eq vars]
  (let [lhs (nth eq 1)
        rhs (nth eq 2)]
    (ce `= (to-vec (for [[p v] vars]
                     [p (search-coef lhs v)])) rhs)))

(defn build-matrix [eqs]
  (mapv #(conj (vec (nth %1 1)) (nth %1 2)) eqs))

(defn simp-sols [sols]
  (cond (= '() sols) sols
        (some expr-op sols) (mapv simp-expr sols)
        :else sols))

(defn add-needed-vars [vs eqs]
  (let [eqv (map (fn [a] [a (vars a)]) eqs)
        needed-vars (filter identity
                            (map (fn [a]
                                   (if (some vs (second a))
                                     (set/difference (second a) vs))) eqv))]
    (into #{} (concat vs (apply set/union needed-vars)))))

(defn to-map [vars v]
  (if (empty? v)
    {}
    (into {} (map (fn [[pos var]] [var (nth v pos)]) vars))))
(declare submap)

(defn remove-unneeded-equations [vs eqv]
  (map first (filter #(some vs (second %)) (map (fn [x] [x (vars x)]) eqv))))


(defn check-if-linear [matrix]
  (when (and (not (empty? matrix)) (not (some (comp not number?) (matrix/eseq matrix))))
    matrix))

(defn check-if-poly [v]
  (when-not (some nil? v)
    v))

(defn solve-linear-system
  "solves a system of equations for the variables in the variable vector"
  [vars eqv]
  (let [v (into #{} vars)
        vs (add-needed-vars v eqv)
        vars (into {} (map (fn [a b] [a b]) (range) vs))]
    (some->> eqv
         (map lhs-to-poly)
         check-if-poly
         (remove-unneeded-equations vs)
         (map #(collect-params % vars))
         build-matrix
         check-if-linear
         symb/ff-gauss-echelon
         symb/report-solution
         simp-sols
         (to-map vars)
         (submap v)
         vector
         set)))


(defn not-in-existing-sols [sol-map var-set]
  (into #{} (remove sol-map var-set)))

(defn solve-general-system*
  ([v eqs] (solve-general-system* v eqs [{}]))
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
                                      (let [ss (solve-general-system* r other-eqs sols)]
                                        (for [l sols s ss]
                                          (merge l s))))
                                    existing-sols depends-on)
             res (set (mapcat (fn [os]
               (let [equation-without-deps (substitute-expr
                                            (first equation-containing-v)
                                            os)
                     sol (solve v equation-without-deps)]
                 (for [s sol]
                   (assoc os v s)))) other-sols))]
             res)
           existing-sols)))))

(defn submap [keys m]
  (into {} (reduce (fn [kvs symb]
                     (if (contains? m symb)
                       (conj kvs [symb (get m symb)])
                       kvs)) [] keys)))

(defn remove-dependencies [symbv m]
  (let [symbs (into #{} symbv)]
    (into {}
          (reduce (fn [o [k v]]
                    (if (contains? symbs k)
                      (let [depends-on
                            (set/difference (set/intersection (vars v) symbs)
                                            #{k})]
                        (conj o
                              [k (reduce
                                  (fn [l r]
                                    (-> (substitute-expr l {r (get m r)})
                                        simp-expr))
                                   v depends-on)]))
                      (conj o [k v]))) [] m))))

(defn solve-general-system [symbv eqs]
  (let [eqs (into #{} eqs)]
    (->> (map #(submap (into #{} symbv) %1)
              (reduce (fn [ls r]
                        (if (r (first ls))
                          ls
                          (for[l ls s (solve-general-system* r eqs ls)]
                            (merge l s)))) [{}] symbv))
         (map #(remove-dependencies symbv %))
         (into #{}))))



(defn solve-system [symbv eqs]
  (if-let [erg (solve-linear-system symbv eqs)]
    erg (solve-general-system symbv eqs)))


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
        