(ns numeric.expresso.solve
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is log] :as l]
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

(declare check-solution)
(declare contains-expr?)
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

(defn rearrange-to-position [equation pos]
  (loop [sols [(vec (rest (if (= (first pos) 1)
                              (swap-sides equation) equation)))]
           pos (subvec pos 1)]
      (if (seq pos)
        (recur (mapcat (fn [[lhs rhs]]
                         (rearrange-step lhs (first pos) rhs)) sols)
               (rest pos))
        (map (fn [[lhs rhs]] (ce `= lhs rhs)) sols))))

(defn rearrange [v equation]
  (assert (only-one-occurrence v equation)
          "cant rearrange an equation with multiple occurrences of the variable")
  (if-let [pos (position-in-equation v equation)]
    (rearrange-to-position equation pos)
    [equation]))

(def simplify-eq (fn [eq] (ce `= (simp-expr (nth eq 1))  (nth eq 2))))

(def simplify-rhs (fn [eq] (ce `= (nth eq 1) (simp-expr (nth eq 2)))))

(defn lhs-rhs=0 [equation]
  (ce `= (ce `- (nth equation 1) (nth equation 2)) 0))

(defn to-poly-nf [v equation]
  (ce `= (poly-in-x v (nth equation 1)) (nth equation 2)))

(def ^:dynamic *treshold* 1e-6)

(defn num= [a b]
  (or (= a b) (and (number? a) (number? b)
                   (or (clojure.core/== a b)
                       (< (- (Math/abs ^double a)
                             (Math/abs ^double b)) *treshold*)))))

(defn report-res [v eq]
  (if (not (seq? eq))
    (report-res v (ce '= v eq))
    (if (= '() eq)
      eq
      (if (= (nth eq 1) v)
        (if (number? (nth eq 2))
          (when-not (Double/isNaN (nth eq 2)) (nth eq 2))
          (nth eq 2))
        (if (and (no-symbol (nth eq 1)) (no-symbol (nth eq 2)))
          (if (num= (evaluate (nth eq 1) {}) (evaluate (nth eq 2) {}))
            '_0
            '())
          (nth eq 2))))))

(defn check-if-can-be-solved [v eq]
  (when (only-one-occurrence v eq) eq))


(declare solve* solve-by-simplification-rules solve-by-homogenization
         solve-by-strategy)

(defn solve-factors [v factors]
  (->> (mapcat #(solve* v (ce `= % 0)) (matcher-args factors))
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
          [(ce `= v (ex' (/ (+ (- b) (sqrt (- (** b 2) (* 4 a c)))) (* 2 a))))
           (ce `= v (ex' (/ (- (- b) (sqrt (- (** b 2) (* 4 a c)))) (* 2 a))))])))

(defn solve-polynomial [x polyeq]
  (when-let [poly (poly-in-x x (to-poly-normal-form
                                (transform-expression
                                 eval-rules (nth polyeq 1))))]
    (let [vs (vars poly)
          deg (degree poly)]
      (if (vs x)
        (cond
         (= deg 1) (solve-by-simplification-rules
                    x (ce '= (to-expression (to-sexp poly)) 0))
         (= deg 2) (solve-quadratic x poly)
         :else (let [factors (ratio-root poly)]
                 (and (every? #(<= (degree %) 2) factors)
                      (map #(ce '= x %) (mapcat #(solve* x (ce '= % 0))
                                                factors)))))))))
  
(defn solve-by-simplification-rules [v expr]
  (some->> expr
       simplify-eq
       (check-if-can-be-solved v)
       (rearrange v)
       (map simplify-rhs)))
       

(def solve-rules
  [(rule [?v (ex (= (* ?&*) 0))] :==> (solve-factors ?v ?&*))
   (rule [?v ?x] :==> (solve-polynomial ?v ?x))
   (rule [?v ?x] :==> (solve-by-simplification-rules ?v ?x))
   (rule [?v ?x] :==> (solve-by-homogenization ?v ?x))
   (rule [?v ?x] :==> (solve-by-strategy ?v ?x))])

(defn apply-solve-rules [v expr]
  (let [res (apply-rules solve-rules [v expr])]
    (when (not= res [v expr])
      res)))

(defn report-solution [v sols]
  (if sols
    (->> sols
         (mapv #(report-res v %))
         (filter identity)
         (remove #{'()})
         (into #{})
         (#(if (some #{'_0} %)
             '_0
             %)))))
       
(defn solved? [v equation]
  (and (= (nth equation 1) v)
       (not= v (nth equation 2))
       (= 0 (->> (nth equation 2) flatten (filter #{v}) count))))

(defn transform-one-level-lhs [rules eq]
  (ce `= (transform-one-level rules (nth eq 1)) (nth eq 2)))

(def ^:dynamic *solve-attempts*)
(def ^:dynamic *symbolv*)

(defn solve [v equation]
  (binding [*solve-attempts* (atom #{})
            *symbolv* (gensym "var")]
    (solve* v equation)))

(defn check-if-was-solved [v equation]
  (if (not (and (bound? #'*symbolv*) (bound? #'*solve-attempts*)))
    equation
    (let [eq (substitute-expr equation {v *symbolv*})]
      (when-not (some #{eq} @*solve-attempts*)
        (swap! *solve-attempts* #(set/union % #{eq}))
        equation))))

(defn solve* [v equation]
  (if (solved? v equation)
    (report-solution v [(simplify-rhs equation)])
    (some->> equation
             (check-if-was-solved v)
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

(defmethod rearrange-step-function 'tan [[op args pos rhs]]
  (unary-rearrange-step 'tan 'arctan args rhs))

(defmethod rearrange-step-function 'arctan [[op args pos rhs]]
  (unary-rearrange-step 'arctan 'tan args ))

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
    [[(second args) (ce '/ (ce 'log rhs) (ce 'log (first args)))]]))

(defmethod rearrange-step-function 'sqrt [[op args pos rhs]]
  [[(first args) (ce '** rhs 2)]])

(defmethod rearrange-step-function 'abs [[op args pos rhs]]
  [[(first args) rhs]
   [(first args) (ce '- rhs)]])
                                        ;(sem-substitute expr compount-term new-var)

(def ^:dynamic ito)

(construct-with [+ * ** exp log / - sin cos]

(def sem-rewrite-rules
  [(rule [(** ?a (* ?x ?&+)) (** ?a ?x)]
         :=> (** (** ?a ?x) (* ?&+)))
   (rule [(** ?a (- ?x)) (** ?a ?x)]
         :=> (/ (** ?a ?x)))
   (rule [(** ?a (+ ?x ?&*)) (** ?a ?x)]
         :=> (* (** ?a ?x) (** ?a (+ ?&*))))
   (rule [(** ?a ?x) (exp ?x)]
         :=> (exp (* ?x (log ?a))))
   (rule [(** ?a (* ?x ?&*)) (exp ?x)]
         :=> (exp (* (log ?a) ?&*)))
   (rule [(exp (+ ?x ?&*)) (exp ?x)]
         :=> (* (exp ?x) (exp (+ ?&*))))
   (rule [(exp (* ?x ?&+)) (exp ?x)]
         :=> (** (exp ?x) (* ?&+)))
   (rule [(exp (- ?x)) (exp ?x)]
         :=> (/ (exp ?x)))
   (rule [(** ?x ?b) (** ?x ?c)]
         :==> (** (** ?x ?c) (clojure.core// ?b ?c))
         :if (guard (and (number? ?b) (number? ?c) (> ?b ?c))))
   (rule [(** (sin ?x) 2) (cos ?x)]
         :=> (- 1 (** (cos ?x) 2)))
   (rule [(** (cos ?x) 2) (sin ?x)]
         :=> (- 1 (** (sin ?x) 2)))]))


(defn rewrite-in-terms-of [expr x]
  (transform-expression
   (with-meta
     (concat arity-rules
             [(rule ?x :==> (let [res (apply-rules sem-rewrite-rules [?x x])]
                              (when-not (= res [?x x]) res)))])
     {:id :rewrite-in-terms-of-rules})
   expr))

(defn sem-substitute [expr old new]
  (-> expr
      (rewrite-in-terms-of old)
      (substitute-expr {old new})))

(defn offenders [x  expr]
  (apply-rules
   [(rule (ex (+ ?&*)) :==> (mapcat #(offenders x %) (matcher-args ?&*)))
    (rule (ex (* ?&*)) :==> (mapcat #(offenders x %) (matcher-args ?&*)))
    (rule (ex (- ?&*)) :==> (mapcat #(offenders x %) (matcher-args ?&*)))
    (rule (ex (/ ?a ?b)) :==> (offenders x ?a) :if
          (guard (is-number? ?b)))
    (rule (ex (** ?a ?b)) :==> (offenders x ?a) :if
          (guard (is-number? ?b)))
    (rule ?x :=> [] :if (guard (is-number? ?x)))
    (rule ?x :=> [?x])]
   expr))


(def substitution-candidate-heuristics
  [#_(fn [x offenders]
     (and (= (count offenders) 1)
          (= (expr-op (first offenders)) 'log)
          (not= (nth (first offenders) 1) x)
          (nth (first offenders) 1)))
   #_(fn [x offenders]
     (and (= (count offenders) 1)
          (= (expr-op (first offenders)) '**)
          (not= (nth (first offenders) 2) x)
          (nth (first offenders) 2)))
   (fn [x eq offenders]
     (and (every? #(= (expr-op %) '**) offenders)
          (every? #{(second (first offenders))} (map second offenders))
          (ce '** (second (first offenders)) x)))
   (fn [x eq offenders]
     (and (every? #(= (expr-op %) 'exp) offenders)
          (ce 'exp x)))
   (fn [x eq offenders]
     (and (every? #(= (expr-op %) 'sin) offenders)
          (every? #{(second (first offenders))} (map second offenders))
          (ce 'sin (second (first offenders)))))
   (fn [x eq offenders]
     (and (every? #(or (= (expr-op %) 'cos)
                       (= (expr-op %) 'sin)
                       (and
                        (= (expr-op %) '**)
                        (num= (nth % 2) 2)
                        (or (= (expr-op (nth % 1)) 'sin)
                            (= (expr-op (nth % 1)) 'cos)))) offenders))
     (if (contains-expr? eq (rule (ex (** (sin ?x) 2)) :=> true))
       (ex (cos x))
       (if (contains-expr? eq (rule (ex (** (cos ?x) 2)) :=> true))
         (ex (sin x))
         (some (fn [x] (if (= (expr-op x) 'sin) 'sin
                           (if (= (expr-op x) 'cos) 'cos))) offenders))))
   (fn [x eq offenders ]
     (let [off (map #(poly-in-x x %) offenders)]
       (and (every? identity off)
            (let [m (apply max (map degree off))]
              (when (> m 2)
                (ce '** x (if (> (- m 2) 1) (- m 2) (- m 1))))))))])
   

(defn substitution-candidates [x equation offenders]
  (filter identity (map #(%1 x equation offenders)
                        substitution-candidate-heuristics)))

(defn solve-by-substitution [x lhs subs]
  (if subs
    (let [v (gensym "var")
          sols (solve* v (ce '= (sem-substitute lhs subs v) 0))]
        (if sols
          (into #{}
                (map #(ce '= x %) (mapcat #(solve* x (ce '= subs %)) sols)))))))
  

(defn solve-by-homogenization [x equation]
  (let [lhs (second equation)
        subs (->> lhs (offenders x ) (substitution-candidates x equation) first)]
    (solve-by-substitution x lhs subs)))
(defn multiply-equation [eq factor]
  (ce '= (ce '* (nth eq 1) factor) (ce '* (nth eq 2) factor)))

(defn positions-of-x
  ([v equation] (positions-of-x v equation []))
  ([v equation pos]
     (if-let [op (expr-op equation)]
       (filter identity
               (mapcat #(positions-of-x v %1 (conj pos %2))
                       (rest equation) (range)))
       (if (= v equation) [pos] nil))))

(defn common-prefix [positions]
  (let [minl (apply min (map count positions))]
    (loop [l minl]
      (if (> l 0)
        (if (every? #{(subvec (first positions) 0 l)}
                    (map #(subvec % 0 l) (rest positions)))
          (subvec (first positions) 0 l)
          (recur (dec l)))
        []))))

(defn surrounded-by [equation pos rule]
  (loop [n (count pos)]
    (if (> n 0)
      (if-let [res (apply-rule rule (utils/get-in-expression equation
                                                             (subvec pos 0 n)))]
        [res (subvec pos 0 n)]
        (recur (dec n))))))

(defn solve-logarithms [x eq]
  (loop [equation (transform-expression log-solve-rules eq) i 0]
    (prn "equation " equation)
    (if (< i 5)
      (let [positions (positions-of-x x equation)
            r (rule (ex (log ?x)) :=> ?x)
            log (some #(surrounded-by equation % r) positions)]
        (if-let [[x pos] log]
          (let [rearr (first (rearrange-to-position equation pos))]
            (recur (transform-expression
                    log-solve-rules
                    (ce '= (ce 'exp (nth rearr 1)) (ce 'exp (nth rearr 2))))
                   (inc i)))
          (set (filter #(check-solution x eq %) (solve* x equation))))))))

(defn solve-square-roots [x equation]
  (let [positions (positions-of-x x equation)
        r (rule (ex (sqrt ?x)) :=> true)]
    (loop [sqrts (filter identity (map #(surrounded-by equation % r) positions))
           equation equation i 0]
      (if (and (empty? sqrts) (< i 10))
            (solve* x equation)
        (let [[_ pos] (first sqrts)
              rearr (first (rearrange-to-position equation pos))
              new-equation (transform-expression
                            (with-meta square-solve-rules {:id 'morssqrt})
                            (ce '= (ce '** (nth rearr 1) 2)
				       (ce '** (nth rearr 2) 2)))]
          (recur (filter identity (map #(surrounded-by new-equation % r)
                                       (positions-of-x x new-equation)))
                 new-equation (inc i)))))))

(defn square-number [a]
  (let [sq (Math/sqrt ^long a)]
    (num= sq (Math/floor sq))))

(def fraction-rules
  (construct-with [+ - * / **]
    (concat universal-rules
            to-inverses-rules
            eval-rules
            [(rule (/ (* ?&*)) :==> (* (map-sm #(/ %) ?&*)))
             (rule (/ (+ (** ?x 2) ?a))
                   :==> (let [sqrt (long (Math/sqrt ^long (clojure.core/- ?a)))]
                          (* (/ (+ ?x sqrt)) (/ (- ?x sqrt))))
                   :if (guard (and (integer? ?a) (< ?a 0)
                                   (square-number (clojure.core/- ?a)))))])))


(def cancel-fraction-rules
  (construct-with [+ - * / **]
    (concat universal-rules
            to-inverses-rules
            eval-rules
            [(rule (* (+ ?&*1) ?&*2) :==>  (+ (map-sm #(* ?&*2 %) ?&*1)))
             (rule (* ?x (/ ?x) ?&*) :=> (* ?&*))])))

(defn rdf [frac]
  (into #{}
        (map (fn [x] [x (:pos (meta x))])
             (into #{} (map #(with-meta (first %) {:pos (second %)}) frac)))))

(declare multiply-equation)
(defn solve-fractions [x equation]
  (loop [equation (transform-expression fraction-rules equation)]
    (let [positions (positions-of-x x equation)
          r (rule (ex (/ ?x)) :=> ?x)
          frac (filter identity (map #(surrounded-by equation % r) positions))
          varmap (into {} (map (fn [[exp pos]] [exp (gensym "var")]) frac))
          symbal (doall (map  (fn [frac] [(get varmap (first frac)) frac])
                              (into #{} frac)))
          rsymbm (into {} (map (fn [[k v]] [k (first v)]) symbal))
          symbm (into {} (map (fn [[x y]] [(concat (second y) [0]) x]) symbal))
          factor (cev '* (into #{} (map first symbal)))
          wof (as-> equation x
                    (utils/substitute-in-positions x symbm)
                    (multiply-equation x factor)
                    (transform-expression cancel-fraction-rules x)
                    (substitute-expr x rsymbm))]
      (when-not (some #(surrounded-by wof % r) (positions-of-x x wof))
        (into #{} (filter #(check-solution x equation %)
                                        (solve* x wof)))))))

(defn solve-abs [x equation]
  (let [positions (positions-of-x x equation)
        r (rule (ex (abs ?x)) :=> true)
        sb (some #(surrounded-by equation % r) positions)]
    (loop [equations [equation]]
      (if (some (fn [eq] (some #(surrounded-by eq % r) (positions-of-x x eq)))
                equations)
        (recur
         (mapcat (fn [eq]
                   (if-let [[_ pos] (some #(surrounded-by eq % r)
                                    (positions-of-x x eq))]
                     (let [abs (utils/get-in-expression eq pos)]
                       [(substitute-expr eq {abs (nth abs 1)})
                        (substitute-expr eq {abs (ce '- (nth abs 1))})])
                     [eq])) equations))
        (set (filter #(check-solution x equation %) (mapcat #(solve* x %)
                                                            equations)))))))
  
(def strategy-choose-heuristics
  [(fn [positions equation]
     (if (> (count positions) 1)
       (let [cs (common-prefix positions)]
         (if (> (count cs) 2)
           (let [s (utils/get-in-expression equation cs)]
             (fn [x eq]
               (solve-by-substitution x (nth eq 1) s)))))))
   (fn [positions equation]
     (let [r (rule (ex (sqrt ?x)) :=> true)]
       (if (some #(surrounded-by equation % r) positions)
         solve-square-roots)))
   (fn [positions equation]
     (let [r (rule (ex (abs ?x)) :=> true)]
       (if (some #(surrounded-by equation % r) positions)
         solve-abs)))
   (fn [positions equation]
     (let [r1 (rule (ex (/ ?x)) :=> ?x)
           r2 (rule (ex (/ ?x ?y)) :=> true)]
       (if (or (some #(surrounded-by equation % r1) positions)
               (some #(surrounded-by equation % r2) positions))
         solve-fractions)))
   (fn [positions equation]
     (let [r (rule (ex (ln ?x)) :=> ?x)]
       (if (some #(surrounded-by equation % r) positions)
         solve-logarithms)))
   ])


(defn position-strategy [positions equation]
  (some identity (map #(%1 positions equation) strategy-choose-heuristics)))

(defn solve-by-strategy [x equation]
  (let [positions (positions-of-x x equation)
        strategy (position-strategy positions equation)]
    (if strategy
      (strategy x equation))))


(defn check-solutions [x equation solutions]
  (map #(solve* (gensym "var") (substitute-expr equation {x %1})) solutions))

(defn check-solution [x equation solution]
  (try 
    (let [res 
          (if-let [x (solve* (gensym "var")
                            (substitute-expr equation {x solution}))]
            (not (= x #{})))]
      res)
    (catch Exception e nil)))


(defn gcd [m n]
  (loop [m (long m) n (long n)]
    (if (> n 0)
      (recur n (rem m n))
      m)))
(declare common-factors)
(construct-with [* + - / **]
 (def common-factor-rules                 
   [(rule [?m ?n] :==> (gcd (Math/abs ^double ?m) (Math/abs ^double ?n))
         :if (guard (and (integer? ?m) (integer? ?n))))
    (rule [?m ?m] :=> ?m)
    (rule [(** ?a ?m) ?a] :=> ?a)
    (rule [(** ?a ?m) (** ?a ?n)] :==> (** ?a (min ?m ?n))
          :if (guard (and (integer? ?m) (integer? ?n))))
   (rule [(* ?a ?&*1) (* ?a ?&*2)] :==> (* ?a
                                           (common-factors
                                            (utils/splice-in-seq-matchers
                                             (* ?&*1))
                                            (utils/splice-in-seq-matchers
                                             (* ?&*2)))))
   (rule [(* ?a ?&*1) (* ?b ?&*2)] :==> (let [cf (common-factors ?a ?b)]
                                          (when (not (num= cf 1))
                                            (* cf
                                               (common-factors
                                                (utils/splice-in-seq-matchers
                                                 (* ?&*1))
                                                (utils/splice-in-seq-matchers
                                                 (* ?&*2)))))))
   (rule [(* ?a ?&*) ?b] :==> (let [cf (common-factors ?a ?b)]
                                (when (not (num= cf 1))
                                  cf)))
   (rule [?m ?n] :=> 1)])
)

(defn common-factors
  ([a b]
  (let [trans (mapv #(transform-expression (concat universal-rules
                                            eval-rules
                                            simplify-rules) %) [a b])]
    (->> (transform-expression common-factor-rules trans)
         (transform-expression (concat universal-rules eval-rules)))))
  ([a b & more]
     (reduce common-factors (common-factors a b) more)))


(construct-with [+ * / **]
(defn cancel-factor [exp factor]
  (transform-expression
   (concat universal-rules
           to-inverses-rules
           eval-rules
           [(rule [(+ ?&*) ?f] :==>  (map-sm #(/ % ?f) ?&*))
            (rule [(ex (* ?a ~?&*1)) (ex (* ?a ~?&*2))] :=> [(ex (* ~?&*1))
                                                             (ex (* ~?&*2))])
            (rule [(ex (* ?a ~?&*1)) (ex (* ?b ~?&*1))] :==>
                  (let [q (quot ?a ?b)]
                    [(ex (* q ~?&*1)) (ex (* ~?&*1))]))
            (rule [?a ?b] ?a)])
   [exp factor]))
)
(defn factor-poly [polyexp]
  (apply-rule
   (rule (ex (+ ?&+)) :==> (let [cf (apply common-factors (matcher-args ?&+))]
                             (ce '* cf (cancel-factor
                                        (utils/splice-in-seq-matchers
                                         (ce '+ ?&+)) cf))))
   polyexp))


(defn contains-expr? [expr r]
  (or (and (not= expr (apply-rules [r] expr))
           (apply-rules [r] expr))
      (some #{true}
            (flatten (transform-expression [r] expr)))))
