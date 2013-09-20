(ns numeric.expresso.solve
  (:refer-clojure :exclude [==])
  (:use [numeric.expresso.construct]
        [numeric.expresso.impl.polynomial]
        [numeric.expresso.protocols]
        [numeric.expresso.properties]
        [numeric.expresso.impl.pimplementation]
        [numeric.expresso.rules]
        [numeric.expresso.simplify])
  (:require [clojure.walk :as walk]
            [numeric.expresso.utils :as utils]
            [clojure.set :as set]
            [numeric.expresso.impl.symbolic :as symb]
            [clojure.core.matrix :as matrix]
            [numeric.expresso.construct :as c]))

(declare contains-expr? positions-of-x surrounded-by check-solution)

;;this is the namespace which implements the solving facility of expresso
;;For code reading, I suggest starting at the solve or the solve-system
;;functions


;;rearrange-to-position is a useful helper function for solving strategies
;;combine-solution is just mapcat.
;;the position is a vector of places which subexpression contains the variable
;;the positions are one lower than usual, because the expression operators
;;are not counted. It uses the rearrange-step function to generate the
;;list of possible partly rearranged equations at each step

(defn rearrange-to-position
  "rearranges the given equation until the part of the equation in pos is the
   left hand side of equation"
  [equation pos]
  (loop [sols [(vec (rest (if (= (first pos) 1)
                              (utils/swap-sides equation) equation)))]
         pos (subvec pos 1)]
      (if (seq pos)
        (recur (utils/combine-solutions
                (fn [[lhs rhs]] (rearrange-step lhs (first pos) rhs)) sols)
               (rest pos))
        (map (fn [[lhs rhs]] (ce `= lhs rhs)) sols))))

;;rearrage fully rearrange the equation for the variable v provided it only
;;occurs in the equation once

(defn rearrange
  "fully rearranges the equation to v provided there is only one occurrence of v
   in the equation"
  [v equation]
  (when (utils/only-one-occurrence v equation)
    (if-let [pos (first (utils/positions-of v equation))]
      (rearrange-to-position equation pos)
      [equation])))

;;report-res is used for the solver to convert the solutions to a suitable
;;output for users. Returns #{} for no solutions and _0 alwaly solved
;;returns nil if the expression couldn't be solved
;;also normalizes the input by nil-ing NaN results and rounding to the nearest
;;integer if appropriate


(defn- report-res
  "normalises the result of eq in regard to v"
  [v eq]
  (cond
   (not (and (seq? eq) (= (expr-op eq) '=))) (report-res v (ce '= v eq))
   (empty? eq) #{}
   (= (utils/eq-lhs eq) v) (let [rhs (utils/eq-rhs eq)]
                             (if (number? rhs)
                               (when-not (Double/isNaN rhs)
                                 (if (utils/num= (utils/round rhs) rhs)
                                   (utils/round rhs) rhs)) rhs))
   :else (let [lhs (utils/eq-lhs eq) rhs (utils/eq-rhs eq)]
           (when (no-symbol eq)
             (if (utils/num= (evaluate lhs {}) (evaluate rhs {})) '_0 '())))))



(declare solve* solve-by-simplification-rules solve-by-homogenization
         solve-by-strategy)

;;following are basic solving strategies. The dispatch to the solving strategies
;;is made by solve-by-rules

;;solve factors is the easiest solving strategy. All it has to do is to solve
;;each factor of the equation and then to combine the solutions
(defn solve-factors
  "solves all factors in regard to v and combines the solutions"[v factors]
  (->> (utils/combine-solutions #(solve* v (ce `= % 0)) factors)
       (map #(ce `= v %))))

;;This is the abc formula used to solve quadratic polynomials. Poly here is
;;an instance of PolynomialExpression. See polynomial.clj for details

(defn solve-quadratic
  "solves the quadratic poly with the abc formula"
  [v poly]
  (let [a (to-expression (to-sexp (coef poly 2)))
        b (to-expression (to-sexp (coef poly 1)))
        c (to-expression (to-sexp (coef poly 0)))]
    (mapv simp-expr
          [(ce `= v (ex' (/ (+ (- b) (sqrt (- (** b 2) (* 4 a c)))) (* 2 a))))
           (ce `= v (ex' (/ (- (- b) (sqrt (- (** b 2) (* 4 a c)))) (* 2 a))))])))

(defn- try-factorise [x poly]
  (let [first-not-null
        (loop [i 0] (if (and (<= i (degree poly))
                             (utils/num= (coef poly i) 0))
                      (recur (inc i)) i))
        common-factor (poly-in 'x (ex (** ~x ~first-not-null)))
        [quot rem] (poly-division poly common-factor)]
    (when (utils/num= 0 rem)
      (solve-factors x [common-factor quot]))))

;;if the lhs of polyeq (rhs=0 here) can be transformed to a polynomial
;;solve the resulting polynomial depending on the degree of the polynomial
;;also fries to factor a polynomial by guessing with ratio-root test

(defn solve-polynomial
  "solves the polynnomial equation in regard to x. tries some effort in
   factorization if the degree of the poly is higher than 2"
  [x polyeq]
  (when-let [poly (poly-in x (transform-expression
                                eval-rules (utils/eq-lhs polyeq)))]
    (let [vs (vars poly)
          deg (degree poly)]
      (when (vs x)
        (cond
         (or (= deg 0) (= deg 1)) (solve-by-simplification-rules
                                   x (ce '= (to-expression (to-sexp poly)) 0))
         (= deg 2) (solve-quadratic x poly)
         :else (or (let [factors (ratio-root poly)]
                     (and (every? #(<= (degree %) 2) factors)
                          (solve-factors x factors)))
                   (try-factorise x poly)))))))

(defn- simplify-eq [eq] (ce `= (simp-expr (nth eq 1))  (nth eq 2)))

(defn- simplify-rhs [eq] (ce `= (nth eq 1) (simp-expr (nth eq 2))))

(defn- check-if-can-be-rearranged [v eq]
  (when (utils/only-one-occurrence v eq) eq))

;;Basic solving strategy. Simplifies the expression and checks if the number
;;of occurrences of the variable are reduced to one. It it is so then the
;;equation can be rearranged and the rhs simplified to get the solution

(defn solve-by-simplification-rules
  "tries to solve the expr in regard to v by applying simplification rules and
   rearranging the expression to the remaining occurrence of v"
  [v expr]
  (some->> expr
       simplify-eq
       (check-if-can-be-rearranged v)
       (rearrange v)
       (map simplify-rhs)))
      
;;the expresso solve is extensible - the actual solving mechanism are nothing
;;but rules which get applied for solving. Here the rules pattern is a vector
;;of [variable expression] 
(def ^:dynamic solve-rules
  [(rule [?v (ex (= (* ?&*) (mzero? ?x)))]
         :==> (solve-factors ?v (matcher-args ?&*)))
   (rule [?v ?x] :==> (solve-polynomial ?v ?x))
   (rule [?v ?x] :==> (solve-by-simplification-rules ?v ?x))
   (rule [?v ?x] :==> (solve-by-homogenization ?v ?x))
   (rule [?v ?x] :==> (solve-by-strategy ?v ?x))])

(defn apply-solve-rules
  "solves the expr in regard to v by applying the rules in solve-rules"
  [v expr]
  (let [res (apply-rules solve-rules [v expr])]
    (when (not= res [v expr])
      res)))

;;reports all the solutions in sols by calling report-res and filtering
;;out empty solutions and normalizing to _0 if one solution is arbitraty

(defn- report-solution
  "report the solutions in regard to v. Does some normalisation like returning
   #{} or _0"
  [v sols]
  (when sols
    (->> sols
         (mapv #(report-res v %))
         (filter identity)
         (remove #{'()})
         (into #{})
         (#(if (some #{'_0} %)
             '_0
             %)))))
       

(defn- transform-one-level-lhs [rules eq]
  (ce `= (transform-one-level rules (nth eq 1)) (nth eq 2)))

(def ^:dynamic *solve-attempts*)
(def ^:dynamic *symbolv*)

;;The top level solve method. Also includes a security mechanism to avoid
;;infinite loops when solving strategies recursively call solve.
;;*solve-attempts* stores the expressions with witch solve* is called and
;;solve* checks if the equation if wants to solve was tried before and gives up
;;in this case

(defn solve
  "solves the equation in regard to the variable v. An optional custom set of
   solve rules can be specified"
  ([v equation]
     (solve v equation solve-rules))
  ([v equation custom-solve-rules]
     (binding [*solve-attempts* (atom #{})
               *symbolv* (gensym "var")
               solve-rules custom-solve-rules]
       (solve* v equation))))

(defn- check-if-was-solved [v equation]
  (if (not (and (bound? #'*symbolv*) (bound? #'*solve-attempts*)))
    equation
    (let [eq (substitute-expr equation {v *symbolv*})]
      (when-not (some #{eq} @*solve-attempts*)
        (swap! *solve-attempts* #(set/union % #{eq}))
        equation))))

(defn- lhs-rhs=0 [equation]
  (ce `= (ce `- (nth equation 1) (nth equation 2)) 0))

;;to solve the equation first check-if it is solved already and short-track in
;;this case.
;;otherwise make the rhs to zero, normalize it and apply-the solving rules which
;;dispatch to the appropriate solving strategies and reports the solutions
(defn- solve* [v equation]
  (if (utils/solved? v equation)
    (report-solution v [(simplify-rhs equation)])
    (some->> equation
             (check-if-was-solved v)
             lhs-rhs=0
             (transform-one-level-lhs universal-rules)
             (apply-solve-rules v)
             (report-solution v))))    

;;code for solving a linear system. These helper functions are used to construct
;;a matrix of a system of simultaneous equations

(defn- poly-const [poly]
  (cond (number? poly) poly
        (number? (coef poly 0)) (coef poly 0)
        :else (poly-const (coef poly 0))))

(defn- lhs-to-poly [eq]
  (let [lhs (nth eq 1) rhs (nth eq 2)
        polylhs (to-poly-normal-form (ex (- ~lhs ~rhs)))]
    (when polylhs
      (let [const (poly-const polylhs)
            nlhs (to-poly-normal-form (ex (- ~polylhs ~const)))]
        (ex (= ~nlhs ~(* -1 const)))))))

(defn- search-coef [lhs v]
  (cond (number? lhs) 0
        (var= (main-var lhs) v) (when (<= (degree lhs) 1) (coef lhs 1))
        (not (var> (main-var lhs) v)) (search-coef (coef lhs 0) v)
        :else 0))

(defn- to-vec [pos-coeffs]
  (->> pos-coeffs (sort-by first) (mapv second)))

(defn- collect-params [eq vars]
  (let [lhs (nth eq 1)
        rhs (nth eq 2)]
    (ce `= (to-vec (for [[p v] vars]
                     [p (search-coef lhs v)])) rhs)))

(defn- build-matrix [eqs]
  (mapv #(conj (vec (nth %1 1)) (nth %1 2)) eqs))

(defn- simp-sols [sols]
  (cond (= '() sols) sols
        (some expr-op sols) (mapv simp-expr sols)
        :else sols))

(defn- add-needed-vars* [vs eqs]
  (let [eqv (map (fn [a] [a (vars a)]) eqs)
        needed-vars (filter identity
                            (map (fn [a]
                                   (if (some vs (second a))
                                     (set/difference (second a) vs))) eqv))]
    (into #{} (concat vs (apply set/union needed-vars)))))

(defn- add-needed-vars [vs eqs]
  (loop [vs vs]
    (let [nvs (add-needed-vars* vs eqs)]
      (if (= nvs vs)
        nvs
        (recur nvs)))))

(defn- to-map [vars v]
  (if (empty? v)
    {}
    (into {} (map (fn [[pos var]] [var (nth v pos)]) vars))))

(defn- remove-unneeded-equations [vs eqv]
  (map first (filter #(some vs (second %)) (map (fn [x] [x (vars x)]) eqv))))

(defn- check-if-linear [matrix]
  (when (and (not (empty? matrix)) (not (some (comp not number?)
                                              (matrix/eseq matrix))))
    matrix))

(defn- check-if-poly [v]
  (when-not (some nil? v)
    v))

;;solve-linear-system can solve a system of linear equations if a matrix can
;;be built to represent the set of equations and the matrix contains only
;;numbers. If this is the case, the matrix is solved using the fraction-free
;;gaussian elimination algorithm. Notice the use of some->> which makes the
;;solving strategy fail early if it detects it can't solve the system and
;;a more general solving strategy has to be used instead.

(defn solve-linear-system
  "solves a system of equations for the variables in the variable vector"
  [vars eqv]
  (let [v (into #{} vars)
        vs (add-needed-vars v eqv)
        vars (into {} (map vector (range) vs))]
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
         (utils/submap v)
         vector
         set)))

(declare solve-general-system*)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;utilities for solve-general-system start reading solve-general-system
(defn- not-in-existing-sols [sol-map var-set]
  (into #{} (remove sol-map var-set)))

(defn- solve-for-dependencies [existing-sols depends-on other-eqs]
  (reduce (fn [sols r]
            (let [ss (solve-general-system* r other-eqs sols)]
              (for [l sols s ss]
                (merge l s))))
          existing-sols depends-on))

(defn- solve-with-dependencies [other-sols v equation-containing-v]
  (utils/combine-solutions
   (fn [os]
     (let [equation-without-deps (substitute-expr
                                  (first equation-containing-v)
                                  os)
           sol (solve v equation-without-deps)]
       (if (= sol '_0)
         [os]
         (for [s sol]
           (assoc os v s))))) other-sols))

;;solves the general-system via substitution for a variable v.
;;first, the equation which contains v is searched for in the set.
;;If it was found, then recursively all its dependencies (the other variables
;;the equation contains) has to be solved with the remaining equations.
;;The solutions for the other variables then have to be combined so that
;;there is one solution map for each possible 'combination' of solutions.
;;with this solutions of the dependencies the equation can be solved for
;;the variable v.

(defn- solve-general-system*
  ([v eqs] (solve-general-system* v eqs [{}]))
  ([v eqs existing-sols]
     (if (v (first existing-sols))
       existing-sols
       ;;v is variable and eqs set of equations
       (let [eqv (map (fn [a] [a (vars a)]) eqs)
             equation-containing-v (some (fn [a]
                                           (if (contains? (second a) v)
                                             a nil)) eqv)
             _ (prn "equation-containing-v " equation-containing-v)]
         (if equation-containing-v
           (let [depends-on (not-in-existing-sols
                             (first existing-sols)
                             (set/difference (second equation-containing-v)
                                             #{v}))
                 other-eqs (set/difference eqs #{(first equation-containing-v)})
                 deps (solve-for-dependencies
                             existing-sols depends-on other-eqs)]
             (set (solve-with-dependencies deps v equation-containing-v)))
           existing-sols)))))

(defn- remove-dependency [solm expr symb]
  (-> (substitute-expr expr {symb (get solm symb)})
      simp-expr))

(defn- remove-dependencies [symbv m]
  (let [symbs (into #{} symbv)]
    (into {}
          (reduce (fn [kv-pairs [k v]]
                    (if (contains? symbs k)
                      (let [depends-on
                            (set/difference (set/intersection (vars v) symbs)
                                            #{k})]
                        (conj kv-pairs
                              [k (reduce (partial remove-dependency m)
                                         v depends-on)]))
                      (conj kv-pairs [k v]))) [] m))))

;;solve-general-system solves a system of equations according to the symbols
;;in symbolv. Output is a set of maps in the form {v res ....}.
;;The algorithm is the following
;;for each variable in symbv, solve the system for it using solve-general-system*
;;solve-general-system returns a solution set in the format like outlined
;;above. Because it may have solved for other variables first in order to solve
;;for the desired value the returned maps can contain also the solutions to
;;symbols for which solve-general-system hasn't jet solved. Therefore there
;;is the check in the reduce operation, if the current solution already has
;;solved for the symbol. If not it solves for the symbol and combines the
;;existing solutions and the new-solutions with merging.
;;after that it removes the dependencies of the symbols in symbv from the
;;solutions in the solution maps. For example if #{{'x 'y 'y 1}} is the solution
;;remove dependency will remove the dependency on 'y on the solution of 'x and
;;return #{{'x 1 'y 1}}

;;TODO it currently fails on some solvable systems because it doesn't check
;;whether it has searched for the system before and doesn't inline equations
;;which don't introduce new symbols to the equation
(defn solve-general-system
  "solves the system of equations for the symbols in symbv by general
   substitution"
  [symbv eqs]
  (let [eqs (into #{} eqs)]
    (->> (map #(utils/submap (into #{} symbv) %1)
              (reduce (fn [ls r]
                        (if (r (first ls))
                          ls
                          (for[l ls s (solve-general-system* r eqs ls)]
                            (merge l s)))) [{}] symbv))
         (map #(remove-dependencies symbv %))
         (into #{}))))

;;solve-system wil also be ported to a rule-based dispatch like solve, but for
;;now it only has two methods, namely solve-linear-system and
;;solve-general-system. Notice here the convention of returning nil to indicate
;;failure.

(defn solve-system
  "solves the system of equations in regard to the symbols in symbv"
  [symbv eqs]
  (if-let [erg (solve-linear-system symbv eqs)]
    erg (solve-general-system symbv eqs)))


(defn- split-in-pos-args [args pos]
  (let [args (vec args)]
    [(subvec args 0 pos) (nth args pos) (subvec args (inc pos))]))


;;Now comes the actual implementations of the rearranging process with the
;;supplied methods to the multimethod rearrange-step-function which is
;;called by the default expression implementation of the rearrange-step protocol
;;function. The arguments of the function are the operator, its arguments
;; (which together constitute the actual lhs of the equation)
;;the position in the args which contains the term to rearrange to and the
;;current rhs of the equation

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
  (unary-rearrange-step 'sin 'asin args rhs))

(defmethod rearrange-step-function 'asin [[op args pos rhs]]
  (unary-rearrange-step 'asin 'sin args rhs))

(defmethod rearrange-step-function 'cos [[op args pos rhs]]
  (unary-rearrange-step 'cos 'acos args rhs))

(defmethod rearrange-step-function 'acos [[op args pos rhs]]
  (unary-rearrange-step 'acos 'cos args rhs))

(defmethod rearrange-step-function 'tan [[op args pos rhs]]
  (unary-rearrange-step 'tan 'atan args rhs))

(defmethod rearrange-step-function 'atan [[op args pos rhs]]
  (unary-rearrange-step 'atan 'tan args ))

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

(defmethod rearrange-step-function 'inner-product [[op args pos rhs]]
  (let [[left x right] (split-in-pos-args args pos)]
    [[x (cev 'inner-product (concat (reverse (map #(ce 'inverse %) left))
                                    [rhs]
                                    (reverse (map #(ce 'inverse %) right))))]]))

(defmethod rearrange-step-function 'sqrt [[op args pos rhs]]
  [[(first args) (ce '** rhs 2)]])

(defmethod rearrange-step-function 'abs [[op args pos rhs]]
  [[(first args) rhs]
   [(first args) (ce '- rhs)]])


;;now comes the part where more sophisticated solving strategies are defined
;;go ahead to solve-by-homogenization and solve-by-strategy


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

;;rewrite-in-terms-of rewrites the expression according to the sem-rewrite-rules.
;;each rule matches a vector of two elements like this:
;;[actual-expression subs-to-rewrite-to] and return the modified expression.
;;an example if the sem-rewrite rule of transforming (exp (* 2 ?x)) to
;; (** (exp ?x) 2) when rewriting for (exp ?x):
;;  (rule [(exp (* ?x ?&+)) (exp ?x)] :=> (** (exp ?x) (* ?&+)))

(defn rewrite-in-terms-of
  "rewrites expr to an expression containing as much as possible occurrences
   of x"
  [expr x]
  (transform-expression
   (with-meta
     (concat arity-rules
             [(rule ?x :==> (let [res (apply-rules sem-rewrite-rules [?x x])]
                              (when-not (= res [?x x]) res)))])
     {:id :rewrite-in-terms-of-rules})
   expr))
;;semantic substitution of an expression works with rewrite-rules which transform
;;the expression to expressions in terms of the substituend. In this rewritten
;;expression the actual substitution is then done.

(defn sem-substitute
  "semantically substitutes old for new in expr. First transforms expr in terms
   of old before substitution"
  [expr old new]
  (-> expr
      (rewrite-in-terms-of old)
      (substitute-expr {old new})))

;;prefilter the expr for offendersm basically +*-/ can be solved normally so
;;they are not included in the offenders. The same counts for numbers. The rest
;;is included in the offenders list.
(defn- offenders [x  expr]
  (apply-rules
   [(rule (ex (+ ?&*)) :==> (mapcat #(offenders x %) (matcher-args ?&*)))
    (rule (ex (* ?&*)) :==> (mapcat #(offenders x %) (matcher-args ?&*)))
    (rule (ex (- ?&*)) :==> (mapcat #(offenders x %) (matcher-args ?&*)))
    (rule (ex (/ ?a ?b)) :==> (offenders x ?a) :if
          (guard (is-number? ?b)))
    (rule (ex (** ?a ?b)) :==> (offenders x ?a) :if
          (guard (and (number? ?b) (< ?b 3))))
    (rule ?x :=> [] :if (guard (is-number? ?x)))
    (rule ?x :=> [?x])]
   expr))

(defn- **-heuristic [x eq offenders]
  (and (every? #(= (expr-op %) '**) offenders)
       (every? #{(second (first offenders))} (map second offenders))
       (ce '** (second (first offenders)) x)))

(defn- exp-heuristic [x eq offenders]
  (and (every? #(= (expr-op %) 'exp) offenders)
       (ce 'exp x)))

(defn- sin-heuristic [x eq offenders]
  (and (every? #(= (expr-op %) 'sin) offenders)
       (every? #{(second (first offenders))} (map second offenders))
       (ce 'sin (second (first offenders)))))

(defn- trig-heuristic [x eq offenders]
  (and (every? #(or (= (expr-op %) 'cos)
                    (= (expr-op %) 'sin)
                    (and
                     (= (expr-op %) '**)
                     (utils/num= (nth % 2) 2)
                     (or (= (expr-op (nth % 1)) 'sin)
                         (= (expr-op (nth % 1)) 'cos)))) offenders))
  (if (contains-expr? eq (rule (ex (** (sin ?x) 2)) :=> true))
    (ex (cos x))
    (if (contains-expr? eq (rule (ex (** (cos ?x) 2)) :=> true))
      (ex (sin x))
      (some (fn [x] (if (= (expr-op x) 'sin) 'sin
                        (if (= (expr-op x) 'cos) 'cos))) offenders))))

(defn- poly-heuristic [x eq offenders ]
  (let [r (rule (ex (** ?x ?y)) :=> (ex (** ?x ?y)) :if (guard (number? ?y)))
        pos (utils/positions-of x eq)
        off (map #(surrounded-by eq % r) pos)
        off (map #(poly-in x (first %)) off)]
    (and (not (empty? off)) (every? identity off)
         (let [m (apply max (map degree off))]
           (when (> m 2)
             (ce '** x (if (> (- m 2) 1) (- m 2) (- m 1))))))))

(def substitution-candidate-heuristics
  [**-heuristic
   exp-heuristic
   sin-heuristic
   trig-heuristic
   poly-heuristic])

;;makes a list of substitution candidates which could transform the expression
;;after semantic substitution to a known form which can be solved.
;;like many of expressos functions, it is datadriven from the functions in the
;;substitution-candidate-heuristics which get the variable, the expression and
;;a prefilterd list of offenders (terms which stand in the way of solving
;;normally (like exp and (** ?x 4) ,....) and return a substitution candidate

(defn- substitution-candidates [x equation offenders]
  (filter identity (map #(%1 x equation offenders)
                        substitution-candidate-heuristics)))

;;solve the equation lhs=0 for the variable x with the given substitution by
;;semantic substitution and combining the solutions of the subsituted expression
;;with the solutions of the equation (= subs <solution-of-substituted-equation)

(defn solve-by-substitution
  "solves the equation lhs=0 by substitution in regard to x"
  [x lhs subs]
  (if subs
    (let [v (gensym "var")
          substituted (sem-substitute lhs subs v)]
      (if (or (and (seq? substituted) (some #{v} (flatten substituted)))
              (= substituted v))
        (let [sols (solve* v (ce '= substituted 0))]
          (if sols
            (into #{}
                  (map #(ce '= x %)
                       (mapcat #(solve* x (ce '= subs %)) sols)))))))))
  

;;solve-by homogenization tries to transform the not solvable expression to
;;a known form by semantic rewriting with suited substitution candidates.
;;An example would be rewriting (ex (= (+ (exp (* 2 x)) (exp x) 4) 0))
;;to (ex (= (+ (** v 2) v 4) 0)) by semantically substituting the
;;substitution candidate expr. The new polynomial can than be solved and by
;;resubstitution also the substitution candidate.


(defn solve-by-homogenization
  "solves the equation for x by trying to transform it to a known form"
  [x equation]
  (let [lhs (second equation)
        subs (->> lhs (offenders x ) (substitution-candidates x equation) last)]
    (solve-by-substitution x lhs subs)))

;;now multiple strategy solving functions are specified, like solve-fractions,
;;solve-logarithms and so on. They are dispatched by solve-by-strategy.
;;See the function documentation for details

(defn- multiply-equation [eq factor]
  (ce '= (ce '* (nth eq 1) factor) (ce '* (nth eq 2) factor)))


(defn surrounded-by
  "returns [res-of-rule-application position] when the rule is succesfully
   applied at a prefix of pos"
  [equation pos rule]
  (loop [n (count pos)]
    (if (> n 0)
      (if-let [res (apply-rule rule (utils/get-in-expression equation
                                                             (subvec pos 0 n)))]
        [res (subvec pos 0 n)]
        (recur (dec n))))))


;;solve-logarithms and solve-square-roots have very similar algorithms.
;;both get all positions of terms which are enclosed by their offending
;;term. For each position, they rearrange the term to the position, that means
;;until the expression has the form (in case of square-root)
;;(ex (= (sqrt term-of-x) rhs)). It then eliminates this occurrence of the
;;offending term by square or exp operations. It recursively elimininates the
;;other occurrences as well and solves the resulting equation which does
;;not contain x-ses enclosed by the offending term any more.
;;each function has own rules to be used in the elimination step to make sure
;;the elimination is done most effectively.

(defn solve-logarithms
  "eliminates all logarithms in eq and solves the resulting equation for x"
  [x eq]
  (loop [equation (transform-expression log-solve-rules eq)]
    (let [positions (utils/positions-of x equation)
          r (rule (ex (log ?x)) :=> ?x)
          log (some #(surrounded-by equation % r) positions)]
      (if-let [[x pos] log]
        (let [rearr (first (rearrange-to-position equation pos))]
          (recur (transform-expression
                  log-solve-rules
                  (ce '= (ce 'exp (nth rearr 1)) (ce 'exp (nth rearr 2))))))
        (set (filter #(check-solution x eq %) (solve* x equation)))))))

(defn solve-square-roots
  "eliminates all square roots and solves the resulting equation for x"
  [x equation]
  (let [positions (utils/positions-of x equation)
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
                                       (utils/positions-of x new-equation)))
                 new-equation (inc i)))))))

(defn- square-number [a]
  (let [sq (Math/sqrt ^long a)]
    (utils/num= sq (Math/floor sq))))

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

(declare multiply-equation)

;;solve-fractions removes all fractions from the equation and then solves the
;;resulting polynomial. It gets all the positions where a x-containing term
;;is enclosed in a fraction in the equation (after preprocessing with
;;fraction rules to ensure for example the denominator has the form (/ term-of-x)
;;Then all the denomiator are collected, their common-factor is calculated
;;(simple-identities like (- (** x 2) 9) are factored out by the rules)
;;and then the equation is multiplied by the factor and transformed with the
;;cancel-fraction-rules, which take care that the factor descends far enough
;;into the equation to cancel out all fractions.
;;Befor the canceling step all the factors are substituted in the expression, so
;;that the cancel-fraction-rules do not influence them, and resubstituted
;;afterwards. If the positions of the unknown are succesfully eliminated by
;;the procedure, it solves the resulting (polynomial) eqaution.

(defn solve-fractions
  "eliminates all fractions and solves the resulting equation for x"
  [x equation]
  (loop [equation (transform-expression fraction-rules equation)]
    (let [positions (utils/positions-of x equation)
          r (rule (ex (/ ?x)) :=> ?x)
          frac (filter identity (map #(surrounded-by equation % r) positions))
          varmap (into {} (map (fn [[exp pos]] [exp (gensym "var")]) frac))
          symbal (doall (map  (fn [frac] [(get varmap (first frac)) frac])
                              (into #{} frac)))
          rsymbm (into {} (map (fn [[k v]] [k (first v)]) symbal))
          symbm (into {} (map (fn [[x y]] [(concat (second y) [0]) x]) symbal))
          factor (cev '* (into #{} (map first symbal)))
          without-fractions
          (as-> equation x
                (utils/substitute-in-positions x symbm)
                (multiply-equation x factor)
                (transform-expression cancel-fraction-rules x)
                (substitute-expr x rsymbm))]
      (when-not (some #(surrounded-by without-fractions % r)
                      (utils/positions-of x without-fractions))
        (into #{} (filter #(check-solution x equation %)
                          (solve* x without-fractions)))))))

;;if the x-ses are enclosed in abs functions, this method creates all the
;;possible equations with abs removed, by replacing each abs by two equations
;;where the abs term is replaced by a plus or minus term respectively.
;;These resulting equations are then solved and their results checked
;;(because not all combinations return valid results). The checking currently
;;is of limited use when the abs-terms have variables in it. In this case
;;the solving method can create false positives. To eliminate this one would have
;;to be able to make analysis on which part of the number spectrum are the terms
;;negative, positive, or zero and create the expression based on that knowledge
;;This is currently out of scope.


(defn solve-abs
  "removes the abs terms in the equation, solves the resulting equations for x
   and checks the results"
  [x equation]
  (let [positions (utils/positions-of x equation)
        r (rule (ex (abs ?x)) :=> true)
        sb (some #(surrounded-by equation % r) positions)]
    (loop [equations [equation]]
      (if (some (fn [eq] (some #(surrounded-by eq % r)
                               (utils/positions-of x eq)))
                equations)
        (recur
         (mapcat (fn [eq]
                   (if-let [[_ pos] (some #(surrounded-by eq % r)
                                    (utils/positions-of x eq))]
                     (let [abs (utils/get-in-expression eq pos)]
                       [(substitute-expr eq {abs (nth abs 1)})
                        (substitute-expr eq {abs (ce '- (nth abs 1))})])
                     [eq])) equations))
        (set (filter #(check-solution x equation %) (mapcat #(solve* x %)
                                                            equations)))))))

;;solve-common-prefix is a very useful strategy when there are multiple
;;occurrences of the variable, but all the occurrences are in one part of the
;;equation (their positions have a common prefix). This is the case in
;;(ex (= (** 100 (+ (** x 2) (* 3 x) 4)) 5)) for example, where all occurences
;;of x are in the (** 100 ....) term.
;;If this is detected, the root of all positions of x is substituted in the
;;expression and then solved. In the example this would be:
;;solve (ex (= (** 100 v) 5)) and then solve (ex (= (+ (** x 2) (* 3 x) 4) ~erg))

(defn- solve-common-prefix [positions equation]
  (if (> (count positions) 1)
    (let [cp (utils/common-prefix positions)]
      (if (> (count cp) 2)
        (let [s (utils/get-in-expression equation cp)]
          (fn [x eq]
            (solve-by-substitution x (nth eq 1) s)))))))

(def strategy-choose-heuristics
  [solve-common-prefix
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
     (let [r (rule (ex (log ?x)) :=> ?x)]
       (if (some #(surrounded-by equation % r) positions)
         solve-logarithms)))
   ])


(defn- position-strategy [positions equation]
  (some identity (map #(%1 positions equation) strategy-choose-heuristics)))

;;solve-by-strategy dispatches to solvers depending where x is in the
;;equation. These heuristics are again stored in a vector for extensibility.
;;The central helper function here is surrounded-by, which gets the positions
;;of x in the equation and works them up. At each stage it applies the given
;;rule and if it succeeds, returns the result+position. This way the
;;heuristics can determine whether the occurrences of x are inside a square root
;;for example. solve-by-strategy then dispatches to the right strategy which
;;inturn eliminates all occurences of its offending term and solves the resulting
;;equation. In case of square roots as surrounding terms, the square roots are
;;recursively eliminated and the resulting equation (which is in the normal case
;;a polynomial) is solved

(defn solve-by-strategy
  "solves equation with a strategy choosen by the positions of x and the terms
   surrounding them in regard to x"
  [x equation]
  (let [positions (utils/positions-of x equation)
        strategy (position-strategy positions equation)]
    (if strategy
      (strategy x equation))))


(defn check-solution
  "checks if solution is a solution to equation for x.
    Does not work for solutions containing variables."
  [x equation solution]
  (try
    (if-not (empty? (vars solution))
      true
      (when-let [x (solve* (gensym "var")
                      (substitute-expr equation {x solution}))]
          (not (= x #{}))))
    (catch Exception e nil)))


(defn- contains-expr?
  "checks is r is applicable on some subexpression of expr"
  [expr r]
  (or (and (not= expr (apply-rules [r] expr))
           (apply-rules [r] expr))
      (some #{true}
            (flatten (transform-expression [r] expr)))))
