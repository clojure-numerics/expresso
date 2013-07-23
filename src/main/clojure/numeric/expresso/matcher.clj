(ns numeric.expresso.matcher
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [numeric.expresso.protocols]
        [clojure.core.logic :exclude [is] ]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [numeric.expresso.utils :as utils]))
(declare match-expressiono)
(declare expression-matcho)
(declare isao)
(declare add-replacemento)



#_(extend-protocol PMatch
  numeric.expresso.protocols.Expression
  (match [this that]
    (if-let [m (and (expr-op that) (meta (expr-op this)))]
      (fresh []
             
               (match-expressiono (expr-op this) (expr-op that))
               ((:match-rel m) (expr-args this) (expr-args that)))
        fail))
  numeric.expresso.protocols.BasicExtractor
  (match [this that]
    (let [args (.args this)
          rel (.rel this)]
      (rel args that)))
  clojure.lang.ISeq
  (match [this that]
    (prn "hi")
    (if-let [m (and (expr-op this) (expr-op that) (meta (expr-op this)))]
      (fresh []
             (match-expressiono (expr-op this) (expr-op that))
             ((:match-rel m) (expr-args this) (expr-args that)))
      fail))
  java.lang.Object
  (match [this that]
    (expression-matcho this that)))
    
(extend-protocol PMatch
  numeric.expresso.protocols.Expression
  (match [this that]
    (if-let [m (and (expr-op that) (meta (expr-op this)))]
      (fresh [ps es pargs eargs]
             (utils/expo ps pargs this)
             (utils/expo es eargs that)
             (isao es ps)
             (add-replacemento es ps)
             ((:match-rel m) (expr-args this) (expr-args that)))
      fail))
  clojure.lang.ISeq
    (match [this that]
      (if-let [m (and (expr-op that) (meta (expr-op this)))]
        (fresh [ps es pargs eargs]
               (utils/expo ps pargs this)
               (utils/expo es eargs that)
               (isao es ps)
               (add-replacemento es ps)
               ((:match-rel m) (expr-args this) (expr-args that)))
        fail))
    numeric.expresso.protocols.BasicExtractor
    (match [this that]
      (let [args (.args this)
            rel (.rel this)]
        (rel args that))))

(defn isao
  "succeeds if a isa? b or if any argument is unbound - in this case
   unifying them"
  [a b]
  (conda
   ((== a b))
   ((project [a b]
             (== true (isa? a b))))))

#_(defn is-expro
  "succeeds if v is an expression"
  [v]
  (project [v]
           (== true (and (coll? v) (symbol? (first v))))))

(defn is-expro [v]
  (project [v]
           (== true (boolean (expr-op v)))))

(defn- memberposo
  "like membero l (zip x (range))"
  [l x]
  (project [x]
           (membero l (map (fn [& a] a) x (range)))))


(defn- removeo
  "binds xr to x with element at position i removed"
  [i x xr]
  (project [i x]
           (== xr (concat (take i x) (drop (+ i 1) x)))))

(defn- positivo
  "succeeds if n is bigger than 0"
  [n]
  (project [n] (if (> n 0) succeed fail)))

(defn- deco
  "binds nn to (dec n)"
  [n nn]
  (project [n] (== nn (- n 1))))

(defn- append-veco
  "appendo on real vectors"
  [ap r nap]
  (project [ap r]
           (== nap (conj (vec ap) r))))

(defn- membersplito
  "generates all possible splits of removing an element from x
   l will be bound to [removed-element rest-of-x]"
  [l x]
  (project [x]
           (fresh [a i xr]
                  (memberposo [a i] x)
                  (removeo i x xr)
                  (== l [a xr]))))

(defn- subseto
  "generates all subsets of size n from x with initial
   elements in ap"
  [n x ap res]
  (fresh []
         (conda
          ((positivo n)
           (fresh [r rx nap nn]
                  (membersplito [r rx] x)
                  (append-veco ap r nap)
                  (deco n nn)
                  (subseto nn rx nap res)))
          ((== res [ap x])))))
  
        



(defn zip
  "utility to zip collections"
  [& colls]
  (apply (partial map (fn [& a] a)) colls))

(defn seq-matcher?
  "A sequential matcher is a logic variable with a name starting with ?&"
  [elem]
  (and (lvar? elem) (.startsWith (:name elem) "?&")))

(defn- counto
  "unifies q to the count of pat or 1 if it is not a collection"
  [pat q]
  (project [pat]
           (== q (if (coll? pat) (count pat) 1))))

(defn- get-positions-of-seq-matchers
  "returns all positions of sequential matchers in the pattern"
  [pat]
  (reduce (fn [ps [p elem]]
            (if (seq-matcher? elem)
              (conj ps p)
              ps))
          [] (zip (range) (if (coll? pat) pat [pat]))))

(defn- pos-of-seq-matcherso
  "core.logic version of get-positions-of-seq-matchers"
  [pat res]
  (project [pat]
           (== res (get-positions-of-seq-matchers pat))))


(defn +-seq-matcher?
  "a lvar starting with ?&+ is a +-seq-matcher. It matches one or more
   variables"
  [psm] (.startsWith (:name psm) "?&+"))

(defn- check-boundso
  "makes sequential matching fail if a ?&+ shall be unified with zero
   elements"
  [psm esm]
  (project [esm]
           (if (and (+-seq-matcher? psm) (empty? esm))
             fail succeed)))

(defn seq-expr-matcho
  "matches psm with the elements in esm"
  [psm esm]
  (fresh []
         (check-boundso psm esm)
         (== psm [:numeric.expresso.construct/seq-match esm])))

(defn- split-expr
  "splits pargs and eargs in normal and seq-matcher part - only supports
    &* matcher at last position in pargs"
  [pargs eargs]
  (let [pos (get-positions-of-seq-matchers pargs)]
    (if (= (count pos) 0)
      [[pargs nil] [eargs nil]]
      (if (or (> (count pos) 1) (not= (first pos) (- (count pargs) 1)))
        (throw (Exception. "only one seq-match in last position is supported"))
        (let [cpa (count pargs)]
        [[(butlast pargs) (last pargs)] [(take (- cpa 1) eargs) (drop (- cpa 1) eargs)]])))))

(defn- split-expro
  "core.logic version of split-expr"
  [pargs eargs res]
  (project [pargs eargs]
           (== res (split-expr pargs eargs))))


(defna match-expressionso
  "matches each of pargs and eargs according to the right matching function"
  [pargs eargs]
  ([[p . ps] [e . es]] (match-expressiono p e) (match-expressionso ps es))
  ([[] []] succeed)
  ([_ _] fail))



(defn single-expr-matcho
  "default matching function if there are no seq-matchers in pargs"
  [pargs eargs]
  (project [pargs eargs]
           (if (not= (count pargs) (count eargs))
             fail
             succeed))
  (match-expressionso pargs eargs))


(defn- any-seq-matcherso
  "succeeds when there is at least a seq-matcher in pattern"
  [pargs]
  (project [pargs]
           (== false (if (coll? pargs) (not (some seq-matcher? pargs)) true))))

(declare match-with-seq-matcherso)
(defn expression-matcho
  "default matching function - matches each element of pargs against the element
   at the same position in eargs using the right matching function. also supports
   sequential matchers"
  [pargs eargs]
  (fresh []
         (conda
          ((any-seq-matcherso pargs) (match-with-seq-matcherso pargs eargs))
          ((single-expr-matcho pargs eargs)))))

(defn- split-list
  "creates the possible splits of v by removing an element if it is not a vlar"
  [v]
  (let [res
        (for [x (range (count v)) :when (not (lvar? (nth v x)))] 
          (let [elem (nth v x)
                left (take x v)
                right (drop (clojure.core/+ x 1) v)]
            [elem (concat left right)]))]
    res))


(defn- split-listo
  "core.logic version of split-list"
  [l erg]
  (project [l ]
           (== erg (split-list l))))

(defn only-lvarso
  "succeeds when there are only lvars in args"
  [args]
  (project [args]
           (== true (every? lvar? args))))

(defn split-pargs
  "splits pargs to the normal part and the sequential matcher part
   associative matching only supports one seq-matcher at any position"
  [pargs]
  (let [p (filter #(seq-matcher? (second %)) (zip (range) pargs))]
    (if (not= (count p) 1)
      (throw (Exception. "only one seq-matcher supported in commutative matching"))
      (let [pp (first (first p))
            sm (second (first p))]
        [(concat (take pp pargs) (drop (+ pp 1) pargs)) sm]))))

(defn- split-pargso
  "core.logic version of split-pargs"
  [pargs res]
  (project [pargs]
           (== res (split-pargs pargs))))

(defn- no-seq-matcherso
  "succeeds if there ale no seq-matchers in pargs"
  [pargs]
  (project [pargs] (== 0 (count (filter seq-matcher? pargs)))))

(defn- match-lvars-commutativeo
  "generates the possible matches of eargs with the lvars in pargs"
  [pargs eargs]
  (fresh [perm npargs sm cnp neargs to-seq-match]
         (conda
          ((no-seq-matcherso pargs)
           (permuteo pargs perm)
           (== perm eargs))
          ((split-pargso pargs [npargs sm])
           (project [npargs] (== cnp (count npargs)))
           (subseto cnp eargs [] [neargs to-seq-match])
           (== neargs npargs)
           (seq-expr-matcho sm to-seq-match)))))

(defn match-commutativeo
  "the matching function for commutative expressions.
   Matches if one permutation matches. also supports
   a seq-matcher"
  [pargs eargs]
  (fresh [esl psl eng png er pr]
         (conda
          ((only-lvarso pargs) (match-lvars-commutativeo pargs eargs))
          ((only-lvarso eargs) (match-lvars-commutativeo pargs eargs))
          ((split-listo pargs psl)
           (membero [png pr] psl)
           (split-listo eargs esl)
           (membero [eng er] esl)
           (match-expressiono png eng)
           (match-commutativeo pr er)))))


(defn- split-seq-matchers
  "splits pargs and eargs in the fix part and the variable parts"
  [pargs eargs]
  (let [indices (map first (filter (comp seq-matcher? second) (zip (range) pargs)))
        sections (partition 2 1 indices)
        v-part (concat (map (fn [[f l]] [(nth pargs f) (subvec pargs (inc f) l)]) sections) [[(nth pargs (last indices)) []]])]
    [(first indices) (last indices)
     (- (count eargs) (- (count pargs) (last indices)))
     v-part]))

(defn- split-seq-matcherso
  "core.logic version of split-seq-matchers"
  [pargs eargs res]
  (project [eargs pargs]
           (== res (split-seq-matchers (vec pargs) (vec eargs)))))

(defn- match-in-positionso
  "matches the elements between fp and tp in pargs and
   fe and te in eargs"
  [fp tp fe te pargs eargs]
  (project [fp tp fe te  pargs eargs]
           (if (or (> tp (count pargs)) (> te (count eargs)))
             fail
             (if (and (< fp tp) (< fe te))
               (fresh []
                      (match-expressiono (nth pargs fp) (nth eargs fe))
                      (match-in-positionso (+ fp 1) tp (+ fe 1) te  pargs eargs))
               succeed))))
(defn- match-fix-parto
  "matches the fix part of pargs and eargs"
  [sm-start sp-end sm-end pargs eargs]
  (project [sm-start sp-end sm-end pargs eargs]
           (fresh []
                  (match-in-positionso 0 sm-start 0 sm-start pargs eargs)
                  (match-in-positionso (+ sp-end 1) (count pargs)
                                       (+ sm-end 1) (count eargs)
                                       pargs eargs))))

(defn- start-positionso
  "generates the possible starting positions for the first vpart in v-parts
   between from and to"
  [from v-parts to pos]
  (project [from v-parts to]
           (let [s (apply + (map (comp count second) v-parts))
                 anz-positions (- (+ to 1) from s)]
             (== pos (range from (+ from anz-positions 1))))))

(defn- match-parto
  "matches a variable part starting at start in eargs matching the seq matcher
   to te position in eargs from start to from"
  [from part start eargs]
  (project [from part start eargs]
           (let [
                 p (second part)
                 sm (first part)
                 tsm (subvec eargs from start)]
             (fresh []
                    (match-in-positionso 0 (count p) start (+ start (count p))
                                         p eargs)
                    (seq-expr-matcho sm tsm)))))

(defn- match-last-seq-matchero
  "matches the seq-matcher at the end of the variable part from from to to in
    eargs"
  [from to seq-matcher eargs]
  (project [from to seq-matcher eargs]
           (let [sm (first seq-matcher)
                 tsm (subvec eargs from (+ to 1))]
             (seq-expr-matcho sm tsm))))

(defna match-variable-parto
  "matches the variable patrs in eargs and the seq-matchers between them in the
   variable part of eargs starting at from to to"
  [from to v-parts eargs]
  ([_ _ [part . '()] _]
     (match-last-seq-matchero from to part eargs))
  ([_ _ [part . parts] _]
     (fresh [pos start]
            (start-positionso from v-parts to pos)
            (membero start pos)
            (match-parto from part start eargs)
            (project [from part start]
                     (match-variable-parto (+ start (count (second part)))
                                           to parts eargs)))))

(defn match-with-seq-matcherso
  "default matching function when there are seq-matchers. Matches the arguments
   in order and supports an arbitrary number of seq-matchers in any position"
  [pargs eargs]
  (project [pargs eargs]
           (let [pargs (vec pargs) eargs (vec eargs)]
             (fresh [from top toe v-parts]
                    (split-seq-matcherso pargs eargs [from top toe v-parts])
                    (match-fix-parto from top toe pargs eargs)
                    (match-variable-parto from toe v-parts eargs)))))




(defn- get-symbol
  "gets the symbol of the expression"
  [expr]
  (if (coll? expr) (first expr) expr))

(defmulti matcher
  "the multimethod to get the right matching functions from the expression"
  get-symbol)

(defmethod matcher :default [_]
  expression-matcho)

(defmethod matcher 'e/ca-op [_] match-commutativeo)

(def replacements (atom {}))

(defmulti extractor
  "multimethod to get the right extractor function for the extractor"
  get-symbol)


(defn extract-is [pargs expr]
  (project [pargs]
           (let [[lv pred] pargs]                   
             (if (pred expr)
               (== lv expr)
               fail))))

(defn extract-cons [pargs expr]
  (project [pargs]
           (let [[p ps] pargs]
             (conso p ps expr))))

(defmethod extractor 'is? [_] extract-is)

(defmethod extractor 'cons? [_] extract-cons)

(defmethod extractor :default [_] (fn [a b] fail))

(defn replace-symbolso
  "replaces the symbols in old wich were replaced during the last match with
   the replacements - method will change"
  [old new]
  (project [old]
           (let [
                 res (walk/prewalk-replace @replacements old)
                 res (utils/splice-in-seq-matchers res)]
             (do (reset! replacements {})
                 (== res new)))))

(defn add-replacemento
  "adds a replacement from ps to es to the replacements - will change"
  [es ps]
  (project [es ps]
           (if (= es ps)
             succeed
             (do (swap! replacements assoc ps es)
                 succeed))))


(defn match-expressiono
  "matches pattern against exp. Dispatches to the right matching function.
   Tries simple unification first to save overhead in the simple case"
  [pat exp]
  (conde
   ((== pat exp))
   ((conda
     ((is-expro exp) (is-expro pat)
             (project [pat exp]
                      (match pat exp)))
     ((is-expro pat)
             (project [pat exp]
                      (match pat exp)))
     ((expression-matcho pat exp))))))