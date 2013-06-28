(ns numeric.expresso.rules
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] ]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [numeric.expresso.utils :as utils]
            [numeric.expresso.construct :as c]))

(defn memberposo [l x]
  (project [x]
           (membero l (map (fn [& a] a) x (range)))))


(defn removeo [i x xr]
  (project [i x]
           (== xr (concat (take i x) (drop (+ i 1) x)))))

(defn positivo [n]
  (project [n] (if (> n 0) succeed fail)))

(defn deco [n nn]
  (project [n] (== nn (- n 1))))

(defn my-appendo [ap r nap]
  (project [ap r]
           (== nap (conj (vec ap) r))))

(defn membersplito [l x]
  (project [x]
           (fresh [a i xr]
                  (memberposo [a i] x)
                  (removeo i x xr)
                  (== l [a xr]))))

(defn subseto [n x ap res]
  (fresh []
         (conda
          ((positivo n)
           (fresh [r rx nap nn]
                  (membersplito [r rx] x)
                  (my-appendo ap r nap)
                  (deco n nn)
                  (subseto nn rx nap res)))
          ((== res [ap x])))))
  


#_(defn subseto [n supset]
  (fresh [a b c d]
         (my-membero [a b] supset)))
         

(defn replace-?-with-lvar [node]
  (if (and (symbol? node) (.startsWith (name node) "?"))
    (lvar node false)
    node))

(defn zip [& colls]
  (apply (partial map (fn [& a] a)) colls))

(defn seq-matcher? [elem]
  (and (lvar? elem) (.startsWith (:name elem) "?&")))

(defn counto [pat q]
  (project [pat]
           (== q (if (coll? pat) (count pat) 1))))

(defn get-positions-of-seq-matchers [pat]
  (reduce (fn [ps [p elem]]
            (if (seq-matcher? elem)
              (conj ps p)
              ps))
          [] (zip (range) (if (coll? pat) pat [pat]))))

(defn pos-of-seq-matcherso [pat res]
  (project [pat]
           (== res (get-positions-of-seq-matchers pat))))

(defn seq-expr-matcho [psm esm]
  (== psm [:numeric.expresso.construct/seq-match esm]))

(defn split-expr [pargs eargs]
  (let [pos (get-positions-of-seq-matchers pargs)]
    (if (= (count pos) 0)
      [[pargs nil] [eargs nil]]
      (if (or (> (count pos) 1) (not= (first pos) (- (count pargs) 1)))
        (throw (Exception. "only one seq-match in last position is supported"))
        (let [cpa (count pargs)]
        [[(butlast pargs) (last pargs)] [(take (- cpa 1) eargs) (drop (- cpa 1) eargs)]])))))

(defn split-expro [pargs eargs res]
  (project [pargs eargs]
           (== res (split-expr pargs eargs))))

(defn ?-to-lvar [code]
  (walk/prewalk replace-?-with-lvar code))

(defn isao [a b]
  (conda
   ((== a b))
   ((project [a b]
             (== true (isa? a b))))))

(defn check-guardo [guard]
  (project [guard] guard))

(defn apply-transformationo [trans n-exp]
  (project [trans]
           (if (and  (ifn? trans) (not (coll? trans)))
             (trans n-exp)
             (== trans n-exp))))

(defmacro rule
  "constructs an rule. Syntax is (rule pat :=> trans) or \n
   (rule pat :=> trans :if guard)"
  [& v]
  (let [expanded (?-to-lvar v)
        [pat to trans & rest] expanded
        guard (if (seq rest) (second rest) succeed)]
    [pat trans guard]))

(defn is-seqo [v]
  (project [v]
           (== true (coll? v))))
(declare match-expressiono)

(defna match-expressionso [pargs eargs]
  ([[p . ps] [e . es]] (match-expressiono p e) (match-expressionso ps es))
  ([[] []] succeed)
  ([_ _] fail))



(defn single-expr-matcho [pargs eargs]
  (project [pargs eargs]
           (if (not= (count pargs) (count eargs))
             fail
             succeed))
  (match-expressionso pargs eargs))


(defn expression-matcho [pargs eargs]
  (fresh [pa ea psm esm]
        (split-expro pargs eargs [[pa psm] [ea esm]])
        (single-expr-matcho pa ea)
        (seq-expr-matcho psm esm)))

(defn split-list [v]
  (let [res
        (for [x (range (count v)) :when (not (lvar? (nth v x)))] 
          (let [elem (nth v x)
                left (take x v)
                right (drop (clojure.core/+ x 1) v)]
            [elem (concat left right)]))]
    res))


(defn split-listo [l erg]
  (project [l ]
           (== erg (split-list l))))

(defn only-lvarso [args]
  (project [args]
           (== true (every? lvar? args))))

(defn split-pargs [pargs]
  (let [p (filter #(seq-matcher? (second %)) (zip (range) pargs))]
    (if (not= (count p) 1)
      (throw (Exception. "only one seq-matcher supported in commutative matching"))
      (let [pp (first (first p))
            sm (second (first p))]
        [(concat (take pp pargs) (drop (+ pp 1) pargs)) sm]))))

(defn split-pargso [pargs res]
  (project [pargs]
           (== res (split-pargs pargs))))

(defn no-seq-matcherso [pargs]
  (project [pargs] (== 0 (count (filter seq-matcher? pargs)))))

(defn match-lvars-commutativeo [pargs eargs]
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

(defn match-commutativeo [pargs eargs]
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

                                        ;var-start is the first position of an seq-matcher
                                        ;var-end is the last position of an seq-matcher

(defn split-seq-matchers [pargs eargs]
  (let [indices (map first (filter (comp seq-matcher? second) (zip (range) pargs)))
        sections (partition 2 1 indices)
        v-part (concat (map (fn [[f l]] [(nth pargs f) (subvec pargs (inc f) l)]) sections) [[(nth pargs (last indices)) []]])]
    [(first indices) (+ 1 (last indices))
     (- (count eargs) (- (count pargs) (last indices)))
     v-part]))

(defn split-seq-matcherso [pargs eargs res]
  (project [eargs pargs]
           (== res (split-seq-matchers (vec pargs) (vec eargs)))))

(defn match-in-positionso [fp tp fe te pargs eargs]
  (project [fp tp fe te  pargs eargs]
           (if (and (< fp tp) (< fe te))
             (fresh []
                    (== (nth pargs fp) (nth eargs fe))
                    (match-in-positionso (+ fp 1) tp (+ fe 1) te  pargs eargs))
             succeed)))

(defn match-fix-parto [sm-start sp-end sm-end pargs eargs]
  (project [sm-start sp-end sm-end pargs eargs]
           (fresh []
                  (match-in-positionso 0 sm-start 0 sm-start pargs eargs)
                  (match-in-positionso sp-end (count pargs)
                                       sm-end (count eargs)
                                       pargs eargs))))

(defn start-positionso [from v-parts to pos]
  (project [from v-parts to]
           (let [s (apply + (map (comp count second) v-parts))
                 anz-positions (- (+ to 1) from s)]
             (== pos (range from (+ from anz-positions 1))))))

(defn match-parto [from part start eargs]
  (project [from part start eargs]
           (let [
                 p (second part)
                 sm (first part)
                 tsm (subvec eargs from start)]
             (fresh []
                    (match-in-positionso 0 (count p) start (+ start (count p))
                                         p eargs)
                    (seq-expr-matcho sm tsm)))))

(defn match-last-seq-matchero [from to seq-matcher eargs]
  (project [from to seq-matcher eargs]
           (let [sm (first seq-matcher)
                 tsm (subvec eargs from (+ to 1))]
             (seq-expr-matcho sm tsm))))

(defna match-variable-parto [from to v-parts eargs]
  ([_ _ [part . '()] _]
     (match-last-seq-matchero from to part eargs))
  ([_ _ [part . parts] _]
     (fresh [pos start]
            (start-positionso from v-parts to pos)
            (membero start pos)
            (match-parto from part start eargs)
            (project [from part start]
                     (match-variable-parto (+ start (count (second part))) to parts eargs))))
  ([_ _ _ _] succeed))

(defn match-associativeo [pargs eargs]
  (project [pargs eargs]
           (let [pargs (vec pargs) eargs (vec eargs)]
             (fresh [from top toe v-parts]
                    (split-seq-matcherso pargs eargs [from top toe v-parts])
                    (match-fix-parto from top toe pargs eargs)
                    (match-variable-parto from toe v-parts eargs)))))
           
(defn get-symbol [expr]
  (if (coll? expr) (first expr) expr))

(defmulti matcher get-symbol)

(defmethod matcher :default [_]
  expression-matcho)

(defmethod matcher 'e/ca-op [_] match-commutativeo)

(defmethod matcher 'e/ao-op [_] match-associativeo)

(def replacements (atom {}))

(defn replace-symbolso [old new]
  (project [old]
           (let [res (walk/prewalk-replace @replacements old)
                 res (c/splice-in-seq-matchers res)]
             (do (reset! replacements {})
                 (== res new)))))

(defn add-replacemento [es ps]
  (project [es ps]
           (if (= es ps)
             succeed
             (do (swap! replacements assoc ps es)
                 succeed))))
(defn match-expressiono [pat exp]
  (conde
   ((== pat exp))
   ((is-seqo pat) (is-seqo exp)
    (fresh [ps es pargs eargs]
           (c/expo ps pargs pat)
           (c/expo es eargs exp)
           (isao es ps)
           (add-replacemento es ps)
           (project [ps pargs eargs pat exp]
                    (let [f (matcher ps)]
                      (f pargs eargs)))))))
    

(defn apply-rule [rule exp]
  (first (run 1 [q]
               (fresh [pat trans guard tmp]
                      (== rule [pat trans guard])
                      (match-expressiono pat exp)
                      (check-guardo guard)
                      (apply-transformationo trans tmp)
                      (replace-symbolso tmp q)))))

(defn apply-ruleo
  "applies rule to exp failing if not applicable or unifying n-exp
   to the result"
  [rule exp n-exp]
  (project [rule]
  (fresh [res]
         (== res (apply-rule rule exp))
         (conda ((nilo res) fail) ((== res n-exp))))))



(defn apply-ruleso [rules expr nexpr]
  (matche [rules]
          ([[?r . ?rs]] (conda
                         ((apply-ruleo ?r expr nexpr))
                         ((apply-ruleso ?rs expr nexpr))))))

(defn transform-with-rules [rules expr]
  (let [tmp (walk/prewalk #(or (first (run* [q] (apply-ruleso rules % q))) %) expr)]
    (if (= tmp expr) tmp (transform-with-rules rules tmp)))) 



