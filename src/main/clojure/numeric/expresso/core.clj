(ns numeric.expresso.core
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        clojure.test)
  (:require [numeric.expresso.utils :as util])
  (:require [numeric.expresso.construct :as c])
  (:require [numeric.expresso.solve :as s])
  (:require [numeric.expresso.rules :as r])
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.logic.unifier :as u]))

(set! *warn-on-reflection* true)
(set! *unchecked-math* true)

(declare ex* mapo resulto)
(comment
  "simple example"
  (run* [q] (s/simplifyo '(+ x 0) q))
  ;=> (x)
  "rules are applied recursively"
  (run* [q] (s/simplifyo '(* x (+ 0 (* 3 (* x 0)))) q))
  ;=> (0)

  "calculate is also just a rule, which checks if there is no variable in expression and calculates it"
  (run* [q] (s/simplifyo '(+ (* 3 4) (+ (* x 0) 7)) q))
  ;=> (19)
 )
  

(def exp (with-meta '(+ 1 0) {:properties [:commutative]}
					   ))

(defn has-metao [q m]
  (== (meta q) (partial-map m)))

(defn is-commutativeo [exp]
  (fresh [m]
         (has-metao exp {:properties m})
         (membero :commutative m)))

(defn isao [a b]
  (== true (isa? a b)))

(defn expression-match [e1 e2]
  )