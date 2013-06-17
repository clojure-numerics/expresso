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


;;logic stuff



;; (run* [q] (fresh [a b] (expo '+ [a b] q)))
;; => ((+ _0 _1))


;; (run* [q] (mapo inco [1 2] q))




;; (run* [q] (resulto 10 q))
;; => 10
;;
;; (run* [q] (resulto [+ 5 6] q))
;; => 11



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; a little proof of concept rule based translator


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
  

