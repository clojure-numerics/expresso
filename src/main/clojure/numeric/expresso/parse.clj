(ns numeric.expresso.parse
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [numeric.expresso.properties]
        [numeric.expresso.rules]
        [numeric.expresso.construct]
        [clojure.test])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.walk :as walk]
            [instaparse.core :as insta]
            [clojure.core.logic.unifier :as u]
            [numeric.expresso.utils :as utils]))



(def arithmetic
  (insta/parser
    "expr = add-sub
     <add-sub> = mul-div | add | sub
     add = add-sub <'+'> mul-div
     sub = add-sub <'-'> mul-div
     <mul-div> = exp-term | mul | div
     mul = mul-div <'*'> exp-term
     div = mul-div <'/'> exp-term
     <exp-term> = term | expon
     expon = exp-term <'**'> term
     <term> = literal | <'('>  expr <')'>
     <literal> = number | symbol | vec | (<' '>* literal <' '>*)
     vec = <'['> expr* <']'>
     symbol = #'[a-zA-Z]'+
     number = floating-point-number | int 
     <floating-point-number> = int  | (int frac) | (int exp) |
                               (int frac exp) | (floating-point-number 'M')
     <int> = digit| (#'[1-9]' digits) |('+' digit) |('+' #'[1-9]' digits)|
             ('-' digit) |('-' #'[1-9]' digits) | (int 'M')
     <frac> = '.' digits
     <exp> = ex digits
     <digits> = digit | (digit digits)
     <digit> = #'[0-9]'
     <ex> = 'e' | 'e+' | 'e-' | 'E' | 'E+' | 'E-'"))

(def parse-simplification-rules
  [(rule (ex (* (* ?&*) ?&*r)) :=> (ex (* ?&* ?&*r)))
   (rule (ex (+ (+ ?&*) ?&*r)) :=> (ex (+ ?&* ?&*r)))
   (rule (ex (+ ?x)) :=> ?x)
   (rule (ex (* ?x)) :=> ?x)])
 
(defn parse-expression [expr]
  (->> (arithmetic expr)
       (insta/transform
        {:number (comp read-string str)
         :expon (partial ce 'numeric.expresso.core/**)
         :div (partial ce `/)
         :mul (partial ce `*)
         :add (partial ce `+)
         :sub (partial ce `-)
         :expr identity
         :vec vector
         })
       (transform-with-rules parse-simplification-rules)))

