(ns numeric.expresso.parse
  (:refer-clojure :exclude [==])
  (:use [numeric.expresso.rules]
        [numeric.expresso.construct])
  (:require [clojure.walk :as walk]
            [instaparse.core :as insta]
            [numeric.expresso.protocols :as protocols]
            [numeric.expresso.utils :as utils]))


;; instaparse grammar for infix expression, used by Expresso's parser.
(def arithmetic
  (insta/parser
   " expr = equals
     <equals> = add-sub | eq
     eq = add-sub <'='> add-sub
     <add-sub> = mul-div | add | sub
     add = add-sub <'+'> mul-div
     sub = add-sub <'-'> mul-div
     <mul-div> = exp-term | mul | div
     mul = mul-div <'*'> exp-term
     div = mul-div <'/'> exp-term
     <exp-term> = func-term | expon
     expon = exp-term <'**'> term
     <func-term> = term 
     func = (symbol <'('> args <')'> <' '>*) | (symbol <'('> <' '>* <')'> <' '>*)
     args = expr | expr <','> args 
     <term> = literal | <' '>* literal <' '>* | <'('>  expr <')'> 
     <literal> = number | symbol | vec | func
     vec = <'['> expr* <']'>
     symbol = math-symbol | lit-symbol
     math-symbol = #'[a-zA-Z]' #'[a-zA-Z0-9]'*
     lit-symbol = <'`'> <' '>* clojure-symbol <'`'>*
     clojure-symbol = #'[a-zA-Z.*+!_?$&=/-]' #'[a-zA-Z.*+!_?$&=0-9:#/-]'*
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

(defn- transform-if-successful [expr]
  (if-let [op (protocols/expr-op expr)]
    (transform-with-rules parse-simplification-rules expr)
    expr))

(defn parse-expression
  "parses the given string to an expresso expression. Supports all normal
   expressions in infix notation."
  [expr]
  (->> (arithmetic expr)
       (insta/transform
        {:number (comp read-string str)
         :expon (partial ce 'numeric.expresso.core/**)
         :div (partial ce `/)
         :mul (partial ce `*)
         :add (partial ce `+)
         :sub (partial ce `-)
         :eq  (partial ce '=)
         :expr identity
         :vec vector
         :symbol identity
         :math-symbol (fn [& r] (symbol (apply str r)))
         :clojure-symbol (fn [& r] (symbol (apply str r)))
         :lit-symbol identity
         :args (fn [& r]
                 (if (= (count r) 1)
                           r (conj (second r) (first r))))
         :func (fn [symb & rest]
                 (if (seq rest)
                   (cev symb (first rest)) (cev symb [])))
         })
       transform-if-successful))
