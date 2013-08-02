(ns numeric.expresso.types)

(def matrix ::matrix)
(def number ::number)
(def integer ::integer)
(def long ::long)
(def double ::double)
(def number ::number)


(derive integer number)
(derive long number)
(derive double number)