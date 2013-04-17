expresso
========

Experimental combination of core.logic and core.matrix to allow reasoning with vectors / mathematical expressions

WORK IN PROGRESS: not much to see here yet!

### Objectives

expresso aims to be a general library for manipulating mathematical expressions.
In particular it should provide following features

 - Enable mathematical expressions to be encoded
 - Support arbitrary symbols as unknowns / variables in expression
 - Provide a standart (canonical?) form for expressions on which more sophisticated functionality can be built
 - An Optimizer, which optimizes expression for excecution on core.matrix
 - A Solver, which finds analytical (or numerical?) solutions to sets of expressions 
 - Full compatibility with [core.matrix](https://github.com/mikera/matrix-api)
 
 
### Implementation ideas

Central concept is an *expression*, in the mathematical sense. Expresso is a library for defining, manipulating and analysing expressions.

Design questions:

 - Is there a different between normal expressions and equations (expressions of equality)?
 - Feasible to use core.logic to search for solutions?
 - Expressions should be wrapped in deftypes?
 - Values can be any core.matrix n-dimensional array?
 - Need a way of handling vector / matrix expressions. 
 - Should an expression implement core.matrix protocols? If so how do semantics work: does multiplying an expression by a vector produce a new modified expression? 
 
### Syntax ideas

```clojure
;; ex macro constructs expression data structures from regular s-expressions. 
(def F1 (ex (= Y (+ X Z)))
(def F2 (ex (= X [1 2 3]))
(def F3 (ex (= Z (* 2.0 X)))

;; solver looks for numerical solutions to systems of equations
(solve [Y] F1 F2 F3)
=> ([3.0 6.0 9.0])         ;; single solution

;; solutions may have unknowns?
(solve [X] F3)
=> ((* 0.5 Z))
```



