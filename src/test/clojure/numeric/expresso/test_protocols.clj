(ns numeric.expresso.test-protocols
  (:use [numeric.expresso.protocols ])
  (:use clojure.test)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        [numeric.expresso.rules]
        [numeric.expresso.construct]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd])
  (:import [numeric.expresso.protocols Expression AtomicExpression MatrixSymbol])
  (:require [clojure.core.logic.unifier :as u]))

(deftest test-unification
  (is (= [1] (run* [q] (== (Expression. `+ [q 2 3]) (Expression. `+ [1 2 3])))))
  (is (= ['_0] (run* [q] (== (Expression. `+ [q 2 3]) (Expression. `+ [q 2 3])))))
  (is (= [] (run* [q] (== (Expression. `+ [q 1 3]) (Expression. `+ [q 2 3])))))
  (is (= ['_0] (run* [q] (== (Expression. `+ [q 1 2]) [`+ q 1 2]))))
  (is (= ['_0] (run* [q] (== [`+ q 1 2] (Expression. `+ [q 1 2])))))
  (is (= [] (run* [q] (== [`+ q q q] (Expression. `+ [q 1 2])))))
  (is (= [] (run* [q] (== (Expression. `+ [q 1 2]) [`+ q q q]))))
  (is (= [`+] (run* [q] (== (Expression. `+ [1 2 3]) [q 1 2 3])))))

(deftest test-sequential
  (is (= `+ (first (Expression. `+ [1 2 3]))))
  (is (= [1 2 3] (rest (Expression. `+ [1 2 3]))))
  (is (= (Expression. `* [1 2 3]) (first (rest (Expression. `+ [(Expression. `* [1 2 3])]))))))


(deftest test-matrix-symbol-unification
  (is (= '(_0) (run* [q] (== (MatrixSymbol. 'a nil nil)
                           (MatrixSymbol. 'a nil nil)))))
  (is (= '(_0) (run* [q] (== (MatrixSymbol. 'a nil nil)
                             (with-meta 'a {:shape nil})))))
  (is (= (MatrixSymbol. 'a 2 nil)
         (first (run* [q] (fresh [a]
                                 (== a 2)
                                 (== q (MatrixSymbol. 'a a nil))))))))


(deftest test-shape
  (is (= '() (shape 1)))
  (is (= [2 2] (shape [[1 2][3 4]])))
  (is (= '() (shape 'bla))))



(def lhs (lvar 'lhs false))
(def rhs (lvar 'rhs false))
(def transs (lvar 'transs false))

(def v1 (add-constraint [lhs rhs] [== lhs rhs]))
(def v2 (add-constraint [lhs transs] [== lhs transs]))

(def vv1 (check-constraints v1))
(def vv2 (check-constraints v2))

(def cv (add-constraint [vv1 vv2] [== lhs rhs]))
(def cv (add-constraint cv [== lhs transs]))

(def ccv (check-constraints cv))

(deftest test-check-constraints
  (is (= [rhs rhs] vv1))
  (is (= [transs transs] vv2))
  (is (= 1 (count (into #{} (flatten ccv))))))

(deftest test-add-constraint
  (is (= 1 (count (constraints (add-constraint 'a [== 0 0]))))))