(ns numeric.expresso.test-parse
  (:use [numeric.expresso.construct]
        [numeric.expresso.parse]
        [clojure.test]))

(deftest test-parse-expression
  (is (= (ex (+ 1 2)) (parse-expression "1+2")))
  (is (= (ex (+ 1 2 3 4)) (parse-expression "1+2+3+4")))
  (is (= (ex (+ (* 1 2 3) 4)) (parse-expression "1*2*3+4")))
  (is (= (ex (* 1 2 (+ 3 4))) (parse-expression "1*2*(3+4)")))
  (is (= (ex (+ 1 (* 2 (** 3 4)) 5)) (parse-expression "1+2*3**4+5"))))

(deftest test-parse-variables
  (is (= (ex (+ x 1)) (parse-expression "x+1"))))

(deftest test-parse-function
  (is (= (ex (abs x)) (parse-expression "abs(x)"))))

