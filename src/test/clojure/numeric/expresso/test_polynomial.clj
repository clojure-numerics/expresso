(ns numeric.expresso.test-polynomial
  (:use numeric.expresso.impl.polynomial)
  (:use clojure.test))

(deftest test-to-poly-normal-form
  (is (= 7 (to-poly-normal-form '(+ 3 x 4 (- x)))))
  (is (= (poly 'x (poly 'y 0 2) 2) (to-poly-normal-form '(+ x y y x)))))