(ns numeric.expresso.test-core
  (:use numeric.expresso.core)
  (:use [clojure.test :exclude [test-vars]])
  (:require [numeric.expresso.types :as types]
            [numeric.expresso.protocols :as protocols]
            [clojure.core.logic :as logic]))


(deftest test-ex
  (is (= 5 (ex 5)))
  (is (= '(+ x y) (ex (+ x y))))
  (is (not (empty? (meta (ex (+ x y))))))
  (is (not (empty? (meta (first (ex (+ x y)))))))
  (is (= '(+ a b) (ex (+ ^:matrix a ^:matrix b))))
  (is (= '(+ x (* x y)) (ex (+ x (* x y)))))
  (is (= '(+ x (* 3 y)) (let [x 3] (ex (+ x (* ~x y)))))))

(deftest test-ex'
  (is (= 5 (ex 5)))
  (is (= '(+ x y) (ex' (+ 'x 'y))))
  (is (= '(+ 3 3) (let [x 3] (ex' (+ 3 x)))))
  (is (= '(+ 3 x) (let [x 3] (ex' [x] (+ 3 x))))))

(deftest test-expression?
  (is (expression? (ex (+ 1 2))))
  (is (not (expression? [+ 1 2])))
  (is (expression? '(+ 1 2))))

(deftest test-constant?
  (is (not (constant? (ex (+ 1 2)))))
  (is (constant? [+ 1 2]))
  (is (not (constant? '(+ 1 2)))))


(deftest test-properties
  (is (= #{:positive}
         (properties (expresso-symbol 'x :properties #{:positive}))))
  (is (contains? (properties 1) :positive)))

(deftest test-vars
  (is (= '#{x y} (vars (ex (* x y x)))))
  (is (= '#{x} (vars 'x))))

(deftest test-shape
  (is (= [] (shape (ex (+ 1 2)))))
  (is (logic/lvar? (shape (matrix-symbol 'x)))))

(deftest test-expresso-symbol
  (is (= 'x (expresso-symbol 'x)))
  (is (= types/number (protocols/type-of (expresso-symbol 'x))))
  (is (= types/matrix
         (protocols/type-of (expresso-symbol 'x :type types/matrix))))
  (is (= types/matrix
         (protocols/type-of (expresso-symbol 'x :shape [2 3]))))
  (is (= [] (shape (expresso-symbol 'x))))
  (is (logic/lvar? (shape (expresso-symbol 'x :type types/matrix))))
  (is (= [2 2] (shape (expresso-symbol 'x :shape [2 2])))))


(deftest test-matrix-symbol
  (is (= types/matrix
         (protocols/type-of (matrix-symbol 'x))))
  (is (logic/lvar? (shape (matrix-symbol 'x))))
  (is (= [2 2] (shape (matrix-symbol 'x :shape [2 2])))))

(deftest test-zero-matrix
  (is (= #{:mzero} (properties (zero-matrix)))))

(deftest test-identity-matrix
  (is (= #{:midentity} (properties (identity-matrix)))))
  

;;see also test_parse.clj
(deftest test-parse-expression
  (is (= (ex (+ 1 2 3)) (parse-expression "1 + 2 + 3")))
  (is (= (ex (+ 1 (* 2 (** 3 4)) 5))
         (parse-expression "1+2*3**4+5")))
  (is (= (ex (= (+ (** (sin x) 2) (** (cos x) 2)) 1))
         (parse-expression "sin(x)**2 + cos(x)**2 = 1"))))

(deftest test-evaluate
  (is (== 6 (evaluate (ex (* 2 x)) {'x 3}))))

(deftest test-substitute
  (is (= (ex (+ x x (/ y z)))
         (substitute (ex (+ (* a b) (* a b) (/ c d)))
                     {(ex (* a b)) 'x 'c 'y 'd 'z}))))


(deftest test-simplify
  (is (= 4 (simplify (ex (+ 2 2)))))
  (is (= 137 (simplify (ex (+ (* 5 20) 30 7)))))
  (is (== 0 (simplify (ex (- (* 5 x) (* (+ 4 1) x))))))
  (is (== 0 (simplify (ex (* (/ y z) (- (* 5 x) (* (+ 4 1) x)))))))
  (is (= (ex (* 6 x)) (simplify (ex (* 3 2 x)))))
  (is (= (ex (* 720 x y z)) (simplify (ex (* 2 x 3 y 4 z 5 6)))))
  (is (= 7 (simplify (ex (+ x 3 4 (- x))))))
  (is (= (ex (* a (+ b c)))
         (simplify (ex (+ (* a b) (* a c) 5 -5)))))
  (is (nil? (simplify (ex (+ (* a b) (* a c) 5 -5)) :ratio 0.5))))

(deftest test-multiply-out
  (is (= (ex (+ (** e 2) (* 2 d e) (** d 2) (* b a) (* c a)))
         (multiply-out (ex (+ (* a (+ b c)) (** (+ d e) 2))))))
  (is (= (ex (+ (** c 3) (* 3 b (** c 2)) (* 3 (** b 2) c) (** b 3)
                (* 3 a (** c 2)) (* 6 a b c) (* 3 a (** b 2))
                (* 3 (** a 2) c) (* 3 (** a 2) b) (** a 3)))
         (multiply-out (ex (** (+ a b c) 3))))))

(deftest test-evaluate-constants
  (is (= (ex (+ (* 3 a) 20))
         (evaluate-constants (ex (+ (* (- 5 2) a) (* 4 5))))))
  (is (== 6 (evaluate-constants (substitute (ex (* 2 x)) {'x 3})))))


(deftest test-transform-to-polynomial-normal-form
  (is (= (ex (** x 3))
         (to-polynomial-normal-form 'x (ex (+ (** x 3) (* 3 (** x 2))
                                              (- (* 2 (** x 2))
                                                 (* 5 (** x 2))))) )))
  (is (= (ex (+ 1024 (* 3840 x) (* 9600 (** x 2)) (* 15840 (** x 3))
                (* 20340 (** x 4)) (* 19683 (** x 5)) (* 15255 (** x 6))
                (* 8910 (** x 7)) (* 4050 (** x 8)) (* 1215 (** x 9))
                (* 243 (** x 10))))
         (to-polynomial-normal-form 'x (ex (** (+ (* 3 x) 4 (* 3 (** x 2)))
                                               5)))))
  (is (= (ex (+ (* (+ 1 (* 2 a) (** a 2)) x) (* (+ 1 a) (** x 2))))
         (to-polynomial-normal-form 'x (ex (* (+ x a 1) (* x (+ 1 a))))))))

(deftest test-rearrange
  (is (= [(ex (= x (- 4 1)))]
         (rearrange 'x (ex (= (+ 1 x) 4)))))
  (is (= '[(= x 3) (= x (- 3))]
         (rearrange 'x (ex (= (abs x) 3)))))
  (is (nil? (rearrange 'x (ex (= (+ x x) 0))))))


(deftest test-solve
  (is (= #{2} (solve 'x (ex (= (+ 1 x) 3)))))
  (is (= '#{} (solve '#{x} (ex (= x (+ x 1))))))
  (is (= '_0 (solve '#{x} (ex (= x x)))))
  (is (= '#{0 1} (solve '#{x} (ex (= (* (sin x) (- x 1)) 0)))))
  (is (= #{4} (solve '#{x} (ex (= (+ 1 (* 2 (- 3 (/ 4 x)))) 5))))) 
  (is (= #{-4}
         (solve '#{x} (ex (= (* 3 x) (+ (* 4 x) 4))))))
  (is (= '#{(* 1/2 (+ (- a) (sqrt (+ (** a 2) -4))))
           (* 1/2 (+ (- a) (- (sqrt (+ (** a 2) -4)))))}
         (solve '#{x} (ex (= (+ (** x 2) (* a x) 1) 0)))))
  (is (= '#{{y (+ (* a 1/2) (* -1/4 (- (sqrt (+ (* -4.0 (** a 2)) 8))))),
             x (+ (* 1/2 a) (* (- (sqrt (+ (* -4.0 (** a 2)) 8))) 1/4))}
            {y (+ (* a 1/2) (* -1/4 (sqrt (+ (* -4.0 (** a 2)) 8)))),
             x (+ (* 1/2 a) (* (sqrt (+ (* -4.0 (** a 2)) 8)) 1/4))}}
       (solve '[x y] (ex (= (+ (** x 2) (** y 2)) 1))
              (ex (= (+ x y) a)))))
  (is (= '#{0 1 -1}
         (solve 'x (ex (= (- (** x 4) (** x 2)) 0)))))
  (is (= '#{1 3}
         (solve 'x (ex (= (+ (** 2 (* 2 x)) (- (* 5 (** 2 (+ x 1)))) 16) 0)))))
  (is (= #{10N}
         (solve 'x (ex (= (+ (* (/ 3 4) x) (/ 5 6)) (- (* 5 x) (/ 125 3)))))))
  (is (= #{3N}
         (solve 'x (ex (= (+ (/ (- (* 6 x) 7) 4)
                             (/ (- (* 3 x) 5) 7))
                          (/ (+ (* 5 x) 78) 28))))))
  (is (= #{17}
         (solve 'x (ex (= (sqrt (- x 8)) 3)))))
  (is (= #{-2 3}
         (solve 'x (ex (= (abs (- (* 2 x) 1)) 5)))))
  (is (= '#{{remaining2 (+ -15N (* 3/5 _0))}}
         (solve '[remaining2]
                (ex (= original b))
                (ex (= remaining1 (- original (/ original 4))))
                (ex (= remaining2 (- remaining1 (+ (/ remaining1 5) 15))))))))


(deftest test-solve-variable-order
  (is (= '#{{dx 4}} (solve 'dx (ex (= 4 dx)) (ex (= dt 5)) (ex (= cs (/ dt dx))))))
  (is (= '#{{s 5/9, m 5/3}}
         (solve ['s 'm] 
                (ex (= m (/ t x)))
                (ex (= s (/ m 3)))
                (ex (= t 5))
                (ex (= x 3)))))
  (is (= '#{{s 5/9, m 5/3}}
         (solve ['m 's] 
                (ex (= m (/ t x)))
                (ex (= s (/ m 3)))
                (ex (= t 5))
                (ex (= x 3))))))

(deftest test-differentiate
  (is (= (ex (* 2 x)) (differentiate '[x] (ex (** x 2)))))
  (is (= 2.0 (differentiate '[x x] (ex (** x 2)))))
  (is (= (ex (* 3 (** x 2))) (differentiate '[x] (ex (** x 3)))))
  (is (= (ex (* 12.0 (** x 3)))
         (differentiate '[x] (ex (* (** x 3) (* 3 x))))))
  (is (= (ex (* 36.0 (** x 2)))
         (differentiate '[x x] (ex (* (** x 3) (* 3 x)))))))

;;see also test-optimize

(deftest test-compile-expr
  (is (= 4 ((compile-expr [] (ex (+ (* 1 2) (* 2 1)))))))
  (is (= 8 ((compile-expr [x] (ex (+ (* x 2) (* 2 x)))) 2))))

(deftest test-compile-expr*
  (is (= 4 ((compile-expr* [] (ex (+ (* 1 2) (* 2 1)))))))
  (is (= 8 ((compile-expr* '[x] (ex (+ (* x 2) (* 2 x)))) 2))))

(deftest test-optimize
  (is (= 4 (evaluate (optimize (ex (+ (* 1 2) (* 2 1)))) {})))
  (is (= 8 (evaluate (optimize (ex (+ (* x 2) (* 2 x)))) {'x 2}))))

