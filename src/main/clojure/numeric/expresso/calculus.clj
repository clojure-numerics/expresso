(ns numeric.expresso.calculus
  (:use [numeric.expresso.construct]
        [numeric.expresso.protocols]
        [numeric.expresso.simplify]
        [numeric.expresso.rules]))

;;implementation of the diff-function multimethod which dispatches to the
;;right operator.

(defmethod diff-function '+ [[expr v]]
  (let [args (expr-args expr)]
    (cev '+ (map #(differentiate-expr % v) args))))

(defmethod diff-function '* [[expr v]]
  (let [args (vec (expr-args expr))
        c (count args)]
    (cev '+ (loop [i 0 exprs []]
              (if (< i c)
                (recur (inc i)
                       (conj exprs
                             (cev '* (concat (subvec args 0 i)
                                             [(differentiate-expr
                                               (nth args i) v)]
                                             (subvec args (inc i))))
                             ))
                exprs)))
    ))


(defmethod diff-function '- [[expr v]]
  (let [args (vec (expr-args expr))]
    (if (= 1 (count args))
      (ce '- (differentiate-expr (first args) v))
      (differentiate-expr
       (cev '+ (concat [(first args)] (map #(ce '- %) (rest args)))) v))))

(defmethod diff-function '/ [[expr v]]
  (let [args (vec (expr-args expr))]
    (if (= 1 (count args))
      (differentiate-expr (ce '** (first args) -1) v)
      (differentiate-expr
       (cev '* (concat [(first args)] (map #(ce '/ %) (rest args)))) v))))

(defmethod diff-function '** [[expr v]]
  (let [args (vec (expr-args expr))]
    (if (= (count args) 2)
      (if (= (nth args 0) v)
        (ce '* (nth args 1) (ce '** (nth args 0)
                                     (apply-rules eval-rules
                                                  (ce '- (nth args 1) 1)))
                 (differentiate-expr (nth args 0) v))
        (differentiate-expr
         (ce 'exp (ce '* (nth args 1) (ce 'log (nth args 0)))) v))
      (differentiate-expr
       (cev '** (concat [(ce '** (nth args 0) (nth args 1))] (subvec args 2)))
       v))))

(defmethod diff-function 'log [[expr v]]
  (ce '* (ce '/ (second expr)) (differentiate-expr (second expr) v)))

(defmethod diff-function 'sin [[expr v]]
  (ce '* (ce 'cos (second expr)) (differentiate-expr (second expr) v)))

(defmethod diff-function 'cos [[expr v]]
  (ce '* (ce '- (ce 'sin (second expr))) (differentiate-expr (second expr) v)))

(defmethod diff-function 'exp [[expr v]]
  (ce '* (cev 'exp (rest expr)) (differentiate-expr (second expr) v)))

(def differentiation-rules
  (with-meta
    (concat eval-rules universal-rules
            simplify-rules)
    {:id :dr}))

(defn differentiate
  "differentiates expression in regard to variable v"
  [v expr]
  (->> expr
       (#(differentiate-expr % v))
       (transform-expression differentiation-rules)))