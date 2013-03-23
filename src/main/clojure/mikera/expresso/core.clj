(ns mikera.expresso.core)

(set! *warn-on-reflection* true)
(set! *unchecked-math* true)

(declare ex*)

;; ========================================
;; Expression datatype
;; node is either: 
;;  - a constant value
;;  - a list of (Operation Expression+)
(deftype Expression [node vars]
  java.lang.Object
    (hashCode [a]
      (.hashCode node))
    (equals [a b]
      (and (instance? Expression b) (== node (.node b)) (== vars (.vars b))))
    (toString [this]
      (str node)))



(defn constant? [^Expression x]
  (not (seq? (.node x))))

(defn- express-list 
  ([[op & exprs]]
    (cons op (map ex* exprs))))

(defn ex* 
  ([expr]
    (cond 
      ;; an operation with child expressions
      (seq? expr)
        (let [childs (express-list expr)]
          (Expression. childs 
                      (reduce (fn [s ^Expression x] (into s (.vars x))) #{} (rest childs))))
      ;; a symbol
      (symbol? expr)
        (Expression. expr #{expr})
      ;; else must be a constant
      :else
        (Expression. expr nil))))

(defmacro ex 
  "Constructs an Expression."
  ([expr]
    (ex* expr)))