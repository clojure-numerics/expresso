(defproject expresso "0.2.2"
  :description "a general Algebraic Expression manipulation library in clojure"
  :url "https://github.com/clojure-numerics/expresso"
  :license {:name "The MIT License"
            :url "http://opensource.org/licenses/mit-license.php"}
  :profiles {:dev {:dependencies [[org.clojure/tools.trace "0.7.8"]
                                  [criterium "0.4.3"]]}}
  :dependencies [[org.clojure/clojure "1.8.0"]
                 [instaparse "1.4.5"]
                 [net.mikera/core.matrix "0.59.0"]
                 [org.clojure/core.memoize "0.5.8"]
                 [mschuene/core.logic "0.8.11.1"]]
  :source-paths ["src" "src/main/clojure"]
  :test-paths ["test" "src/test/clojure"]
  :aot [numeric.expresso.impl.pimplementation])

