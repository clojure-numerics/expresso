(defproject expresso "0.2.1-SNAPSHOT"
  :description "a general Algebraic Expression manipulation library in clojure"
  :url "https://github.com/clojure-numerics/expresso"
  :license {:name "The MIT License"
            :url "http://opensource.org/licenses/mit-license.php"}
  :profiles {:dev {:dependencies [[org.clojure/tools.trace "0.7.8"]
                                  [criterium "0.4.3"]]}}
  :dependencies [[org.clojure/clojure "1.6.0"]
                 [instaparse "1.3.0"]
                 [org.clojure/core.memoize "0.5.6"]
                 [net.mikera/core.matrix "0.33.2"]
                 [org.clojure/core.logic "0.8.10"]]
  :source-paths ["src" "src/main/clojure"]
  :test-paths ["test" "src/test/clojure"]
  :aot [numeric.expresso.impl.pimplementation])

