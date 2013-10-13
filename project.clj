(defproject expresso "0.2.0"
  :description "a general Algebraic Expression manipulation library in clojure"
  :url "https://github.com/clojure-numerics/expresso"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :profiles {:dev {:dependencies [[org.clojure/tools.trace "0.7.6"]
                                  [criterium "0.4.2"]]}}
  :dependencies [[org.clojure/clojure "1.5.1"]
                 [instaparse "1.2.2"]
                 [org.clojure/core.memoize "0.5.6"]
                 [net.mikera/core.matrix "0.10.0"]
                 [org.clojure/core.logic "0.8.4"]]
  :source-paths ["src" "src/main/clojure"]
  :test-paths ["test" "src/test/clojure"]
  :aot [numeric.expresso.impl.pimplementation]

)

