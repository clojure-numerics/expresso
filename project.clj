(defproject expresso "0.1.0-SNAPSHOT"
  :description "FIXME: write description"
  :url "http://example.com/FIXME"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :dependencies [[org.clojure/clojure "1.5.1"]
                 [org.clojure/tools.trace "0.7.5"]
                 [org.clojure/core.logic "0.8.3"]]

  :source-paths ["src" "src/main/clojure"]
  :test-paths ["test" "src/test/clojure"]
  :aot [numeric.expresso.protocols]

)

