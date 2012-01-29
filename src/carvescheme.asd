(in-package :asdf)

(defsystem "carvescheme"
  :description "carvescheme: a RnRS Scheme Compiler."
  :version "0.1.0"
  :author "quasicrane <quasi@kc4.so-net.ne.jp>"
  :licence "Public Domain"
  :components ((:file "package")
               (:file "match" :depends-on ("package"))
               (:file "util" :depends-on ("package"))
               (:file "carve" :depends-on ("match" "util"))
               (:file "test" :depends-on ("carve"))
               ))

;;fixme; should load quickload ...
                      