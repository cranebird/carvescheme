(in-package :common-lisp-user)

(ql:quickload :com.gigamonkeys.test-framework)
(ql:quickload "cffi")

(defpackage :carve
  (:use :cl :com.gigamonkeys.test :cffi))

