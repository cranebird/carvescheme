(in-package :carve)

(defun set-scm-macro-character ()
  "Set macro-character for scheme #f and #t."
  (set-dispatch-macro-character #\# #\t
                                #'(lambda (stream subchar arg)
                                    (declare (ignore stream subchar arg))
                                    '|#t|))
  (set-dispatch-macro-character #\# #\f
                                #'(lambda (stream subchar arg)
                                    (declare (ignore stream subchar arg))
                                    '|#f|)))

(defun show-doc (&optional (pkg *package*))
  "Print documentation strings of the package PKG."
  (loop for sym being the present-symbols in (find-package pkg)
     if (documentation sym 'function)
     collect (cons (string sym) (documentation sym 'function))
     into docs
     finally
       (loop for (sym . doc) in (sort docs #'string-lessp :key #'car)
          do (format t "~24,,,a : ~a~%" sym doc))))
