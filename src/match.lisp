(in-package :carve)

(defun single? (x)
  (and (consp x) (null (cdr x))))

;; (quote obj)
(defun quoted-symbol-p (x)
  "Return t when x is '(quote obj)"
  (and (consp x) (eql (car x) 'quote) (single? (cdr x))))

(defun pattern-repeat-p (pattern)
  "Return t if pattern repeats."
  (and (consp pattern)
       (consp (cdr pattern))
       (eql (cadr pattern) '|...|)))

(defun generate-predicate (pattern x)
  "Generate predicte for pattern."
  (cond
    ((null pattern)
     `((null ,x)))
    ((numberp pattern)
     `((eql ,x ,pattern)))
    ((quoted-symbol-p pattern)
     ;;`((equal ,x ',(cadr pattern))))
     `((eql ,x ',(cadr pattern))))
    ((eql pattern :_) ;; match every thing
     `(t))
    ((keywordp pattern)
     `((eql ,x ,pattern)))
    ((consp pattern)
     (cond
       ((pattern-repeat-p pattern)
        ;;(and (consp (cdr pattern)) (eql (cadr pattern) '|...|)) ;; (pat ...)
        (let ((arg (gensym "arg"))
              (fn (gensym "fn")))
          `((labels ((,fn (,arg)
                       (cond
                         ((null ,arg) t)
                         ((and (consp ,arg) ,@(generate-predicate (car pattern) `(car ,arg)))
                          (if (cdr ,arg)
                              (,fn (cdr ,arg))
                              t)))))
              (,fn ,x))
            )))
       (t
        `((consp ,x)
          ,@(generate-predicate (car pattern) `(car ,x))
          ,@(generate-predicate (cdr pattern) `(cdr ,x))))))
    ((eql pattern t)
     nil)
    (t
     nil)))

(defun pattern->binding (pattern x &optional repeat)
  (cond
    ((null pattern) nil)
    (repeat
     (cond
       ((keywordp pattern)
        nil)
       ((eql pattern '|...|)
        nil)
       ((atom pattern)
        `((,pattern (mapcar #'identity ,x))))
       (t
        `(,@(pattern->binding (car pattern) `(mapcar #'car ,x) t)
            ,@(pattern->binding (cdr pattern) `(mapcar #'cdr ,x) t)))))
    (t
      (cond
        ((numberp pattern) nil)
        ((quoted-symbol-p pattern) nil)
        ((keywordp pattern) nil)
        ((eql pattern t) nil)
        ((atom pattern) `((,pattern ,x)))
        ((single? pattern)
         `(,@(pattern->binding (car pattern) `(car ,x))))
        ((consp pattern)
         (cond
           ((and (consp (cdr pattern)) (eql (cadr pattern) '|...|)) ;; (pat ...)
            (let ((pat (car pattern)))
              (pattern->binding pat x t)))
           (t
            `(,@(pattern->binding (car pattern) `(car ,x))
                ,@(pattern->binding (cdr pattern) `(cdr ,x))))))))))
  
;; x => (a)  ===> ((a (car x)))
;; x => (a ...) ===> ((a x))
;; x => (a ...) ===> ((a (mapcar #'identity x)))

;; x => (a b) ===> ((a (car x)) (b (car (cdr x))))
;; x=> ((a b) ...) ===> ((a (loop for z in x collect (car x))) (b loop for z in x collect (car (cdr x))))


(defun validate-pattern (pattern-body)
  (let ((ht (make-hash-table :test #'equal))
        (x (gensym "x")))
    (loop :for (pattern . body) :in pattern-body
       :do
       (multiple-value-bind (val present-p)
           (gethash (generate-predicate pattern x) ht)
         (if present-p
             (error "~%same pattern found: ~s~%~s" pattern val)
             (setf (gethash (generate-predicate pattern x) ht) pattern))))))

(defmacro match (expr &rest pattern-body)
  (validate-pattern pattern-body)
  (let ((x (gensym "x")))
    `(let ((,x ,expr))
       (cond
         ,@(loop :for (pattern . body) :in pattern-body
              :collect
              `((and ,@(generate-predicate pattern x))
                (let (,@(pattern->binding pattern x))
                  ,@body)))))))

(defun pattern-n->predicate-n (pattern vs)
  "patterns into 'and clauses"
  `(and
    ,@(loop :for p :in pattern :for v :in vs
         :append (generate-predicate p v))))

(defmacro match-n ((&rest es) &body pattern-body)
  ;;(validate-pattern pattern-body)
  `(cond
     ,@(loop :for (pattern . body) :in pattern-body
          :collect
          `((,@(pattern-n->predicate-n pattern es))
            (let ,(loop :for p :in pattern :for v :in es
                     :append (pattern->binding p v))
              ,@body)))))

