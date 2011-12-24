(in-package :carve)

(defvar *asm-output* t
  "write assembler to this stream.")

(defvar *fixnum-tag* #b00)
(defvar *fixnum-shift* 2)
(defvar *fixnum-mask* #b11)
(defvar *empty-list* #b01001111) ;; see Ghu[2] A.2 . not ghu[1]

(defvar *char-tag* #b00001111)
(defvar *char-shift* 8)
(defvar *char-mask* #b11111111)

;;(defvar *boolean-mask* #b111111) ;; 63
(defvar *scheme-t* #b00111111) ;; 63 Ghu[2]
(defvar *scheme-f* #b00101111) ;; 47 Ghu[2]

;; ASCII chars
;; ----------------------------------------------------------------
;; 000000000000000000000000000000000000000000000000XXXXXXXX00001111

(defvar *asm-file* "/home/cranebird/carvescheme/src/asm.s")
(defvar *scheme-entry-lib-file* "/home/cranebird/carvescheme/src/scm.lib")
(defvar *scheme-driver-c-file* "/home/cranebird/carvescheme/src/driver.c")
(defvar *scheme-driver-exe* "/home/cranebird/carvescheme/src/main")

(define-condition scheme-compile-error (simple-error)
  ((expr :initarg :expr :accessor scheme-compile-error-expr)
   (reason :initarg :reason :accessor scheme-compile-error-reason))
  (:report (lambda (condition stream)
             (format stream "SCHEME Compile Error: Fail to compile ~a~%~a"
                     (scheme-compile-error-expr condition)
                     (scheme-compile-error-reason condition)))))

(defun emit (str &rest args)
  (apply 'format *asm-output* str args)
  (terpri *asm-output*))

(defun primcall-p (expr)
  "return non-nil if expr is primitive function call."
  (and (consp expr)
       (member (car expr)
               '(%add1 %sub1
                 %fixnum->char %char->fixnum
                 %zero? %null? %fixnum? %boolean?))))

(defun primcall-op (expr)
  "return operator of primitive function call."
  (car expr))

(defun primcall-operand1 (expr)
  "return operand-1 of primitive function call."
  (nth 1 expr))

(defun primcall-operand (expr)
  "return operands of primitive function call."
  (cdr expr))

(defun immediate-rep (x)
  (cond
    ((integerp x) (ash x *fixnum-shift*))
    ((null x) *empty-list*)
    ((characterp x)
     (logior (ash (char-code x) 8) #b00001111))
    ((eql x '|#t|)
     *scheme-t*)
    ((eql x '|#f|)
     *scheme-f*)
    ))

;; 64 bit 
;; max: 9223372036854775807 (= 2^63 - 1)
;; min:-9223372036854775808 (= - 2^63)

;; tagged pointer:
;; max: 2305843009213693951 (= 2^61 - 1)
;; min:-2305843009213693952 (= - 2^61)

(defvar most-positive-immediate-integer
  (1- (expt 2 61)))

(defvar most-negative-immediate-integer
  (- (expt 2 61)))

(defun immediate-integer-p (x)
  (and (integerp x)
       (<= most-negative-immediate-integer x)
       (<= x most-positive-immediate-integer)))

(defun immediate-p (x)
  (or (immediate-integer-p x) (null x)
      (characterp x)
      (eql x '|#t|)
      (eql x '|#f|)
      ))

(defun emit-expr (x)
  (cond
    ((immediate-p x)
     (emit "movq $~a, %rax" (immediate-rep x)))
    ((primcall-p x) ;; unary primitive
     (emit-unary-primitive (primcall-op x) (primcall-operand1 x)))
    (t
     (error (make-condition 'scheme-compile-error
                            :expr x :reason "unknown expr")))
     ))

(defgeneric emit-unary-primitive (name arg)
  (:documentation "emit primitive"))

(defmacro define-unary-primitive (opcode (arg) &rest body)
  (let ((name (gensym)))
  `(defmethod emit-unary-primitive ((,name (eql ',opcode)) ,arg)
     ,@body)))

(define-unary-primitive %add1 (x)
  (emit-expr x)
  (emit "addq $~a, %rax" (immediate-rep 1)))

(define-unary-primitive %sub1 (x)
  (emit-expr x)
  (emit "subq $~a, %rax" (immediate-rep 1)))

(define-unary-primitive %fixnum->char (x)
  (emit-expr x)
  (emit "shlq $~a, %rax" (- *char-shift* *fixnum-shift*))
  (emit "orq $~a, %rax" *char-tag*))

(define-unary-primitive %char->fixnum (x)
  (emit-expr x)
  (emit "shrq $~a, %rax" (- *char-shift* *fixnum-shift*)))

(define-unary-primitive %zero? (x)
  (emit-expr x)
  (emit "cmpq $0, %rax")
  (emit "movq $0, %rax")
  (emit "sete %al")
  (emit "salq $4, %rax")
  (emit "orq $47, %rax") 
  )

(define-unary-primitive %null? (x)
  (emit-expr x)
  (emit "cmpq $79, %rax") ;; *empty-list*
  (emit "movq $0, %rax")
  (emit "sete %al")
  (emit "salq $4, %rax")
  (emit "orq $47, %rax") 
  )

(define-unary-primitive %boolean? (x)
  (emit-expr x)
  (emit "andq $3, %rax")
  (emit "cmpq $0, %rax")
  (emit "movq $0, %rax")
  (emit "sete %al")
  (emit "salq $4, %rax")
  (emit "orq $47, %rax") 
  )

(define-unary-primitive %fixnum? (x)
  (emit-expr x)
  (emit "andq $3, %rax")
  (emit "cmpq $0, %rax")
  (emit "movq $0, %rax")
  (emit "sete %al")
  (emit "salq $4, %rax")
  (emit "orq $47, %rax") 
  )



;; (define-unary-primitive %fixnum? (x)
;;   (emit-expr x)
;;   (emit "cmpq $0, %rax")
;;   (emit "movq $0, %rax")
;;   (emit "sete %al")

(defun compile-program (x)
  (flet ((emit-header ()
           (emit "	.text")
           (emit "	.p2align 4,,15")
           (emit ".globl scheme_entry")
           (emit "	.type	scheme_entry, @function")
           (emit "scheme_entry:")))
    (emit-header)
    (emit-expr x)
    (emit "ret")
    ))

(defun write-asm (x)
  (with-open-file (*asm-output* *asm-file* :direction :output :if-exists :supersede)
    (compile-program x)))

(defun load-scheme-entry ()
  (sb-ext:run-program "/usr/bin/gcc" `("-g" "-shared" ,*asm-file* "-o" ,*scheme-entry-lib-file*))
  (sb-ext:run-program "/usr/bin/gcc" `("-g" ,*asm-file* ,*scheme-driver-c-file* "-o" ,*scheme-driver-exe*))
  (load-foreign-library *scheme-entry-lib-file*)
  (defcfun "scheme_entry" :int64))

(defun format-scheme-value (val)
  "printer"
  (cond
    ((eql (logand val *fixnum-mask*) *fixnum-tag*)
     (ash val (- *fixnum-shift*)))
    ((eql val *empty-list*)
     "()")
    ((eql val *scheme-t*)
     "#t")
    ((eql val *scheme-f*)
     "#f")
    ((eql (logand val *char-mask*) *char-tag*)
     (format nil "#\\~a" (code-char (ash val (- *char-shift*)))))))

(defun run (x &optional (out t))
  (write-asm x)
  (load-scheme-entry)
  (let ((val (scheme-entry)))
    (format out "~a" (format-scheme-value val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; test
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftest test-immediate ()
  (check
    (equal "13" (run 13 nil))
    (equal "7" (run 7 nil))
    (equal "()" (run nil nil))
    (equal "#\\A" (run #\A nil))
    (equal "#\\1" (run #\1 nil))
    (equal "#\\9" (run #\9 nil))
    (equal "#t" (run '|#t| nil))
    (equal "#f" (run '|#f| nil))
    ))

(deftest test-unary-primitive ()
  (check
    (equal "1" (run '(%add1 0) nil))
    (equal "2" (run '(%add1 1) nil))
    (equal "0" (run '(%add1 -1) nil))
    (equal "-1" (run '(%add1 -2) nil))
    (equal "-2" (run '(%add1 -3) nil))
    (equal "3" (run '(%add1 (%add1 (%add1 0))) nil))
    (equal "1" (run '(%add1 (%sub1 (%add1 0))) nil))
    (equal "#\\A" (run `(%fixnum->char ,(char-code #\A)) nil))
    (equal "#\\l" (run `(%fixnum->char ,(char-code #\l)) nil))
    (equal (format nil "~a" (char-code #\Z)) (run `(%char->fixnum #\Z) nil))
    (equal "#t" (run '(%zero? 0) nil))
    (equal "#f" (run '(%zero? 3) nil))
    (equal "#t" (run '(%zero? (%add1 -1)) nil))
    (equal "#f" (run '(%zero? (%sub1 -1)) nil))
    (equal "#t" (run '(%zero? (%sub1 (%sub1 2))) nil))

    (equal "#t" (run '(%null? nil) nil))
    (equal "#f" (run '(%null? 3) nil))
    (equal "#f" (run '(%null? 0) nil))

    (equal "#t" (run '(%fixnum? 0) nil))
    (equal "#t" (run '(%fixnum? 4) nil))
    (equal "#t" (run '(%fixnum? -2) nil))
    (equal "#t" (run '(%fixnum? (%add1 -1)) nil))
    (equal "#f" (run '(%fixnum? |#t|) nil))
    (equal "#f" (run '(%fixnum? |#f|) nil))
    (equal "#f" (run '(%fixnum? (%zero? 3)) nil))
    (equal "#f" (run '(%fixnum? (%zero? 0)) nil))
    ))

(deftest test-unary-primitive-edge ()
  (check
    (equal (format nil "~a" most-positive-immediate-integer)
           (run `(%add1 ,(1- most-positive-immediate-integer)) nil))
    (equal (format nil "~a" most-negative-immediate-integer)
           (run `(%sub1 ,(1+ most-negative-immediate-integer)) nil))
    ))
