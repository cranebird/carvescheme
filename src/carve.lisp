;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; carve.lisp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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

(defun emit-asm (ir)
  (assert (or (null ir) (consp ir)) (ir) "emit-ir: except cons, but got: ~a" ir)
  (if (null ir)
      nil
      (progn
        (match (car ir)
          (('SET ('REG r) v)
           (emit "movq $~a, %~a" v r))
          (('ADD v ('REG r))
           (emit "addq $~a, %~a" v r))
          (('SUB v ('REG r))
           (emit "subq $~a, %~a" v r))
          (('SHL v ('REG r))
           (emit "shlq $~a, %~a" v r))
          (('SHR v ('REG r))
           (emit "shrq $~a, %~a" v r))
          (('OR v ('REG r))
           (emit "orq $~a, %~a" v r))
          (('AND v ('REG r))
           (emit "andq $~a, %~a" v r))
          (('CMP v ('REG r))
           (emit "cmpq $~a, %~a" v r))
          (('SETE ('REG r))
           (emit "sete %~a" r))
          (('SAL v ('REG r))
           (emit "salq $~a, %~a" v r))
          (('JE label)
           (emit "je ~a" label))
          (('JMP label)
           (emit "jmp ~a" label))
          (('DEFLABEL label)
           (emit "~a:" label))
          (t
           (error "emit-asm error: ~a" ir))
          )
        (emit-asm (cdr ir)))))

(defun genlabel ()
  (gensym "Label"))
  
(defun expr->ir (x)
  "compile expression X into Carve IR."
  (let ((acc '(REG "rax")))
    (if(immediate-p x)
       `((SET ,acc ,(immediate-rep x)))
       (match x
         (('%add1 expr)
          `(,@(expr->ir expr)
              (ADD ,(immediate-rep 1) ,acc)))
         (('%sub1 expr)
          `(,@(expr->ir expr)
              (SUB ,(immediate-rep 1) ,acc)))
         (('%fixnum->char expr)
          `(,@(expr->ir expr)
              (SHL ,(- *char-shift* *fixnum-shift*) ,acc)
              (OR ,*char-tag* ,acc)))
         (('%char->fixnum expr)
          `(,@(expr->ir expr)
              (SHR ,(- *char-shift* *fixnum-shift*) ,acc)))
         (('%zero? expr)
          `(,@(expr->ir expr)
              (CMP 0 ,acc)
              (SET ,acc 0)
              (SETE (REG "al"))
              (SAL 4 ,acc)
              (OR ,*scheme-f* ,acc)))
         (('%null? expr)
          `(,@(expr->ir expr)
              (CMP ,*empty-list* ,acc)
              (SET ,acc 0)
              (SETE (REG "al"))
              (SAL 4 ,acc)
              (OR ,*scheme-f* ,acc)))
         (('%boolean? expr)
          `(,@(expr->ir expr)
              (AND ,*scheme-f* ,acc)
              (CMP ,*scheme-f* ,acc)
              (SET ,acc 0)
              (SETE (REG "al"))
              (SAL 4 ,acc)
              (OR ,*scheme-f* ,acc)))
         (('%fixnum? expr)
          `(,@(expr->ir expr)
              (AND ,3 ,acc)
              (CMP ,0 ,acc)
              (SET ,acc 0)
              (SETE (REG "al"))
              (SAL 4 ,acc)
              (OR ,*scheme-f* ,acc)))
         
         (('if test conseq altern)
          (let ((alt-label (genlabel))
                (end-label (genlabel)))
            `(,@(expr->ir test)
                (CMP ,*scheme-f* ,acc)
                (JE ,alt-label)
                ,@(expr->ir conseq)
                (JMP ,end-label)
                (DEFLABEL ,alt-label)
                ,@(expr->ir altern)
                (DEFLABEL ,end-label)))
          )

         (t
          (error (make-condition 'scheme-compile-error
                            :expr x :reason "unknown expr")))
         ))))

(defun compile-program (x)
  (flet ((emit-header ()
           (emit "	.text")
           (emit "	.p2align 4,,15")
           (emit ".globl scheme_entry")
           (emit "	.type	scheme_entry, @function")
           (emit "scheme_entry:")))
    (emit-header)
    (let ((ir (expr->ir x)))
      (format *terminal-io* ";;;; Carve IR:~%~a~%" ir)
      (format *terminal-io* ";;;; End Carve IR~%")
      (emit-asm ir)
      (emit "ret")
      )))

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

(defun run* (x)
  (run x nil))

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

    (equal "#t" (run '(%boolean? |#t|) nil))
    (equal "#t" (run '(%boolean? |#f|) nil))
    (equal "#f" (run '(%boolean? 4) nil))
    (equal "#f" (run '(%boolean? -1) nil))
    (equal "#f" (run '(%boolean? nil) nil))
    (equal "#f" (run '(%boolean? #\a) nil))

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

(deftest test-if ()
  (check
    (equal "#t" (run '(if |#t| |#t| |#f|) nil))
    (equal "#f" (run '(if |#f| |#t| |#f|) nil))
    (equal "3" (run '(if |#t| 3 4) nil))
    (equal "4" (run '(if |#f| 3 4) nil))
    (equal "6" (run '(if |#t| (%add1 5) 4) nil))
    (equal "9" (run '(if |#f| (%add1 5) (%add1 8)) nil))
    ))
