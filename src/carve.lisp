;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; carve.lisp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package :carve)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (set-scm-macro-character))

(defvar *asm-output* t
  "write assembler to this stream.")

(defvar *word-size* 8)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; x86_64
;; 64-bit registers
;; rax ; the accumulator
;; rbx, rcx, rdx, rdi, rsi, r8, r9, r10, r11, r12, r13, r14, r15
;; rbp ; the frame pointer
;; rsp ; the stack pointer
;; 8-bit registers
;; al ;; TODO 命令との関係を整理すること

(defvar *x86-64-specific-register*
  (list "rax" "rbp" "rsp" "al"))

(defvar *x86-64-generic-register*
  (list "rbx" "rcx" "rdx" "rdi" "rsi" "r8" "r9" "r10" "r11" "r12" "r13" "r14" "r15"))

(defvar *x86-64-registers*
  (list "rbx" "rcx" "rdx" "rdi" "rsi" "r8" "r9" "r10" "r11" "r12" "r13" "r14" "r15"
        "rax" "rbp" "rsp" "al"))

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
(defvar *scheme-entry-error-file* "/home/cranebird/carvescheme/src/scm.err")
(defvar *scheme-entry-output-file* "/home/cranebird/carvescheme/src/scm.out")
(defvar *scheme-driver-c-file* "/home/cranebird/carvescheme/src/driver.c")
(defvar *scheme-driver-exe* "/home/cranebird/carvescheme/src/main")
(defvar *scheme-driver-error-file* "/home/cranebird/carvescheme/src/main.err")

(defvar *liveness-file* "/home/cranebird/carvescheme/src/liveness.ps")

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

(defun immediate-rep (x)
  (cond
    ((integerp x) (ash x *fixnum-shift*))
    ((null x) *empty-list*)
    ((characterp x)
     (logior (ash (char-code x) 8) #b00001111))
    ((eql x '#t)
     *scheme-t*)
    ((eql x '#f)
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
  "return non-nil if X is immediate integer."
  (and (integerp x)
       (<= most-negative-immediate-integer x)
       (<= x most-positive-immediate-integer)))

(defun immediate-p (x)
  "return non-nil if X is immediate object."
  (or (immediate-integer-p x) (null x)
      (characterp x)
      (eql x '#t)
      (eql x '#f)))

(defun collect-register (ir)
  "return list of register name in the IR."
  (match ir
    ((:REG r) (list r))
    (t
     (if (consp ir)
         (remove-duplicates 
          (append (collect-register (car ir))
                  (collect-register (cdr ir))))
         nil))))

(defstruct liveness name start end)

(defun analyze-liveness (ir)
  "analyze liveness for IR. return list of (register start end)."
  (loop with exists = (make-hash-table)
     for insn in ir for i from 0
     for regs = (collect-register insn)
     do (loop for r in regs
           if (register-symbol-p r)
           do (push i (gethash r exists))
           else
           do (warn "in regs, but not register-symbol-p: ~a" r))
     finally
       (return 
         (loop for k being the hash-keys in exists
            collect
              (make-liveness :name k
                             :start (apply #'min (gethash k exists))
                             :end (apply #'max (gethash k exists)))))))

(defun interference-p (liveness1 liveness2)
  "return non-nil if liveness1 and liveness2 are inteferenced."
  (let ((s1 (liveness-start liveness1))
        (e1 (liveness-end liveness1))
        (s2 (liveness-start liveness2))
        (e2 (liveness-end liveness2)))
    (assert (and (>= e1 s1) (>= e2 s2)))
    (or
     (and (< s2 s1) (> e2 s1))
     (and (>= s2 s1) (< s2 e1)))))

(defun print-rig (ir stream)
  (format stream "graph ig {~%")
  (format stream "graph[charset=\"UTF-8\"];~%")
  (format stream "node[shape=circle];~%")
  (let ((regs (collect-register ir))
        (liveness (analyze-liveness ir))
        (done nil))
    (loop for r0 in regs
       for r0range = (find r0 liveness :key #'liveness-name)
       do
         (loop for r1 in regs
            for r1range = (find r1 liveness :key #'liveness-name)
            if (and (not (eql r0 r1))
                    (interference-p r0range r1range)
                    (not (member r1 done)))
            do
              (format t "~a -- ~a;~%" r0 r1))
         (pushnew r0 done)))
  (format stream "}~%"))

(defun dump-hash (ht)
  (loop for k being the hash-keys in ht
     do (format t "~a => ~a~%" k (gethash k ht))))

(defun replace-all-virtual-register (insn register location)
  (match insn
    ((:REG r)
     (cond
       ((gethash r location)
        (reg "rsp" :disp (gethash r location)))
       ((gethash r register)
        (reg (gethash r register)))
       (t
        (reg r))))
    (t
     (if (consp insn)
         (cons (replace-all-virtual-register (car insn) register location)
               (replace-all-virtual-register (cdr insn) register location))
         insn))))

(defun allocate-register (ir &optional (init-regs (list "rbx" "rcx" "rdx" "rdi" "rsi"
                                                        "r8" "r9" "r10" "r11" "r12" "r13" "r14" "r15")))
  (let* ((liveness (sort (analyze-liveness ir) #'< :key #'liveness-start))
         (si (- *word-size*))  ;; fixme まっとうな手段で si を得ること
         (r (length init-regs))
         (register (make-hash-table :test #'equal))
         (location (make-hash-table :test #'equal)) 
         (pool (copy-seq init-regs))
         (active nil))
    (labels ((startpoint (i) (liveness-start i))
             (endpoint (i) (liveness-end i))
             (expire-old-intervals (i)
               (warn "expire-old-intervals: active=~a" (mapcar #'liveness-name active))
               (loop for j in (sort (copy-seq active) #'< :key #'endpoint)
                  do
                    (when (>= (endpoint j) (startpoint i))
                      (warn "endpoint ~a >= startpoint ~a, dont expire."
                            (endpoint i) (startpoint j))
                      (return-from expire-old-intervals))
                    (warn "remove ~a from active" (liveness-name j))
                    (setf active (remove j active :test #'equal))
                    (push (gethash (liveness-name j) register) pool)))
             (spill-at-interval (i)
               (warn "spill-at-interval ~a:" (liveness-name i))
               (let ((spill (car (last active))))
                 (warn "try to spill=~a..." spill)
                 (cond
                   ((> (endpoint spill) (endpoint i))
                    (warn "endpoint spill ~a > endpoint i ~a." (endpoint spill) (endpoint i))
                    (setf (gethash (liveness-name i) register)
                          (gethash (liveness-name spill) register))
                    (setf (gethash (liveness-name spill) location) si)
                    (decf si *word-size*)
                    (warn "befere spill: active = ~a" active)
                    (setf active (remove spill active :test #'equal))
                    (push i active)
                    (setf active (sort (copy-seq active) #'< :key #'endpoint))
                    (warn "after spill: active=~a" active))
                   (t
                    (warn "spill-at-interval else")
                    (setf (gethash (liveness-name i) location) si)
                    (decf si *word-size*))))))
      (loop for i in liveness ;; list of liveness
         unless (member (liveness-name i) *x86-64-registers* :test #'equal)
         do
           (warn ";;; process liveness ~a..." (liveness-name i))
           (expire-old-intervals i)
           (cond
             ((= (length active) r)
              (warn "active = ~a, then spill ~a" (length active) (liveness-name i))
              (spill-at-interval i))
             (t
              (warn "get register from pool ~a" pool)
              (setf (gethash (liveness-name i) register) (pop pool))
              (push i active)
              (setf active (sort active #'< :key #'liveness-end))))
         finally
           (return (replace-all-virtual-register ir
                                                 register 
                                                 location))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; x86_64 and Carve IR
;; movq source, dest
;; addq
;; subq
;; shlq
;; orq
;; andq
;; sete
;; salq
;; jump
;; je

(defun emit-mov (src dest &key (size "q"))
  (emit "mov~a ~a, ~a" size src dest))

(defun asm-reg (r &key disp)
  (if disp
      (format nil "~a(%~a)" disp r)
      (format nil "%~a" r)))

(defun asm-const (v)
  (format nil "$~a" v))

;; now
(defun emit-addressing (x)
  (match dest
    ((:REG r)
     (asm-reg r))
    (((:REG r) disp)
     (asm-reg r :disp disp))
    (t
     (error "invalid dest"))))

(defun emit-set (dest src)
  (let ((asm-dest (match dest
                    ((:REG r)
                     (asm-reg r))
                    (((:REG r) disp)
                     (asm-reg r :disp disp))
                    (t
                     (error "invalid dest"))))
        (asm-src (match src
                   ((:REG r)
                    (asm-reg r))
                   (((:REG r) disp)
                    (asm-reg r :disp disp))
                   (t
                    (asm-const src)))))
    (emit-mov asm-src asm-dest)))

(defun emit-asm (ir)
  (assert (or (null ir) (consp ir)) (ir) "emit-ir: except cons, but got: ~a" ir)
  (if (null ir)
      nil
      (progn
        (match (car ir)
          ((:SET ((:REG r0) disp0) ((:REG r1) disp1)) ;; 存在しない命令
           (declare (ignore r0 disp0 r1 disp1))
           (error (make-condition 'scheme-compile-error
                                  :expr (car ir)
                                  :reason "Invalid compilation.src and dest are memory")))
          ((:SET dest src)
           (emit-set dest src))

          ((:ADD (:REG r1) (:REG r0))
           (emit "addq %~a, %~a" r1 r0))
          ((:ADD ((:REG r1) disp) (:REG r0))
           (emit "addq ~a(%~a), %~a" disp r1 r0))

          ((:ADD (:REG r1) ((:REG r0) disp))
           (emit "addq %~a, ~a(%~a)" r1 disp r0))

          ((:ADD ((:REG r1) disp1) ((:REG r0) disp0)) ;; 存在しない命令
           (declare (ignore r1 disp1 r0 disp0))
           (error (make-condition 'scheme-compile-error
                                  :expr (car ir)
                                  :reason "Invalid compilation.src and dest are memory")))

          ((:ADD v (:REG r))
           (emit "addq $~a, %~a" v r))

          ((:SUB (:REG r1) (:REG r0))
           (emit "subq %~a, %~a" r1 r0))
          ((:SUB v (:REG r))
           (emit "subq $~a, %~a" v r))

          ((:SHL v (:REG r))
           (emit "shlq $~a, %~a" v r))
          ((:SHR v (:REG r))
           (emit "shrq $~a, %~a" v r))
          ((:OR v (:REG r))
           (emit "orq $~a, %~a" v r))
          ((:AND v (:REG r))
           (emit "andq $~a, %~a" v r))
          ((:CMP v (:REG r))
           (emit "cmpq $~a, %~a" v r))
          ((:SETE (:REG r))
           (emit "sete %~a" r))
          ((:SAL v (:REG r))
           (emit "salq $~a, %~a" v r))
          ((:JE label)
           (emit "je ~a" label))
          ((:JMP label)
           (emit "jmp ~a" label))
          ((:DEFLABEL label)
           (emit "~a:" label))

          (t
           (error "emit-asm error unmatch expression: ~a~%~a" (car ir) ir)))
        (emit-asm (cdr ir)))))

(defun gen-label ()
  (gensym "Label"))

(defun gen-vreg ()
  "create symbol for virtual register."
  (gensym "reg"))

(defmacro with-vregs ((&rest regs) &body body)
  `(let ,(loop for r in regs collect `(,r (gen-vreg)))
     ,@body))

(defmacro with-labels ((&rest labels) &body body)
  `(let ,(loop for l in labels collect `(,l (gen-label)))
     ,@body))

(defun specific-symbol-p (x thing)
  (and (symbolp x)
       (let ((name (symbol-name x))
             (len (length thing)))
         (and
          (not (find-symbol name))
          (> (length name) len)
          (equal (subseq name 0 len) thing)))))

(defun register-symbol-p (x)
  (or (specific-symbol-p x "reg") 
      (member x *x86-64-registers* :test #'equal)))

(defun label-symbol-p (x)
  (specific-symbol-p x "Label"))


;; IR

(defun seq (&rest code)
  "return a sequence of instruction."
  (apply #'append code))

(defun gen (opcode &rest args)
  (list (cons opcode args)))

(defun gen-1 ()
  (immediate-rep 1))

(defun gen-set (place value)
  (gen :SET place value))

(defun gen-deflabel (label)
  (gen :DEFLABEL label))

(defun gen-and (a b)
  (gen :AND a b))

(defun gen-or (a b)
  (gen :OR a b))

(defun reg (r &key disp)
  "return part of instruction refer the register R."
  (if disp
      `((:REG "rsp") ,disp)
      `(:REG ,r)))

(defun comp-unary (expr si acc code)
  "generate unary primitive call."
  (seq (comp expr si acc) code))

(defun comp-add/sub (op expr1 expr2 si acc)
  (let ((insn (ecase op
                ((%+) :ADD)
                ((%-) :SUB))))
    (with-vregs (r1 r2)
      (seq
       (comp expr2 si r2)
       (comp expr1 si r1)
       (gen insn (reg r2) (reg r1))
       (gen-set (reg acc) (reg r1))))))

(defun comp (x si &optional (acc (gen-vreg)))
  "compile expression X into Carve IR."
  (cond
    ((immediate-p x)
     (gen-set (reg acc) (immediate-rep x)))
    (t
     (match x
       (('%add1 expr)
        (comp-unary expr si acc (gen :ADD (gen-1) (reg acc))))
       (('%sub1 expr)
        (comp-unary expr si acc (gen :SUB (gen-1) (reg acc))))
       (('%fixnum->char expr)
        (comp-unary expr si acc
                    (seq
                     (gen :SHL (- *char-shift* *fixnum-shift*) (reg acc))
                     (gen-or *char-tag* (reg acc)))))
       (('%char->fixnum expr)
        (comp-unary expr si acc
                    (gen :SHR (- *char-shift* *fixnum-shift*) (reg acc))))
       (('%zero? expr)
        (comp-unary expr si acc
                    (seq
                     (gen :CMP 0 (reg acc))
                     (gen-set (reg acc) 0)
                     (gen :SETE (reg "al"))
                     (gen :SAL 4 (reg acc))
                     (gen-or *scheme-f* (reg acc)))))
       (('%null? expr)
        (comp-unary expr si acc
                    (seq
                     (gen :CMP *empty-list* (reg acc))
                     (gen-set (reg acc) 0)
                     (gen :SETE (reg "al")) ;; fixme
                     (gen :SAL 4 (reg acc))
                     (gen-or *scheme-f* (reg acc)))))
       (('%boolean? expr)
        (comp-unary expr si acc
                    (seq 
                     (gen-and *scheme-f* (reg acc))
                     (gen :CMP *scheme-f* (reg acc))
                     (gen-set (reg acc) 0)
                     (gen :SETE (reg "al"))
                     (gen :SAL 4 (reg acc))
                     (gen-or *scheme-f* (reg acc)))))
       (('%fixnum? expr)
        (comp-unary expr si acc
                    (seq
                     (gen-and 3 (reg acc))
                     (gen :CMP 0 (reg acc))
                     (gen-set (reg acc) 0)
                     (gen :SETE (reg "al"))
                     (gen :SAL 4 (reg acc))
                     (gen-or *scheme-f* (reg acc)))))
       (('if test conseq altern)
        (with-labels (alt-label end-label)
          (seq
           (comp test si acc)
           (gen :CMP *scheme-f* (reg acc))
           (gen :JE alt-label)
           (comp conseq si acc)
           (gen :JMP end-label)
           (gen-deflabel alt-label)
           (comp altern si acc)
           (gen-deflabel end-label))))
       (('%+ expr1 expr2)
        (comp-add/sub '%+ expr1 expr2 si acc))
       (('%- expr1 expr2)
        (comp-add/sub '%- expr1 expr2 si acc))
       (('plus expr1 expr2) ;; 
        `(,@(comp expr2 si acc)
            ;; base register, displ  => -si(%rsp)
            (gen-set (reg "rsp" :disp si) (reg acc))
            ,@(comp expr1 (- si *word-size*) acc)
            (:ADD ((:REG "rsp" ) ,si) (reg acc))))

       (t
        (error (make-condition 'scheme-compile-error
                               :expr x :reason "unknown expr")))))))

(defun compile-program (x)
  (flet ((emit-header ()
           (emit "	.text")
           (emit "	.p2align 4,,15")
           (emit ".globl scheme_entry")
           (emit "	.type	scheme_entry, @function")
           (emit "scheme_entry:"))
         (print-info (ir stage)
           (format *terminal-io* ";;; Carve IR ~a~%" stage)
           (dump-ir ir *terminal-io*)))
    (emit-header)
    (let* ((si (- *word-size*))
           (ir0 (comp x si "rax"))
           (ir1 (allocate-register ir0))
           ;;(ir1 (allocate-register ir0 (list "rbx" "rcx")))
           )
      (print-info ir0 "IR0")
      (print-info ir1 "IR1")
      (emit-asm ir1)

      (emit "ret")
      )))

(defun write-asm (x)
  (with-open-file (*asm-output* *asm-file* :direction :output :if-exists :supersede)
    (compile-program x)))

(defun make-scheme-library ()
  (sb-ext:run-program "/usr/bin/gcc"
                      `("-g" "-shared" ,*asm-file* "-o" ,*scheme-entry-lib-file*) 
                      :error *scheme-entry-error-file* :if-error-exists :supersede
                      :output *scheme-entry-output-file*  :if-output-exists :supersede))

(defun make-scheme-exe ()
  (let ((proc
         (sb-ext:run-program "/usr/bin/gcc"
                             `("-g" ,*asm-file* ,*scheme-driver-c-file* "-o" ,*scheme-driver-exe*)
                             :error *terminal-io*)))
    (unless (= 0 (sb-ext:process-exit-code proc))
      (error "make-scheme-exe exit"))))

(defun load-scheme-entry ()
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

(defun run (x &optional (out t)) ;; Use C driver version.
  (write-asm x)
  ;; (make-scheme-library)
  (handler-bind ((error
                  #'(lambda (cond)
                      (declare (ignore cond))
                      (warn "Error. check *terminal-io*"))))
    (make-scheme-exe)
    ;; (load-scheme-entry)
    (let ((str
           (with-output-to-string (o)
             (sb-ext:run-program *scheme-driver-exe* nil :output o))))
      (format out "~a" str))))

;;; cffi version.
;; (defun run (x &optional (out t))
;;   (write-asm x)
;;   (make-scheme-library)
;;   (make-scheme-exe)
;;   (load-scheme-entry)
;;   (let ((val (scheme-entry)))
;;     (format out "~a" (format-scheme-value val))))

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
    (equal "#t" (run '#t nil))
    (equal "#f" (run '#f nil))
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

    (equal "#t" (run '(%boolean? #t) nil))
    (equal "#t" (run '(%boolean? #f) nil))
    (equal "#f" (run '(%boolean? 4) nil))
    (equal "#f" (run '(%boolean? -1) nil))
    (equal "#f" (run '(%boolean? nil) nil))
    (equal "#f" (run '(%boolean? #\a) nil))

    (equal "#t" (run '(%fixnum? 0) nil))
    (equal "#t" (run '(%fixnum? 4) nil))
    (equal "#t" (run '(%fixnum? -2) nil))
    (equal "#t" (run '(%fixnum? (%add1 -1)) nil))
    (equal "#f" (run '(%fixnum? #t) nil))
    (equal "#f" (run '(%fixnum? #f) nil))
    (equal "#f" (run '(%fixnum? (%zero? 3)) nil))
    (equal "#f" (run '(%fixnum? (%zero? 0)) nil))
    ))

(deftest test-unary-primitive-edge ()
  (check
    (equal (format nil "~a" most-positive-immediate-integer)
           (run `(%add1 ,(1- most-positive-immediate-integer)) nil))
    (equal (format nil "~a" most-negative-immediate-integer)
           (run `(%sub1 ,(1+ most-negative-immediate-integer)) nil))))

(deftest test-if ()
  (check
    (equal "#t" (run '(if #t #t #f) nil))
    (equal "#f" (run '(if #f #t #f) nil))
    (equal "3" (run '(if #t 3 4) nil))
    (equal "4" (run '(if #f 3 4) nil))
    (equal "6" (run '(if #t (%add1 5) 4) nil))
    (equal "9" (run '(if #f (%add1 5) (%add1 8)) nil))
    ))

(deftest test-+ ()
  (check
    (equal "3" (run '(%+ 1 2) nil))
    (equal "4" (run '(%+ -1 5) nil))
    (equal "10" (run '(%+ 10 0) nil))
    (equal "7" (run '(%+ (%+ 1 2) 4)  nil))
    (equal "7" (run '(%+ (%+ 1 2) (%+ 3 1))  nil))
    (equal "7" (run '(%+ (%add1 2) 4)  nil))
    (equal "8" (run '(%+ (%add1 2) (%add1 4))  nil))

    ))

(deftest test-high-register-pressure ()
  (check
    (equal "105"
           (run '(%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ 1 2) 3) 4) 5) 6) 7) 8) 9) 10) 11) 12) 13) 14)  nil))
    (equal "120"
           (run '(%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ 1 2) 3) 4) 5) 6) 7) 8) 9) 10) 11) 12) 13) 14) 15) nil))
    
    (equal "191"
           (run '(%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ 1 2) 3) 4) 5) 6) 7) 8) 9) 10) 11) 12) 13) 14)
                  (%+ (%+ 20 21) (%+ 22 23))) nil))

    (equal "245"
           (run '(%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ 1 2) 3) 4) 5) 6) (%+ 30 31)) 8) 9) 10) 11) 12) 13) 14)
                  (%+ (%+ 20 21) (%+ 22 23))) nil))
    ))
    
(deftest test-- ()
  (check
    (equal "3" (run '(%- 4 1) nil))
    (equal "-1" (run '(%- 1 2) nil))
    (equal "-6" (run '(%- -1 5) nil))
    (equal "10" (run '(%- 10 0) nil))
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utility
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun dump-ir (ir &optional (stream t))
  (let ((regs (collect-register ir)))
    (format stream ";; insn: ~a reg: ~a~%" (length ir) (length regs))
    (loop for insn in ir for i from 0
       do (format stream ";;[~a] ~a~%" i insn))
    (values)))

(defun write-liveness-graph (ir)
  (with-open-file (out *liveness-file* :direction :output
                       :if-exists :supersede)
    (dump-ir ir)
    (write-liveness-graph-data ir out)))

(defun write-liveness-graph-data (ir out)
  (let ((regs (collect-register ir))
        (liveness (analyze-liveness ir)))
    (let ((num-reg (length regs))
          (num-code (1+ (apply #'max (mapcar #'liveness-end liveness)))))
      (format out "%!PS-Adobe-3.0 EPSF-3.0
gsave

/vertexradius 3 def

/vertex {
    2 dict begin
    /y exch def
    /x exch def    
    x y vertexradius 0 360 arc fill
    end
} def

/hdashline {
    3 dict begin
    /w exch def % width
    /y exch def % start y
    /x exch def % start x
    x y moveto
    w 0 rlineto
    1 setlinewidth
    [ 4 ] 0 setdash
    end
} def

/hdashlines {
    5 dict begin
    /n exch def % number of lines
    /w exch def % width
    /ysep exch def % y sep
    /y0 exch def % start point y
    /x0 exch def % start point x
    0 1 n {
        2 dict begin
        /i exch def
        /str 3 string def
        newpath
        x0 y0 ysep i mul sub w hdashline
        stroke

        newpath
        x0 18 sub y0 ysep i mul sub moveto
        i str cvs show
        stroke
        
        end
    } for
    end
} def

/vx-line { % vertex 付きの線を引く
    4 dict begin
    /y1 exch def    
    /x1 exch def
    /y0 exch def    
    /x0 exch def

    % 線
    newpath
    1 setlinewidth
    [] 0 setdash % 実線に戻す

    x0 y0 moveto
    x1 y1 lineto
    stroke

    % 端点
    newpath
    x0 y0 vertex
    x1 y1 vertex
    stroke

    end
} def

/regline { % レジスタの生存線を引く
    10 dict begin
    /rdead exch def % 死ぬ
    /rdefine exch def % 生まれ
    /rn exch def % n 番目のレジスタ
    /rx0 x0gap rn xgap mul add def
    /rydefine y0 ygap rdefine mul sub def
    /rydead y0 rdead ygap mul sub def
    rx0 rydefine rx0 rydead vx-line

    newpath
    rx0 2 sub y0 10 add moveto
    rn 3 string cvs show
    stroke
    end
} def

0 0 0 setrgbcolor
/Helvetica findfont 12 scalefont setfont

%
/num-reg ~a def
/num-code ~a def
/ygap 10 def
/x0gap 100 def
/xgap 15 def
/y0 755 def

/figwidth xgap num-reg 2 mul mul def
x0gap y0 ygap figwidth num-code hdashlines~%"
              num-reg num-code)
      (loop for i from 1 for l in (sort (copy-seq liveness) #'< :key #'liveness-start)
         do
           (format out "~a ~a ~a regline~%" i (liveness-start l) (liveness-end l)))
      (format out
              "showpage
grestore"))))