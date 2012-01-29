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

(defun comp-error (expr reason &rest args)
  "Raise scheme-compile-error."
  (error (make-condition 'scheme-compile-error
                         :expr expr
                         :reason (apply #'format nil reason args))))

(defun emit (str &rest args)
  "Emit assembler to *asm-output*."
  (apply 'format *asm-output* str args)
  (terpri *asm-output*))

(defun immediate-rep (x)
  "Return immediate representation of X."
  (const
   (cond
     ((integerp x) (ash x *fixnum-shift*))
     ((null x) *empty-list*)
     ((characterp x)
      (logior (ash (char-code x) 8) #b00001111))
     ((eql x '#t)
      *scheme-t*)
     ((eql x '#f)
      *scheme-f*)
     (t (error "unknown immediate: ~a" x)))))

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
  "Return non-nil if X is immediate integer."
  (and (integerp x)
       (<= most-negative-immediate-integer x)
       (<= x most-positive-immediate-integer)))

(defun immediate-p (x)
  "Return non-nil if X is immediate object."
  (or (immediate-integer-p x) (null x)
      (characterp x)
      (eql x '#t)
      (eql x '#f)))

(defun collect-register (ir)
  "Return list of register name in the IR."
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
  "Analyze liveness for IR and return list of liveness."
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
  "Return non-nil if liveness1 and liveness2 are inteferenced."
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
  "Replace virtual register into physical register in IR."
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

(defun allocate-register (ir phys-regs)
  "Allocate physical resister for IR by linear scan register allocation."
  (let* ((liveness (sort (analyze-liveness ir) #'< :key #'liveness-start))
         (si (- *word-size*))  ;; fixme まっとうな手段で si を得ること
         (r (length phys-regs))
         (register (make-hash-table :test #'equal))
         (location (make-hash-table :test #'equal)) 
         (pool (copy-seq phys-regs))
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

(defun emit-mov (src dst &key (size "q"))
  (emit "mov~a ~a, ~a" size src dst))

(defun emit-add (src dst &key (size "q"))
  ;; add src, dst # dst = dst + src
  (emit "add~a ~a, ~a" size src dst))

(defun emit-sub (src dst &key (size "q"))
  ;; sub src, dst # dst = dst - src
  (emit "sub~a ~a, ~a" size src dst))

(defun emit-mul (src dst &key (size "q"))
  ;; imulq src, dst # dst = dst * src
  (emit "imul~a ~a, ~a" size src dst))

(defun asm-reg (r &key disp)
  "Generate asm for register R."
  (if disp
      (format nil "~a(%~a)" disp r)
      (format nil "%~a" r)))

(defun asm-const (v)
  "Generate asm immediate value."
  (format nil "$~a" v))

(defun asm-addressing (x)
  (match x
    ((:REG r)
     (asm-reg r))
    (((:REG r) disp)
     (asm-reg r :disp disp))
    ((:CONST v)
     (asm-const v))
    (t
     (error "invalid addressing: ~a" x))))

(defun asm-const-p (x)
  "Is the asm a CONST?"
  (match x
    ((:CONST v)
     (declare (ignore v))
     t)
    (t nil)))

(defun emit-set (dest src)
  (assert (not (asm-const-p dest)) (dest) "dest must be a register!")
  (let ((asm-dest (asm-addressing dest))
        (asm-src (asm-addressing src)))
    (emit-mov asm-src asm-dest)))

(defun emit-asm (ir)
  "Emit assembler of IR."
  (assert (or (null ir) (consp ir)) (ir) "emit-ir: except cons, but got: ~a" ir)
  (if (null ir)
      nil
      (progn
        (match (car ir)
          ((:SET ((:REG r0) disp0) ((:REG r1) disp1)) ;; 存在しない命令
           (declare (ignore r0 disp0 r1 disp1))
           (comp-error (car ir) "Invalid compilation.src and dest are memory"))
          ((:SET dest src)
           (emit-set dest src))
          ((:ADD ((:REG r1) disp1) ((:REG r0) disp0)) ;; 存在しない命令
           (declare (ignore r1 disp1 r0 disp0))
           (comp-error (car ir) "Invalid compilation.src and dest are memory"))
          ((:ADD a b)
           (emit-add (asm-addressing a) (asm-addressing b)))
          ((:SUB a b) ; a - b
           (emit-sub (asm-addressing a) (asm-addressing b)))
          ((:MUL a b) ; a * b
           (emit-mul (asm-addressing a) (asm-addressing b)))

          ((:SHL (:CONST v) (:REG r))
           (emit "shlq $~a, %~a" v r))
          ;; todo other SHL
          ((:SHR (:CONST v) (:REG r))
           (emit "shrq $~a, %~a" v r))
          ;; todo other SHR
          ((:OR (:CONST v) (:REG r))
           (emit "orq $~a, %~a" v r))
          ;; todo other OR
          ((:AND (:CONST v) (:REG r))
           (emit "andq $~a, %~a" v r))
          ;; todo other AND
          ((:CMP (:CONST v) (:REG r))
           (emit "cmpq $~a, %~a" v r))
          ;; todo other cmp
          ((:SAL (:CONST v) (:REG r))
           (emit "salq $~a, %~a" v r))
          ;; todo other sal
          ((:SETE (:REG r))
           (emit "sete %~a" r))

          ((:JE label)
           (emit "je ~a" label))
          ((:JMP label)
           (emit "jmp ~a" label))
          ((:DEFLABEL label)
           (emit "~a:" label))
          (t
           (comp-error (car ir) "emit-asm error unmatch expression: ~a" ir)))
        (emit-asm (cdr ir)))))

(defun gen-label ()
  "Generate an asm label."
  (gensym "Label"))

(defun gen-vreg ()
  "Return new symbol for virtual register."
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
;; seq, gen is from PAIP Chapter 23.
(defun seq (&rest code)
  "Return a sequence of instruction."
  (apply #'append code))

(defun gen (opcode &rest args)
  "Generate a single instruction."
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
  "Return instruction refer the register R."
  (if disp
      `((:REG "rsp") ,disp)
      `(:REG ,r)))

(defun const (v)
  "Return instruction for constant value V."
  `(:CONST ,v))

(defun comp-unary (expr si acc code)
  "Compile unary-primitive EXPR."
  (seq (comp expr si acc) code))

(defmacro def-unary-prim (name (expr si acc) &body body)
  "Define unary primitive compiler."
  (let ((code (gensym)))
    `(defun ,name (,expr ,si ,acc)
       (let ((,code (seq ,@body)))
         (comp-unary ,expr ,si ,acc ,code)))))

(def-unary-prim comp-fixnum->char (expr si acc)
  (gen :SHL (const (- *char-shift* *fixnum-shift*)) (reg acc))
  (gen-or (const *char-tag*) (reg acc)))

(def-unary-prim comp-char->fixnum (expr si acc)
  (gen :SHR (const (- *char-shift* *fixnum-shift*)) (reg acc)))

(def-unary-prim comp-zero? (expr si acc)
  (gen :CMP (const 0) (reg acc))
  (gen-set (reg acc) (const 0))
  (gen :SETE (reg "al"))
  (gen :SAL (const 4) (reg acc))
  (gen-or (const *scheme-f*) (reg acc)))

(def-unary-prim comp-null? (expr si acc)
  (gen :CMP (const *empty-list*) (reg acc))
  (gen-set (reg acc) (const 0))
  (gen :SETE (reg "al")) ;; fixme
  (gen :SAL (const 4) (reg acc))
  (gen-or (const *scheme-f*) (reg acc)))

(def-unary-prim comp-boolean? (expr si acc)
  (gen-and (const *scheme-f*) (reg acc))
  (gen :CMP (const *scheme-f*) (reg acc))
  (gen-set (reg acc) (const 0))
  (gen :SETE (reg "al"))
  (gen :SAL (const 4) (reg acc))
  (gen-or (const *scheme-f*) (reg acc)))

(def-unary-prim comp-fixnum? (expr si acc)
  (gen-and (const 3) (reg acc))
  (gen :CMP (const 0) (reg acc))
  (gen-set (reg acc) (const 0))
  (gen :SETE (reg "al"))
  (gen :SAL (const 4) (reg acc))
  (gen-or (const *scheme-f*) (reg acc)))

(defun comp-if (pred then else si acc)
  (with-labels (alt-label end-label)
    (seq (comp pred si acc)
         (gen :CMP (const *scheme-f*) (reg acc))
         (gen :JE alt-label)
         (comp then si acc)
         (gen :JMP end-label)
         (gen-deflabel alt-label)
         (comp else si acc)
         (gen-deflabel end-label))))

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

(defun comp-mul (expr1 expr2 si acc)
  (with-vregs (r1 r2)
    (seq
     ;; 4xy = 4x * (4y / 4)
     (comp expr2 si r2)
     (gen :SHR (const *fixnum-shift*) (reg r2))
     (comp expr1 si r1)
     (gen :MUL (reg r2) (reg r1))
     (gen-set (reg acc) (reg r1)))))

(defun comp (x si &optional (acc (gen-vreg)))
  "Compile expression X and return Carve IR."
  (cond
    ((immediate-p x)
     (gen-set (reg acc) (immediate-rep x)))
    (t
     (match x
       (('%add1 expr) (comp-unary expr si acc (gen :ADD (gen-1) (reg acc))))
       (('%sub1 expr) (comp-unary expr si acc (gen :SUB (gen-1) (reg acc))))
       (('%fixnum->char expr) (comp-fixnum->char expr si acc))
       (('%char->fixnum expr) (comp-char->fixnum expr si acc))
       (('%zero? expr) (comp-zero? expr si acc))
       (('%null? expr) (comp-null? expr si acc))
       (('%boolean? expr) (comp-boolean? expr si acc))
       (('%fixnum? expr) (comp-fixnum? expr si acc))
       (('if pred then else) (comp-if pred then else si acc))
       (('%+ expr1 expr2) (comp-add/sub '%+ expr1 expr2 si acc))
       (('%- expr1 expr2) (comp-add/sub '%- expr1 expr2 si acc))
       (('%* expr1 expr2) (comp-mul expr1 expr2 si acc))

       (('plus expr1 expr2) ;; fixme or remove
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
    (let* ((init-regs (list "rbx" "rcx" "rdx" "rdi" "rsi"
                            "r8" "r9" "r10" "r11" "r12" "r13" "r14" "r15"))
           (si (- *word-size*))
           (ir0 (comp x si "rax"))
           (ir1 (allocate-register ir0 init-regs))
           ;;(ir1 (allocate-register ir0 (list "rbx" "rcx")))
           )
      (print-info ir0 "IR0")
      (print-info ir1 "IR1")
      (emit-asm ir1)

      (emit "ret"))))

(defun write-asm (x)
  "Compile s-expression X and write to *asm-file*"
  (with-open-file (*asm-output* *asm-file* :direction :output :if-exists :supersede)
    (compile-program x)))

(defun make-scheme-library ()
  (let ((program "/usr/bin/gcc")
        (args `("-g" "-shared" ,*asm-file* "-o" ,*scheme-entry-lib-file*)))
    (sb-ext:run-program program args
                        :error *scheme-entry-error-file*
                        :if-error-exists :supersede
                        :output *scheme-entry-output-file*
                        :if-output-exists :supersede)))

(defun make-scheme-exe ()
  (let* ((args `("-g" ,*asm-file* ,*scheme-driver-c-file* "-o" ,*scheme-driver-exe*))
         (proc (sb-ext:run-program "/usr/bin/gcc" args :error *terminal-io*)))
    (unless (= 0 (sb-ext:process-exit-code proc))
      (error "make-scheme-exe exit"))))

(defun load-scheme-entry ()
  (load-foreign-library *scheme-entry-lib-file*)
  (defcfun "scheme_entry" :int64))

(defun format-scheme-value (val)
  "Printer. *not used*"
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