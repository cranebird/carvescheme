;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; carve.lisp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package :carve)

(defvar *asm-output* t
  "write assembler to this stream.")

(defvar *word-size* 8)

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

;; (defun collect-register (ir)
;;   (loop for insn in ir with regs
;;      do
;;        (match insn
;;          ((op ('REG r1) ('REG r2))
;;           (declare (ignore op))
;;           (pushnew r2 regs)
;;           (pushnew r1 regs))

;;          ((op ('REG r) res)
;;           (declare (ignore op res))
;;           (pushnew r regs))
                                       
;;          ((op res ('REG r))
;;           (declare (ignore op res))
;;           (pushnew r regs))

;;          (t
;;           nil))
;;      finally
;;        (return (reverse regs))))

(defun collect-register (ir)
  (match ir
    (('REG r)
     (list r))
    (t
     (if (consp ir)
         (remove-duplicates 
          (append (collect-register-iter (car ir))
                  (collect-register-iter (cdr ir))))
         nil))))

(defun flatten (x)
  (cond
    ((null x)
     nil)
    ((atom x)
     (list x))
    (t
     (append (flatten (car x)) (flatten (cdr x))))))

(defun analyze-liveness (ir)
  "analyze liveness for IR. return list of (register start end)."
  (loop for insn in ir for i from 0
     with exists = (make-hash-table)
     do
       (loop for x in (flatten insn)
          if (register-symbol-p x)
          do (push i (gethash x exists)))
     finally
       (return 
         (loop for k being the hash-keys in exists
            collect
              (list k (apply #'min (gethash k exists)) (apply #'max (gethash k exists)))))))

(defun write-register-interference-graph (ir)
  
  )

(defun interference-p (liveness1 liveness2)
  "return non-nil if liveness1 and liveness2 are inteferenced."
  (let ((s1 (nth 1 liveness1))
        (e1 (nth 2 liveness1))
        (s2 (nth 1 liveness2))
        (e2 (nth 2 liveness2)))
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
    (loop for r0 in regs for r0range = (assoc r0 liveness)
       do
         (loop for r1 in regs
            for r1range = (assoc r1 liveness)
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

(defun linear-scan-allocation (ir registers)
  (let ((liveness (sort (analyze-liveness ir) #'< :key (lambda (x) (nth 1 x))))
        (assigned (make-hash-table :test #'equal)))
    (flet ((startpoint (r)
             (nth 1 (assoc r liveness)))
           (endpoint (r)
             (nth 2 (assoc r liveness))))
      (loop for (r startpoint endpoint) in liveness with active = nil
         with free = (copy-seq registers)
         unless (member r *x86-64-registers* :test #'equal) ;; 実レジスタは再アロケートしない
         do
           (loop named active-loop for ar in (copy-seq active)
              do
                (when (>= (endpoint ar) (startpoint r))
                  (return-from active-loop nil))
                (setf active (remove ar active))
                (push (gethash ar assigned) free))
           (let ((reg (pop free)))
             (unless reg
               (warn "fail to allocate register!"))
             (setf (gethash r assigned) reg))
           (push r active)
           (setf active (sort active #'< :key #'endpoint)))
      assigned)))

(defun allocate-register (ir &optional (regs (list "rbx" "rcx" "rdx" "rdi" "rsi"
                                                   "r8" "r9" "r10" "r11" "r12" "r13" "r14" "r15")))
  (allocate-register-iter ir (linear-scan-allocation ir regs)))

(defun allocate-register-iter (ir regmap)
  (match ir
    (('REG r)
     `(REG ,(gethash r regmap r)))
    (t
     (if (consp ir)
         (cons (allocate-register-iter (car ir) regmap)
               (allocate-register-iter (cdr ir) regmap))
         ir))))

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

(defun emit-asm (ir)
  (assert (or (null ir) (consp ir)) (ir) "emit-ir: except cons, but got: ~a" ir)
  (if (null ir)
      nil
      (progn
        (match (car ir)
          (('SET ('REG r1) ('REG r0)) ;; SET dest source
           (emit "movq %~a, %~a" r0 r1)) ;; movq source dest
          (('SET ('REG r) v) ;; SET dest source
           (emit "movq $~a, %~a" v r)) ;; movq
          (('SET (('REG r0) disp) ('REG r1))
           (emit "movq %~a, ~a(%~a)" r1 disp r0))

          (('ADD ('REG r1) ('REG r0)) ;; ADD source dest
           (emit "addq %~a, %~a" r1 r0)) ;; addq source,dest
          (('ADD (('REG r1) disp) ('REG r0)) ;; ADD source dest
           (emit "addq ~a(%~a), %~a" disp r1 r0))

          (('ADD v ('REG r)) ;; ADD source dest
           (emit "addq $~a, %~a" v r))

          (('SUB ('REG r1) ('REG r0)) ;; SUB source dest
           (emit "subq %~a, %~a" r1 r0))
          (('SUB v ('REG r)) ;; SUB source dest
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
           (error "emit-asm error unmatch expression: ~a" ir)))
        (emit-asm (cdr ir)))))

(defun genlabel ()
  (gensym "Label"))

(defun genreg ()
  (gensym "reg"))

(defun specific-symbol-p (x thing)
  (and (symbolp x)
       (let ((name (symbol-name x))
             (len (length thing)))
         (and
          (not (find-symbol name))
          (> (length name) len)
          (equal (subseq name 0 len) thing)))))

(defvar *x86-64-registers*
  (list "rax" "rbx" "rcx" "rdx" "rdi" "rsi" "r8" "r9" "r10" "r11" "r12" "r13" "r14" "r15"))

(defun register-symbol-p (x)
  (or (specific-symbol-p x "reg") 
      (member x *x86-64-registers* :test #'equal)))

(defun label-symbol-p (x)
  (specific-symbol-p x "Label"))

(defun expr->ir (x si &optional (acc (genreg)))
  "compile expression X into Carve IR."
  (if (immediate-p x)
      `((SET (REG ,acc) ,(immediate-rep x)))
      (match x
        (('%add1 expr)
         (cond
           ((immediate-p expr)
            `((SET (REG ,acc) ,(immediate-rep expr))
              (ADD ,(immediate-rep 1) (REG ,acc))))
           (t
            `(,@(expr->ir expr si acc)
                (ADD ,(immediate-rep 1) (REG ,acc))))))
        (('%sub1 expr)
         (cond
           ((immediate-p expr)
            `((SET (REG ,acc) ,(immediate-rep expr))
              (SUB ,(immediate-rep 1) (REG ,acc))))
           (t
            `(,@(expr->ir expr si acc)
                (SUB ,(immediate-rep 1) (REG ,acc))))))
        (('%fixnum->char expr)
         `(,@(expr->ir expr si acc)
             (SHL ,(- *char-shift* *fixnum-shift*) (REG ,acc))
             (OR ,*char-tag* (REG ,acc))))
        (('%char->fixnum expr)
         `(,@(expr->ir expr si acc)
             (SHR ,(- *char-shift* *fixnum-shift*) (REG ,acc))))
        (('%zero? expr)
         `(,@(expr->ir expr si acc)
             (CMP 0 (REG ,acc))
             (SET (REG ,acc) 0)
             (SETE (REG "al"))
             (SAL 4 (REG ,acc))
             (OR ,*scheme-f* (REG ,acc))))
        (('%null? expr)
         `(,@(expr->ir expr si acc)
             (CMP ,*empty-list* (REG ,acc))
             (SET (REG ,acc) 0)
             (SETE (REG "al"))
             (SAL 4 (REG ,acc))
             (OR ,*scheme-f* (REG ,acc))))
        (('%boolean? expr)
         `(,@(expr->ir expr si acc)
             (AND ,*scheme-f* (REG ,acc))
             (CMP ,*scheme-f* (REG ,acc))
             (SET (REG ,acc) 0)
             (SETE (REG "al"))
             (SAL 4 (REG ,acc))
             (OR ,*scheme-f* (REG ,acc))))
        (('%fixnum? expr)
         `(,@(expr->ir expr si acc)
             (AND ,3 (REG ,acc))
             (CMP ,0 (REG ,acc))
             (SET (REG ,acc) 0)
             (SETE (REG "al"))
             (SAL 4 (REG ,acc))
             (OR ,*scheme-f* (REG ,acc))))

        (('if test conseq altern)
         (let ((alt-label (genlabel))
               (end-label (genlabel)))
           `(,@(expr->ir test si acc)
               (CMP ,*scheme-f* (REG ,acc))
               (JE ,alt-label)
               ,@(expr->ir conseq si acc)
               (JMP ,end-label)
               (DEFLABEL ,alt-label)
               ,@(expr->ir altern si acc)
               (DEFLABEL ,end-label))))
        
        (('%+ expr1 expr2)
         (let ((r1 (genreg))
               (r2 (genreg)))
           `(,@(expr->ir expr2 si r2)
               ,@(expr->ir expr1 si r1)
               (ADD (REG ,r2) (REG ,r1))
               (SET (REG ,acc) (REG ,r1)))))

        (('%- expr1 expr2)
         (let ((r1 (genreg))
               (r2 (genreg)))
           `(,@(expr->ir expr2 si r2)
               ,@(expr->ir expr1 si r1)
               (SUB (REG ,r2) (REG ,r1))
               (SET (REG ,acc) (REG ,r1)))))

        (('plus expr1 expr2)
         `(,@(expr->ir expr2 si acc)
             (SET ((REG "rsp") ,si) (REG ,acc)) ;; base register, displ  => -si(%rsp)
             ,@(expr->ir expr1 (- si *word-size*) acc)
             (ADD ((REG "rsp" ) ,si) (REG ,acc))))

        (t
         (error (make-condition 'scheme-compile-error
                                :expr x :reason "unknown expr"))))))
        
(defun compile-program (x)
  (flet ((emit-header ()
           (emit "	.text")
           (emit "	.p2align 4,,15")
           (emit ".globl scheme_entry")
           (emit "	.type	scheme_entry, @function")
           (emit "scheme_entry:"))
         (print-info (ir stage)
           (format *terminal-io* ";;; Carve IR ~a~%" stage)
           (dump-ir ir *terminal-io*))
         )
    (emit-header)
    (let* ((si (- *word-size*))
           (ir0 (expr->ir x si "rax"))
           (ir1 (allocate-register ir0)))
      (print-info ir0 "IR0")
      (print-info ir1 "IR1")
      (emit-asm ir1)
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
           (run `(%sub1 ,(1+ most-negative-immediate-integer)) nil))))

(deftest test-if ()
  (check
    (equal "#t" (run '(if |#t| |#t| |#f|) nil))
    (equal "#f" (run '(if |#f| |#t| |#f|) nil))
    (equal "3" (run '(if |#t| 3 4) nil))
    (equal "4" (run '(if |#f| 3 4) nil))
    (equal "6" (run '(if |#t| (%add1 5) 4) nil))
    (equal "9" (run '(if |#f| (%add1 5) (%add1 8)) nil))
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
          (num-code (1+ (apply #'max (flatten (mapcar #'cdr liveness))))))
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
/ygap 20 def
/x0gap 100 def
/xgap 25 def
/y0 750 def

/figwidth xgap num-reg 2 mul mul def
x0gap y0 ygap figwidth num-code hdashlines~%"
              num-reg num-code)
      (loop for r in regs for i from 1
         do
           (format out "~a ~a ~a regline~%"
                   i
                   (nth 1 (assoc r liveness))
                   (nth 2 (assoc r liveness))))
      
      (format out
              "showpage
grestore"))))