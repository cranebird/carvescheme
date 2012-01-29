(in-package :carve)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (set-scm-macro-character))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; test
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro check* (&rest data)
  "Run each expression in data as a (expect s-exp)."
  `(check
     ,@(loop for (expect exp) in data
          collect `(equal ,expect (run ,exp nil)))))

(deftest test-immediate ()
  (check*
   ("13" 13)
   ("7" 7)
   ("()" nil)
   ("#\\A" #\A)
   ("#\\1" #\1)
   ("#\\9" #\9)
   ("#t" '#t)
   ("#f" '#f)))

(deftest test-unary-primitive ()
  (check*
   ("1" '(%add1 0))
   ("2" '(%add1 1))
   ("0" '(%add1 -1))
   ("-1" '(%add1 -2))
   ("-2" '(%add1 -3))
   ("3" '(%add1 (%add1 (%add1 0))))
   ("1" '(%add1 (%sub1 (%add1 0))))
   ("#\\A" `(%fixnum->char ,(char-code #\A)))
   ("#\\l" `(%fixnum->char ,(char-code #\l)))
   ((format nil "~a" (char-code #\Z)) `(%char->fixnum #\Z))
   ("#t" '(%zero? 0))
   ("#f" '(%zero? 3))
   ("#t" '(%zero? (%add1 -1)))
   ("#f" '(%zero? (%sub1 -1)))
   ("#t" '(%zero? (%sub1 (%sub1 2))))

   ("#t" '(%null? nil))
   ("#f" '(%null? 3))
   ("#f" '(%null? 0))

   ("#t" '(%boolean? #t))
   ("#t" '(%boolean? #f))
   ("#f" '(%boolean? 4))
   ("#f" '(%boolean? -1))
   ("#f" '(%boolean? nil))
   ("#f" '(%boolean? #\a))

   ("#t" '(%fixnum? 0))
   ("#t" '(%fixnum? 4))
   ("#t" '(%fixnum? -2))
   ("#t" '(%fixnum? (%add1 -1)))
   ("#f" '(%fixnum? #t))
   ("#f" '(%fixnum? #f))
   ("#f" '(%fixnum? (%zero? 3)))
   ("#f" '(%fixnum? (%zero? 0)))))

(deftest test-unary-primitive-edge ()
  (check*
   ((format nil "~a" most-positive-immediate-integer)
    `(%add1 ,(1- most-positive-immediate-integer)))
   ((format nil "~a" most-negative-immediate-integer)
    `(%sub1 ,(1+ most-negative-immediate-integer)))))

(deftest test-if ()
  (check*
   ("#t" '(if #t #t #f))
   ("#f" '(if #f #t #f))
   ("3" '(if #t 3 4))
   ("4" '(if #f 3 4))
   ("6" '(if #t (%add1 5) 4))
   ("9" '(if #f (%add1 5) (%add1 8)))))

(deftest test-+ ()
  (check*
   ("3" '(%+ 1 2))
   ("4" '(%+ -1 5))
   ("10" '(%+ 10 0))
   ("7" '(%+ (%+ 1 2) 4))
   ("7" '(%+ (%+ 1 2) (%+ 3 1)))
   ("7" '(%+ (%add1 2) 4))
   ("8" '(%+ (%add1 2) (%add1 4)))))

(deftest test-high-register-pressure ()
  (check*
   ("105"
    '(%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ 1 2) 3) 4) 5) 6) 7) 8) 9) 10) 11) 12) 13) 14))
   ("120"
    '(%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ 1 2) 3) 4) 5) 6) 7) 8) 9) 10) 11) 12) 13) 14) 15))
   ("191"
    '(%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ 1 2) 3) 4) 5) 6) 7) 8) 9) 10) 11) 12) 13) 14)
      (%+ (%+ 20 21) (%+ 22 23))))
   ("245"
    '(%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ (%+ 1 2) 3) 4) 5) 6) (%+ 30 31)) 8) 9) 10) 11) 12) 13) 14)
      (%+ (%+ 20 21) (%+ 22 23))))
   ))

(deftest test-- ()
  (check*
   ("3" '(%- 4 1))
   ("-1" '(%- 1 2))
   ("-6" '(%- -1 5))
   ("10" '(%- 10 0))
   ))

(deftest test-* ()
  (check*
   ("1" '(%* 1 1))
   ("2" '(%* 1 2))
   ("8" '(%* 2 4))
   ("9" '(%* 3 3))
   ("9" '(%* 9 1))
   ("21" '(%* 3 7))
   ("21" '(%* 7 3))
   ("96" '(%* 12 8))
   ("0" '(%* 0 5))
   ("49" '(%* 7 7))
   ("10" '(%* 5 (%add1 1)))
   ("10" '(%* (%+ 2 3) (%add1 (%add1 0))))
   ("99" '(%* (%* 3 3) (%+ 10 1)))
   ("99" '(%* (%* 3 (%add1 2)) (%+ (%* 4 2) 3)))
   ))

(deftest test-*-edge ()
  (check*
   ("2305843009213693950" '(%* 1152921504606846975 2)) ;; most-positive-immediate-integer - 1
   ("2305843009213693951" '(%+ 1 (%* 1152921504606846975 2))) ;; most-positive-immediate-integer
   ))
