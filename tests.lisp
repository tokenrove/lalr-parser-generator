
(defpackage :lalr-parser-generator-tests
  (:use :cl :rt :lalr-parser-generator))

(in-package :lalr-parser-generator-tests)


;;;; LR(0) GRAMMARS

#| (defparameter *lr0-test-grammar*
'(sentence ((open list close)
(variable))
list ((sentence)
(list comma sentence)))) |#

;; Basic parsing test.
(deftest lr0-grammar.1
    (let ((input "open variable comma open open variable close comma variable close close"))
      (lalr-parser-generator::test-parser '(sentence ((open list close)
						      (variable))
					    list ((sentence)
						  (list comma sentence)))
					  input))
  (SENTENCE
   (OPEN)
   (LIST
    (LIST (SENTENCE (VARIABLE)))
    (COMMA)
    (SENTENCE (OPEN)
	      (LIST (LIST
		     (SENTENCE (OPEN)
			       (LIST (SENTENCE (VARIABLE)))
			       (CLOSE)))
		    (COMMA)
		    (SENTENCE (VARIABLE)))
	      (CLOSE)))
   (CLOSE)))

;; Test for failure: parse errors.
(deftest lr0-grammar.2
    (let ((input "open"))
      (handler-case
	  (lalr-parser-generator::test-parser '(sentence ((open list close)
							  (variable))
						list ((sentence)
						      (list comma sentence)))
					      input)
	(simple-error () t)))
  t)

(deftest lr0-grammar.3
    (let ((input "open variable comma open open variable close comma variable close close open"))
      (handler-case
	  (lalr-parser-generator::test-parser '(sentence ((open list close)
							  (variable))
						list ((sentence)
						      (list comma sentence)))
					      input)
	(simple-error () t)))
  t)


#| (defparameter *slr-test-grammar*
  '(E ((T + E) (T))
    T ((x)))) |# 

(deftest slr-grammar.1
    (let ((input "x + x + x"))
      (lalr-parser-generator::test-parser '(E ((T + E) (T))
					    T ((x)))
					  input))
  (E (T (x)) (+) (E (T (x)) (+) (E (T (x))))))

#| (defparameter *simple-nullable-test-grammar*
  '(Z ((d)
       (X Y Z))
    Y (nil
       (c))
    X ((Y)
       (a)))) |#

;; XXX has shift/reduce conflicts
(deftest nullable-grammar.1
    (let ((input "a d"))
      (handler-bind ((warning #'muffle-warning))
	(lalr-parser-generator::test-parser '(Z ((d) (X Y Z))
					      Y (nil (c))
					      X ((Y) (a)))
					    input)))
  (Z (X (A)) (Y) (Z (D))))

#|
(defparameter *simple-lalr-test-grammar*
  '(S ((E))
    E ((E - T) (T))
    T ((n) (OPEN E CLOSE))))
 |#

(deftest lalr-grammar.1
    (let ((input "open n - open n close - n close - open n close"))
      (lalr-parser-generator::test-parser '(S ((E))
					    E ((E - T) (T))
					    T ((n) (OPEN E CLOSE)))
					  input))
  (S (E (E
	 (T (OPEN)
	    (E (E (E (T (N))) (-) (T (OPEN) (E (T (N))) (CLOSE))) (-) (T (N)))
	    (CLOSE)))
	(-)
	(T (OPEN) (E (T (N))) (CLOSE)))))

#|
(defparameter *nicer-looking-test-grammar*
"S = E
 E = E - T
   | T

 T = n
   | ( E )")
 |#


;;;; MISC. FAILURE CONDITIONS

;; Test for failure: bad terminal.
(deftest test-for-failure.1
    (let ((input "not-a-terminal"))
      (handler-case
	  (lalr-parser-generator::test-parser '(sentence ((variable))) input)
	(simple-error () t)))
  t)

;; Expected shift-reduce conflict.

;; Expected reduce-reduce conflict.

;;;; MAKE-PARSER

;; test make-parser by evaluating its output etc

;;;; STRESS TESTS

;; Stress test with random sentence generation.
