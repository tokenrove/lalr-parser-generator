
(in-package :lalr-parser-generator)

;;; It's too bad PSXHASH isn't available everywhere.

(defconstant +simple-hash-multiplier+ 31
  "Multiplication constant suggested by Kernighan and Pike for simple
hashing applications.")

(defun simple-checksum (x)
  "Provides an SXHASH-style checksum of X, but also sloppily handles
arrays and hash tables, like SBCL's PSXHASH.  However, this checksum
was only designed for use in comparing relatively similar structures,
so it shouldn't be used as a general replacement for something like
PSXHASH."
  (typecase x
    (array (simple-array-sum x))
    (hash-table (simple-hash-sum x))
    (t (sxhash x))))

(defun simple-hash-sum (hash-table)
  (loop for x being each hash-value of hash-table
	summing (simple-checksum x)))

(defun simple-array-sum (array)
  (loop for x across array
	summing (simple-checksum x)))

;;; Note: there are various ways we can make this much more efficient,
;;; but I don't think it really matters that much.
(defmacro do-until-unchanged1 (var &body body)
  "Loop BODY until VAR doesn't change (according to EQUALP) between
iterations."
  (let ((last-time (gensym)))
    `(let ((,last-time))
      (tagbody
       top
	 (setf ,last-time (simple-checksum ,var))
	 ,@body
	 (unless (equal ,last-time (simple-checksum ,var))
	   (go top)))
      ,var)))

(defmacro do-until-unchanged (vars &body body)
  "Loop BODY until each variable in VARS doesn't change (according to
EQUALP) between iterations."
  (if vars
      `(do-until-unchanged1 ,(car vars)
	(do-until-unchanged ,(cdr vars)
	  ,@body))
      `(progn ,@body)))


(defmacro dovector ((var vector) &body body)
  "Iterate VAR across VECTOR."
  `(loop for ,var across ,vector
         do (progn ,@body)))


(defmacro do-for-each-item ((var set) &body body)
  "Iterate VAR across the item-set SET."
  `(dovector (,var ,set) ,@body))

;;; grammar traversal

(defmacro do-for-each-production ((lhs rhs grammar) &body body)
  "For each production in GRAMMAR, BODY is called with LHS and RHS
bound to the left-hand side and right-hand side (in the form of a list
of tokens) of the grammar rule."
  (let ((value (gensym)))
    `(maphash (lambda (,lhs ,value)
		(dolist (,rhs ,value)
		  ,@body))
      ,grammar)))

(defmacro do-for-each-terminal ((var grammar) &body body)
  "Do BODY for each terminal symbol referenced in GRAMMAR."
  (let ((list (gensym))
	(unused (gensym)))
    (declare (ignore unused))
    `(do-for-each-production (,unused ,list ,grammar)
      (dolist (,var ,list)
	(when (not (non-terminal-p ,var))
	  ,@body)))))

