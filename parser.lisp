;;; LALR parser generator.
;;; Julian Squires / 2005

;;; notes for rewrite:
;;;
;;; When we preprocess the grammar, give every symbol a unique
;;; integer, and then use bitvectors for all set operations.  Keep a
;;; bitvector to track terminal/nonterminal-ness.
;;; (any benefit to doing this?)
;;;
;;; Add a suite of tests using RT.
;;;
;;; Write some usage information.
;;;
;;; Add some operator precedence controls.
;;;
;;; Code to convert yacc file into suitable grammar.

(in-package :lalr-parser-generator)

;;;; Special variables.

(defparameter *start-symbol* 'start)
(defparameter *end-symbol* '$)

(defvar *grammar* nil
  "The default grammar used by the LALR parser generator; set by
PROCESS-GRAMMAR.")
(defvar *first-set* nil)
(defvar *follow-set* nil)
(defvar *nullable-set* nil)


;;;; LALR ITEMS
;;; We could use a structure instead of a list here, and it would
;;; probably be much more efficient.  For the moment, it doesn't
;;; matter.

(defstruct item (lhs) (rhs) (dot) (lookahead))

;;; XXX should these dot functions operate on the dot itself, rather
;;; than calling item-dot?  That would make it easier to hide the fact
;;; that dot is just a list.
(defun dot-at-end-p (item) (endp (item-dot item)))
(defun symbol-at-dot (item) (car (item-dot item)))
(defun advance-dot (item)
  "Returns the item dot, advanced by one symbol.  Note:
non-destructive."
  (cdr (item-dot item)))


;;; item sets -- see also macros.lisp.

(defun make-item-set (&rest items)
  (let ((set (make-array '(0) :adjustable t :fill-pointer 0)))
    (dolist (i items) (add-to-set i set))
    set))


(defun items-equal-except-lookahead-p (a b)
  (every (lambda (x) (equal (funcall x a) (funcall x b)))
	 (list #'item-lhs #'item-rhs #'item-dot)))

(defun add-to-set (item set)
  "Returns position of ITEM in SET."
  (or (dotimes (i (length set))
	(when (items-equal-except-lookahead-p item (aref set i))
	  (unless (equal (item-lookahead item) (item-lookahead (aref set i)))
	    (setf (item-lookahead (aref set i))
		  (union (item-lookahead item)
			 (item-lookahead (aref set i)))))
	  (return i)))
      ;;(position item set :test #'equalp)
      (vector-push-extend item set)))

(defun item-set-equal-ignoring-la (set-a set-b)
  (when (= (length set-a) (length set-b))
    (every #'items-equal-except-lookahead-p set-a set-b)))


;;;; GRAMMAR

(defun process-grammar (grammar)
  "Processes GRAMMAR, returns a grammar suitable for binding to
*GRAMMAR.  Augments the grammar with a new start rule."
  ;; split grammar into hash table of non-terminals, terminals.

  ;; the grammar is a list of non-terminals followed by their
  ;; productions.
  ;;
  ;; we compile the basic hash table of non-terminals by iterating
  ;; through the grammar, storing the lists of productions.
  (let ((grammar-hash (make-hash-table)))
    (do ((list-> grammar (cddr list->)))
	((null list->))
      (setf (gethash (car list->) grammar-hash) 
	    (cadr list->)))

    ;; augment grammar with start symbol
    (dolist (i (list *start-symbol* *end-symbol*))
      (assert (null (gethash i grammar-hash)) nil
	      "~A is a reserved non-terminal, unfortunately.  Try
calling MAKE-PARSER with a different END-SYMBOL or START-SYMBOL
specified."  i))
    (setf (gethash *start-symbol* grammar-hash)
	  (list (list (car grammar) *end-symbol*)))
    grammar-hash))

(defun non-terminal-p (symbol) (gethash symbol *grammar*))
(defun grammar-productions (symbol) (gethash symbol *grammar*))


;;;; PARSE TABLE CONSTRUCTION

(defun first-sets (symbol-list)
  (do* ((x-> symbol-list (cdr x->))
	(s (and x-> (gethash (car x->) *first-set*))
	   (union s (and x-> (gethash (car x->) *first-set*)))))
       ((or (null x->) (not (gethash (car x->) *nullable-set*)))
	s)))

(defun lalr-closure (item-set)
  "Returns the closure of ITEM-SET."
  (do-until-unchanged (item-set)
    (do-for-each-item (i item-set)
      (when (non-terminal-p (symbol-at-dot i))
	(dolist (r (grammar-productions (symbol-at-dot i)))
	  (add-to-set (make-item :lhs (symbol-at-dot i) :rhs r :dot r
				 :lookahead (union (first-sets (advance-dot i))
						   (item-lookahead i)))
		      item-set)))))
  item-set)

(defun lalr-goto (item-set grammar-symbol)
  "Returns the closure of ITEM-SET after having read GRAMMAR-SYMBOL."
  (let ((j (make-item-set)))
    (do-for-each-item (i item-set)
      (when (eql (symbol-at-dot i) grammar-symbol)
	(add-to-set (make-item :lhs (item-lhs i) :rhs (item-rhs i)
			       :dot (advance-dot i)
			       :lookahead (item-lookahead i))
		    j)))
    (lalr-closure j)))

(defun make-start-item ()
  "Makes the item S' -> .S$, as appropriate for the grammar."
  (make-item :lhs *start-symbol*
	     :rhs (first (gethash *start-symbol* *grammar*))
	     :dot (first (gethash *start-symbol* *grammar*))))

(defun make-almost-done-item ()
  "Makes the item S' -> S.$, as appropriate for the grammar."
  (let* ((start-item (make-start-item))
	 (dot (do ((dot (advance-dot start-item) (cdr dot)))
		  ((or (null dot) (eql (car dot) *end-symbol*)) dot))))
    (assert (not (null dot)))
    (make-item :lhs (item-lhs start-item) :rhs (item-rhs start-item)
	       :dot dot)))



(defun merge-lookahead-in-sets (src dst)
  (macrolet ((la (set) `(item-lookahead (aref ,set i))))
    (dotimes (i (length dst))
      (unless (equal (la dst) (la src))
	(setf (la dst) (union (la dst) (la src)))))))

(defun add-to-states (set states)
  "Adds SET to STATES, either by merging it with another set which is
identical save for look-ahead, or push it onto the end.  Returns the
index in STATES."
  (flet ((merge-existing ()
	   (dotimes (i (length states))
	     (when (item-set-equal-ignoring-la set (aref states i))
	       (merge-lookahead-in-sets set (aref states i))
	       (return i)))))
    (or (merge-existing) (vector-push-extend set states))))

(defun make-initial-state ()
  (lalr-closure (make-item-set (make-start-item))))

(defun compute-shifts ()
  "Computes shift actions and states for the generated parser.  Returns
a list of shift actions and the state table."
  (let ((shift-table nil)
	(states (make-array '(1) :adjustable t :fill-pointer 1
			    :initial-element (make-initial-state))))
    (do-until-unchanged (states shift-table)
      (dotimes (i (length states))
	(do-for-each-item (item (aref states i))
	  (unless (or (dot-at-end-p item)
		      (eql (symbol-at-dot item) *end-symbol*))
	    (let* ((x (symbol-at-dot item))
		   (new-set (lalr-goto (aref states i) x))
		   (j (add-to-states new-set states)))
	      (pushnew (list i x j) shift-table :test #'equalp))))))
    (values shift-table states)))


(defun compute-reductions (states)
  "Compute reduce actions for the generated parser.  Depends on
*STATE* already being filled, and returns the reduce actions."
  (let ((reduce-table nil))
    (dotimes (i (length states))
      (do-for-each-item (item (aref states i))
	(when (dot-at-end-p item)
	  (dolist (j (item-lookahead item))
	    (pushnew (list i j item) reduce-table :test #'equalp)))))
    reduce-table))


;; XXX revisit
(defun add-accept-actions (parse-table states)
  "Finds states whose next token should be $ (EOF) and adds accept
actions to the parse table for those states."
#|  (loop with n-states = (length states)
	and item = (make-almost-done-item)
	for i from 0 to n-states
	when (find item (aref states i) :test #'equalp)
	do (add-to-parse-table parse-table n-states i *end-symbol* '(accept)))) |#
  (do* ((i 0 (1+ i))
	(n-states (length states))
	(item (make-almost-done-item)))
       ((>= i n-states))
    (when (find item (aref states i) :test #'equalp)
      (add-to-parse-table parse-table n-states i *end-symbol* `(accept)))))


(defun add-to-parse-table (parse-table n-states i x action)
  "Adds ACTION to the parse table at (X,I).  Applies braindead
conflict resolution rule to any conflicts detected."
  (sunless (gethash x parse-table)
    (setf it (make-array (list n-states) :initial-element nil)))
  (aif (aref (gethash x parse-table) i)
       ;; XXX should probably collate the number of conflicts
       ;; somewhere.
       ;; XXX should resolve reduce/reduce conflicts by reducing by
       ;; the largest rule.
       (warn "~&Conflict at ~A,~A -> last action ~A, new action ~A."
	     x i it action)
       (cond ((and (eql it 'shift) (eql action 'reduce))
	      ;; shift-reduce conflict
	      )
	     ((and (eql it 'reduce) (eql action 'reduce))
	      ;; reduce-reduce conflict
	      )
	     (t (error "This is an unexpected conflict.  Call a wizard.")))
  ;;   (assert (null (aref (gethash x parse-table) i)))
       (setf (aref (gethash x parse-table) i) action)))


(defun create-parse-table (shifts reductions states)
  "Constructs a parse table usable by PARSE, from the list of shift
and reduce actions, and the set of parse states."
  (let ((parse-table (make-hash-table))
	(n-states (length states)))
    (dolist (shift shifts)
      (destructuring-bind (i x j) shift
	(add-to-parse-table parse-table n-states i x
			    (list (if (non-terminal-p x) 'goto 'shift) j))))

    (dolist (reduce reductions)
      (destructuring-bind (i x j) reduce
	(add-to-parse-table parse-table n-states i x
			    `(reduce ,(item-lhs j) ,(length (item-rhs j))))))
    (add-accept-actions parse-table states)

    parse-table))


;;; XXX certainly not the most attractive way to do this, but I've
;;; done worse...
(defun write-parser-function (table package stream fn-name)
  (let* ((*package* (find-package "LALR-PARSER-GENERATOR"))
	 (fn-name (intern (if (stringp fn-name)
			      fn-name
			      (symbol-name fn-name)))))
    (format stream ";; Automatically generated by LALR-PARSER-GENERATOR.")
    (format stream "~&(in-package ~S)~%" (package-name package))
    (pprint `(flet ((unmash (entries)
		     (let ((ht (make-hash-table)))
		       (dolist (e entries)
			 (setf (gethash (car e) ht) (cdr e)))
		       ht)))
	      (let ((table (unmash ',(let ((untable))
					  (maphash (lambda (k v)
						     (push (cons k v)
							   untable))
						   table)
					  untable))))
		(defun ,fn-name (next-token)
		  "NEXT-TOKEN is a function which returns a cons of the next token in
the input (the CAR being the symbol name, the CDR being any
information the lexer would like to preserve), and advances the input
one token.  Returns what might pass for a parse tree in some
countries."
		  (do* ((stack (list 0))
			(token (funcall next-token))
			(result-stack nil)
			(row (gethash (car token) table)
			     (gethash (car token) table)))
		       (nil)
		    (unless row
		      (error "~A is not a valid token in this grammar." token))
		    (let ((action (aref row (first stack))))
		      (case (first action)
			(shift
			 (push token result-stack)
			 (setf token (funcall next-token))
			 (push (second action) stack))
			(reduce
			 (push (list (second action)) result-stack)
			 (dotimes (i (third action))
			   (pop stack)
			   (push (pop (cdr result-stack)) (cdar result-stack)))
			 (destructuring-bind (goto state)
			     (aref (gethash (second action) table) (first stack))
			   (assert (eql goto 'goto) (state) "Malformed parse table!")
			   (push state stack)))
			(accept (return (car result-stack)))
			(t (error "Parse error at ~A" token)))))))))))


(defun parse (table next-token)
  "TABLE is a table generated by CREATE-PARSE-TABLE, NEXT-TOKEN is a
function which returns a cons of the next token in the input (the CAR
being the symbol name, the CDR being any information the lexer would
like to preserve), and advances the input one token.  Returns what
might pass for a parse tree in some countries."
  (declare (optimize (debug 3)))
  (do* ((stack (list 0))
	(token (funcall next-token))
	(result-stack nil)
	(row (gethash (car token) table)
	     (gethash (car token) table)))
       (nil)
    (unless row
      (error "~A is not a valid token in this grammar." token))
    (let ((action (aref row (first stack))))
      (case (first action)
	(shift
	 (push token result-stack)
	 (setf token (funcall next-token))
	 (push (second action) stack))
	(reduce
	 (push (list (second action)) result-stack)
	 (dotimes (i (third action))
	     (pop stack)
	     (push (pop (cdr result-stack)) (cdar result-stack)))
	   (destructuring-bind (goto state)
	       (aref (gethash (second action) table) (first stack))
	     (assert (eql goto 'goto) (state) "Malformed parse table!")
	     (push state stack)))
	(accept (return (car result-stack)))
	(t (error "Parse error at ~A" token))))))


;;;; External functions

;; XXX document this, improve interface
(defun make-parser (grammar &key end-symbol start-symbol
		    (stream *standard-output*)
		    (package *package*)
		    (fn-name 'parse))
  "Writes a parser for GRAMMAR onto STREAM, with symbols in PACKAGE;
notably, with the parser name being FN-NAME (default of PARSE)."
  (awhen end-symbol (setf *end-symbol* it))
  (awhen start-symbol (setf *start-symbol* it))
  (let ((*grammar* (process-grammar grammar)))
    (process-grammar grammar)
    (multiple-value-bind (*first-set* *follow-set* *nullable-set*)
	(compute-prediction-sets *grammar*)
      (multiple-value-bind (shifts states) (compute-shifts)
	(let ((table (create-parse-table shifts 
					 (compute-reductions states)
					 states)))
	  (write-parser-function table package stream fn-name))))))


;;;; Testing stuff.

(defun test-parser (grammar string)
  (let ((*grammar* (process-grammar grammar)))
    (multiple-value-bind (*first-set* *follow-set* *nullable-set*)
	(compute-prediction-sets *grammar*)
      (with-input-from-string (*standard-input* string)
	(multiple-value-bind (shifts states) (compute-shifts)
	  (parse (create-parse-table shifts 
				     (compute-reductions states)
				     states)
		 (lambda () (cons (read) nil))))))))

(defparameter *lr0-test-grammar*
  '(sentence ((open list close)
	      (variable))
    list ((sentence)
	  (list comma sentence))))

(defparameter *slr-test-grammar*
  '(E ((T + E) (T))
    T ((x))))

(defparameter *simple-nullable-test-grammar*
  '(Z ((d)
       (X Y Z))
    Y (nil
       (c))
    X ((Y)
       (a))))

(defparameter *simple-lalr-test-grammar*
  '(S ((E))
    E ((E - T) (T))
    T ((n) (OPEN E CLOSE))))

(defparameter *nicer-looking-test-grammar*
"S = E
 E = E - T
   | T

 T = n
   | ( E )")