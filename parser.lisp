;;; LALR parser generator.
;;; Julian Squires / 2005

;;; Things to do:
;;;
;;; Add some operator precedence controls.
;;;
;;; Write some usage information.
;;;
;;; When we preprocess the grammar, give every symbol a unique
;;; integer, and then use bitvectors for all set operations.  Keep a
;;; bitvector to track terminal/nonterminal-ness.
;;;
;;; Code to convert yacc file into suitable grammar.
;;;
;;; Refactor heavily.

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
  (let* ((i (or (position item set :test #'items-equal-except-lookahead-p)
		(vector-push-extend item set)))
	 (la-of-a (item-lookahead item))
	 (la-of-b (item-lookahead (aref set i))))
    (unless (equal la-of-a la-of-b)
      (unionf (item-lookahead (aref set i)) la-of-a))))

(defun item-set-equal-ignoring-la (set-a set-b)
  (when (= (length set-a) (length set-b))
    (every #'items-equal-except-lookahead-p set-a set-b)))


;;;; GRAMMAR

(defun process-grammar (grammar)
  "Processes GRAMMAR, returns a grammar suitable for binding to
*GRAMMAR*.  Augments the grammar with a new start rule."
  ;; we compile the basic hash table of non-terminals by iterating
  ;; through the grammar, storing the lists of productions.
  (let ((grammar-hash (make-hash-table)))
    (do ((list-> grammar (cddr list->)))
	((null list->))
      (setf (gethash (car list->) grammar-hash) 
	    (cadr list->)))

    (augment-grammar grammar-hash (car grammar))
    grammar-hash))

(defun augment-grammar (hash first-real-symbol)
  ;; augment grammar with start symbol
  (dolist (i (list *start-symbol* *end-symbol*))
    (assert (null (gethash i hash)) nil
	    "~A is a reserved non-terminal, unfortunately.  Try
calling MAKE-PARSER with a different END-SYMBOL or START-SYMBOL
specified."  i))
  (setf (gethash *start-symbol* hash)
	(list (list first-real-symbol *end-symbol*))))

(defun non-terminal-p (symbol) (gethash symbol *grammar*))
(defun grammar-productions (symbol) (gethash symbol *grammar*))


;;;; PARSE TABLE CONSTRUCTION

(defun first-sets (symbol-list)
  "Returns the union of the first sets of each symbol in SYMBOL-LIST,
until either a nullable symbol is found or we run out of symbols."
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
	(unionf (la dst) (la src))))))

(defun add-to-states (set states)
  "Adds SET to STATES, either by merging it with another set which is
identical save for look-ahead, or push it onto the end.  Returns the
index in STATES."
  (flet ((merge-existing ()
	   (loop for i below (length states)
		 and other-set across states
		 when (item-set-equal-ignoring-la set other-set)
		 do (merge-lookahead-in-sets set other-set)
		    (return i))))
    (or (merge-existing) (vector-push-extend set states))))

(defun make-initial-state ()
  (lalr-closure (make-item-set (make-start-item))))

(defun compute-shifts (table)
  "Computes shift actions and states for the generated parser.  Adds
shifts to the parse table as we find them.  Returns the state table."
  (let ((states (make-array '(1) :adjustable t :fill-pointer 1
			    :initial-element (make-initial-state))))
    (do-until-unchanged (states) ;; XXX also table?
      (dotimes (i (length states))
	(do-for-each-item (item (aref states i))
	  (maybe-shift table states item i))))
    states))

;; XXX awful name; refactor.
(defun maybe-shift (table states item i)
  (unless (or (dot-at-end-p item)
	      (eql (symbol-at-dot item) *end-symbol*))
    (let* ((symbol (symbol-at-dot item))
	   (new-set (lalr-goto (aref states i) symbol))
	   (j (add-to-states new-set states))
	   (action (list (if (non-terminal-p symbol) 'goto 'shift) j)))
      (add-to-parse-table table i symbol action))))


(defun compute-reductions (table states)
  "Compute reduce actions for the generated parser, based on STATES.
Fills in TABLE with the reduce actions."
  (dotimes (i (length states))
    (do-for-each-item (item (aref states i))
      (when (dot-at-end-p item)
	(dolist (symbol (item-lookahead item))
	  (let ((action `(reduce ,(item-lhs item)
			  ,(length (item-rhs item)))))
	    (add-to-parse-table table i symbol action)))))))


(defun add-accept-actions (parse-table states)
  "Finds states whose next token should be $ (EOF) and adds accept
actions to the parse table for those states."
  (loop with n-states = (length states)
	and item = (make-almost-done-item)
	for i from 0 below n-states
	when (find item (aref states i) :test #'equalp)
	do (add-to-parse-table parse-table i *end-symbol* '(accept))))


(defun add-to-parse-table (parse-table state symbol action)
  "Adds ACTION to the parse table at (SYMBOL,STATE).  Applies braindead
conflict resolution rule to any conflicts detected."
  (sunless (gethash symbol parse-table)
    (setf it (make-hash-table :test 'equal)))
  (let ((row (gethash symbol parse-table)))
    (awhen (gethash state row)
      (when (equal action it) (return-from add-to-parse-table))
      (setf action (resolve-collision action it symbol state))
      (warn "Preferring ~A." action))
    (setf (gethash state row) action)))


(defun resolve-collision (new-action old-action symbol state)
  ;; XXX should probably collate the number of conflicts
  ;; somewhere.
  (warn "~&Conflict at ~A,~A -> last action ~A, new action ~A."
	symbol state old-action new-action)
  (cond ((and (eql (car old-action) 'shift) (eql (car new-action) 'reduce))
	 old-action)			; S/R => prefer shift.
	((and (eql (car old-action) 'reduce) (eql (car new-action) 'reduce))
	 ;; R/R => prefer longer reduction.
	 (if (>= (third new-action) (third old-action))
	     new-action
	     old-action))
	(t (error "This is an unexpected conflict (~A, ~A).  Call a wizard."
		  old-action new-action))))


(defun create-parse-table ()
  "Constructs a parse table usable by PARSE."
  (let* ((parse-table (make-hash-table))
	 (states (compute-shifts parse-table)))
    (compute-reductions parse-table states)
    (add-accept-actions parse-table states)
    parse-table))



(defun hash->tree (table)
  (let ((acc))
    (maphash #'(lambda (k v) (push (cons k (typecase v
					     (hash-table (hash->tree v))
					     (t v)))
				   acc))
	     table)
    acc))

(defun tree->hash (tree)
  (let ((ht (make-hash-table))) 
    (dolist (x tree)
      (setf (gethash (car x) ht)
	    (if (listp (second x))
		(tree->hash (cdr x))
		(cdr x))))
    ht))

;;; XXX certainly not the most attractive way to do this, but I've
;;; done worse...
(defun write-parser-function (table package stream fn-name)
  (let* ((*package* (find-package "LALR-PARSER-GENERATOR"))
	 (fn-name (intern (if (stringp fn-name)
			      fn-name
			      (symbol-name fn-name)))))
    (format stream ";; Automatically generated by LALR-PARSER-GENERATOR.")
    (format stream "~&(in-package ~S)~%" (package-name package))
    (pprint `(labels ((tree->hash (tree)
		       (let ((ht (make-hash-table))) 
			 (dolist (x tree)
			   (setf (gethash (car x) ht)
				 (if (listp (second x))
				     (tree->hash (cdr x))
				     (cdr x))))
			 ht)))
	      (let ((table (tree->hash ',(hash->tree table))))
		(defun ,fn-name (next-token)
		  "NEXT-TOKEN is a function which returns a cons of the next token in
the input (the CAR being the symbol name, the CDR being any
information the lexer would like to preserve), and advances the input
one token.  Returns what might pass for a parse tree in some
countries."
  (loop with stack = (list 0)
	and token = (funcall next-token)
	and result-stack
	for row = (gethash (car token) table)
	for action = (if row 
			 (gethash (first stack) row)
			 (error "~A is not a valid token in this grammar."
				token))
	do (case (first action)
	     (shift (push token result-stack)
		    (setf token (funcall next-token))
		    (push (second action) stack))
	     (reduce (push (list (second action)) result-stack)
		     (dotimes (i (third action))
		       (pop stack)
		       (push (pop (cdr result-stack)) (cdar result-stack)))
		     (destructuring-bind (goto state)
			 (gethash (first stack) (gethash (second action) table))
		       (assert (eql goto 'goto) () "Malformed parse table!")
		       (push state stack)))
	     (accept (return (car result-stack)))
	     (t (error "Parse error at ~A" token))))))) stream)))


(defun parse (table next-token)
  "TABLE is a table generated by CREATE-PARSE-TABLE, NEXT-TOKEN is a
function which returns a cons of the next token in the input (the CAR
being the symbol name, the CDR being any information the lexer would
like to preserve), and advances the input one token.  Returns what
might pass for a parse tree in some countries."
  (loop with stack = (list 0)
	and token = (funcall next-token)
	and result-stack
	for row = (gethash (car token) table)
	for action = (if row 
			 (gethash (first stack) row)
			 (error "~A is not a valid token in this grammar."
				token))
	do (case (first action)
	     (shift (push token result-stack)
		    (setf token (funcall next-token))
		    (push (second action) stack))
	     (reduce (push (list (second action)) result-stack)
		     (dotimes (i (third action))
		       (pop stack)
		       (push (pop (cdr result-stack)) (cdar result-stack)))
		     (destructuring-bind (goto state)
			 (gethash (first stack) (gethash (second action) table))
		       (assert (eql goto 'goto) () "Malformed parse table!")
		       (push state stack)))
	     (accept (return (car result-stack)))
	     (t (error "Parse error at ~A" token)))))

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
    (multiple-value-bind (*first-set* *follow-set* *nullable-set*)
	(compute-prediction-sets *grammar*)
      (let ((table (create-parse-table)))
	(write-parser-function table package stream fn-name)))))


;;;; Testing stuff.

(defun test-parser (grammar string)
  (let ((*grammar* (process-grammar grammar))
	(*read-eval* nil))
    (multiple-value-bind (*first-set* *follow-set* *nullable-set*)
	(compute-prediction-sets *grammar*)
      (with-input-from-string (*standard-input* string)
	(parse (create-parse-table)
	       #'(lambda () (cons (handler-case (read)
				    (end-of-file () *end-symbol*))
				  nil)))))))
