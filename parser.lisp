;;; LALR parser generator.
;;; Julian Squires / 2005
;;;
;;; Currently SLR, will be LALR after rewrite.

;;; notes for rewrite:
;;;
;;; When we preprocess the grammar, give every symbol a unique
;;; integer, and then use bitvectors for all set operations.  Keep a
;;; bitvector to track terminal/nonterminal-ness.
;;;
;;; Add a suite of tests using RT.
;;;
;;; write parse tables and functions to a file, so projects don't need
;;; to even depend on this package to use their parser.

(in-package :lalr-parser-generator)

;;;; Special variables.

(defparameter +start-symbol+ 'start)
(defparameter +end-symbol+ '$)

(defvar *grammar* nil
  "The default grammar used by the LALR parser generator; set by
PROCESS-GRAMMAR.")
(defvar *states* nil
  "A list of states seen by the parser generator.  Constructed in
COMPUTE-SHIFTS, used in COMPUTE-REDUCTIONS.")
(defvar *first-set* nil)
(defvar *follow-set* nil)
(defvar *nullable-set* nil)


;;;; LALR ITEMS
;;; We could use a structure instead of a list here, and it would
;;; probably be much more efficient.  For the moment, it doesn't
;;; matter.

(defun make-item (lhs rhs dot lookahead)
  (list lhs rhs dot lookahead))

(defun item-lhs (item) (first item))
(defun item-rhs (item) (second item))
(defun item-dot (item) (third item))
(defun item-la (item) (fourth item))

(defun dot-at-end-p (item)
  (endp (item-dot item)))

(defun symbol-at-dot (item)
  (car (item-dot item)))

(defun advance-dot (item)
  "Returns the item dot, advanced by one symbol.  Note:
non-destructive."
  (cdr (item-dot item)))


;;; item sets -- see also macros.lisp.

(defun make-item-set (&rest items)
  (let ((set (make-array '(0) :adjustable t :fill-pointer 0)))
    (dolist (i items)
      (add-to-set i set))
    set))

(defun add-to-set (item set)
  "Returns position of ITEM in SET."
  (or (position item set :test #'equalp)
      (vector-push-extend item set)))


;;;; GRAMMAR

(defun process-grammar (grammar)
  "Processes GRAMMAR, sets *GRAMMAR*.  Augments the grammar with a new
start rule."
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
    (dolist (i (list +start-symbol+ +end-symbol+))
      (assert (null (gethash i grammar-hash)) nil
	      "~A is a reserved non-terminal, unfortunately.  Try
calling MAKE-PARSER with a different END-SYMBOL or START-SYMBOL
specified."  i))
    (setf (gethash +start-symbol+ grammar-hash)
	  (list (list (car grammar) +end-symbol+)))
    (setf *grammar* grammar-hash)))

(defun non-terminal-p (symbol) (gethash symbol *grammar*))
(defun grammar-productions (symbol) (gethash symbol *grammar*))


;;;; FIRST and FOLLOW

(defun compute-prediction-sets ()
  "Computes the first, follow, and nullable sets for *GRAMMAR*.
Sets *FIRST-SET*, *FOLLOW-SET*, and *NULLABLE-SET*."
  (let ((nullable (make-hash-table))
	(follow (make-hash-table))
	(first (make-hash-table)))
    (flet ((nullable-p (x) (gethash x nullable)))
      (do-for-each-terminal (z *grammar*)
	(setf (gethash z first) (list z)))

      (do-until-unchanged (first follow nullable)
	(do-for-each-production (x ys *grammar*)
	  (when (every #'nullable-p ys)
	    (setf (gethash x nullable) t))

	  (do ((i 0 (1+ i))
	       (k (length ys)))
	      ((>= i k))

	    (when (every #'nullable-p (and (> i 0) (subseq ys 0 (1- i))))
	      (setf (gethash x first)
		    (union (gethash x first)
			   (gethash (nth i ys) first))))

	    (when (every #'nullable-p (and (< i k) (subseq ys (1+ i) k)))
	      (setf (gethash (nth i ys) follow)
		    (union (gethash (nth i ys) follow)
			   (gethash x follow))))

	    (loop for j from (1+ i) to k
		  when (every #'nullable-p (and (> j (1+ i))
						(subseq ys (1+ i) (1- j))))
		  do (setf (gethash (nth i ys) follow)
			   (union (gethash (nth i ys) follow)
				  (gethash (nth j ys) first)))))))

      (setf *first-set* first *follow-set* follow *nullable-set* nullable)
      (values first follow nullable))))

(defun first-sets (symbol-list)
  (do* ((x-> symbol-list (cdr x->))
	(s (and x-> (gethash (car x->) *first-set*))
	   (union s (and x-> (gethash (car x->) *first-set*)))))
       ((or (null x->) (not (gethash (car x->) *nullable-set*)))
	s)))

;;; The following three functions are just for testing.  Combined,
;;; they perform the same functions as COMPUTE-PREDICTION-SETS

(defun list-nullable ()
  (let ((nullable nil))
    (do-until-unchanged (nullable)
      (do-for-each-production (lhs rhs *grammar*)
	(when (or (null rhs)
		  (every #'(lambda (x) (member x nullable)) rhs))
	  (pushnew lhs nullable))))
    nullable))

(defun list-first-set (nullable)
  (let ((first-set (make-hash-table)))
    (do-for-each-terminal (x *grammar*)
      (setf (gethash x first-set) (list x)))
    (do-until-unchanged (first-set)
      (do-for-each-production (lhs rhs *grammar*)
	(do ((r-> rhs (cdr r->))
	     (done-p nil))
	    ((or done-p (null r->)))
	  (when (not (member (car r->) nullable)) 
	    (setf (gethash lhs first-set)
		  (union (gethash lhs first-set)
			 (gethash (car r->) first-set)))
	    (setf done-p t)))))
    first-set))

(defun list-follow-set (nullable first-set)
  (let ((follow-set (make-hash-table)))
    (do-until-unchanged (follow-set)
      (do-for-each-production (lhs rhs *grammar*)
	(do ((r-> rhs (cdr r->))
	     (done-p nil))
	    ((or done-p (null r->)))
	  (when (every (lambda (x) (member x nullable)) (cdr r->))
	    (setf (gethash (car r->) follow-set)
		  (union (gethash (car r->) follow-set)
			 (gethash lhs follow-set))))

	  (loop for j from 1 to (length r->)
		do (progn
		     (when (every (lambda (x) (member x nullable))
				  (and (> j 1) (subseq r-> 1 (1- j))))
		       (setf (gethash (car r->) follow-set)
			     (union (gethash (car r->) follow-set)
				    (gethash (nth j r->) first-set)))))))))
    follow-set))



;;;; PARSE TABLE CONSTRUCTION

(defun lalr-closure (item-set)
  "Returns the closure of ITEM-SET."
  (do-until-unchanged (item-set)
    (do-for-each-item (i item-set)
      (when (non-terminal-p (symbol-at-dot i))
	(dolist (r (grammar-productions (symbol-at-dot i)))
	  (dolist (w (first-sets (append (advance-dot i)
					 (list (item-la i)))))
	    (add-to-set (make-item (symbol-at-dot i) r r w) item-set))))))
  item-set)

(defun lalr-goto (item-set grammar-symbol)
  "Returns the closure of ITEM-SET after having read GRAMMAR-SYMBOL."
  (let ((j (make-item-set)))
    (do-for-each-item (i item-set)
      (when (eql (symbol-at-dot i) grammar-symbol)
	(add-to-set (make-item (item-lhs i) (item-rhs i) (advance-dot i)
			       (item-la i))
		    j)))
    (lalr-closure j)))

(defun make-start-item ()
  "Makes the item S' -> .S$, as appropriate for the grammar."
  (make-item +start-symbol+
	     (first (gethash +start-symbol+ *grammar*))
	     (first (gethash +start-symbol+ *grammar*))
	     nil))

(defun make-almost-done-item ()
  "Makes the item S' -> S.$, as appropriate for the grammar."
  (let* ((start-item (make-start-item))
	 (dot (do ((dot (advance-dot start-item) (cdr dot)))
		  ((or (null dot) (eql (car dot) +end-symbol+)) dot))))
    (assert (not (null dot)))
    (make-item (item-lhs start-item) (item-rhs start-item) dot
	       nil)))

;;; The code gets progressively uglier as I refine the data
;;; structures.  Shame on me.

#+nil
(defun item-set-equal (set-a set-b)
  (do ((a set-a (cdr a))
       (b set-b (cdr b)))
      ((and (endp a) (endp b)) t)
    (unless (and (equal (item-lhs (car a)) (item-lhs (car b)))
		 (equal (item-rhs (car a)) (item-rhs (car b)))
		 (equal (item-dot (car a)) (item-dot (car b))))
      (return nil))))

(defun item-set-equal (set-a set-b)
  (block body
    (when (= (length set-a) (length set-b))
      (dotimes (i (length set-a))
	(unless (and (equal (item-lhs (aref set-a i))
			    (item-lhs (aref set-b i)))
		     (equal (item-rhs (aref set-a i))
			    (item-rhs (aref set-b i)))
		     (equal (item-dot (aref set-a i))
			    (item-dot (aref set-b i))))
	  (return-from body nil)))
      t)))

(defun add-to-states (set states)
  (block body
    (dotimes (i (length states))
      (when (item-set-equal set (aref states i))
	(return-from body i)))
    (vector-push-extend set states)))

(defun compute-shifts ()
  "Compute shift actions for the generated parser.  Fills the *STATE*
variable and returns a list of shift actions."
  (setf *states* (make-array '(1) :adjustable t :fill-pointer 1
			     :initial-element
			     (lalr-closure (make-item-set (make-start-item)))))

  (let ((shift-table nil))
    (do-until-unchanged (*states* shift-table)
      (dotimes (i (length *states*))
	(do-for-each-item (item (aref *states* i))
	  (when (and (not (dot-at-end-p item))
		     (not (eql (symbol-at-dot item) +end-symbol+)))
	    (let* ((x (symbol-at-dot item))
		   (new-set (lalr-goto (aref *states* i) x))
		   (j (add-to-states new-set *states*)))
	      (pushnew (list i x j) shift-table :test #'equalp))))))
    shift-table))


(defun compute-reductions ()
  "Compute reduce actions for the generated parser.  Depends on
*STATE* already being filled, and returns the reduce actions."
  (let ((reduce-table nil))
    (do-for-each-item (item-set *states*)
      (do-for-each-item (item item-set)
	(when (dot-at-end-p item)
	  (pushnew (list (position item-set *states* :test #'equalp)
			 (item-la item) item)
		   reduce-table :test #'equalp))))
    reduce-table))


(defun add-accept-actions (parse-table)
  (do* ((i 0 (1+ i))
	(item (make-almost-done-item)))
       ((>= i (length *states*)))
    (when (find item (aref *states* i) :test #'equalp)
      (add-to-parse-table parse-table i +end-symbol+ (list 'accept)))))


(defun add-to-parse-table (parse-table i x action)
  "Adds ACTION to the parse table at (X,I).  Applies braindead
conflict resolution rule to any conflicts detected."
  (anaphora:sunless (gethash x parse-table)
    (setf anaphora:it (make-array (list (length *states*))
				  :initial-element nil)))
  (aif (aref (gethash x parse-table) i)
       ;; XXX should probably collate the number of conflicts somewhere.
       (warn "~&Conflict at ~A,~A -> last action ~A, new action ~A."
	     x i it action)
  ;;   (assert (null (aref (gethash x parse-table) i)))
       (setf (aref (gethash x parse-table) i) action)))


(defun create-parse-table (shifts reductions)
  "Constructs a parse table usable by PARSE, from the list of shift
and reduce actions supplied as arguments, and from the set of states
stored in *STATES*, which COMPUTE-SHIFTS fills in."
  (let ((parse-table (make-hash-table)))
    (dolist (shift shifts)
      (destructuring-bind (i x j) shift
	(add-to-parse-table parse-table i x
			    (list (if (non-terminal-p x) 'goto 'shift) j))))

    (dolist (reduce reductions)
      (destructuring-bind (i x j) reduce
	(add-to-parse-table parse-table i x
			    (list 'reduce (list (item-lhs j)
						(length (item-rhs j)))))))
    (add-accept-actions parse-table)

    parse-table))


(defun parse (table next-token)
  "TABLE is a table generated by CREATE-PARSE-TABLE, NEXT-TOKEN is a
function which returns a cons of the next token in the input (the CAR
being the symbol name, the CDR being any information the lexer would
like to preserve), and advances the input one token.  Returns what
might pass for a parse tree in some countries."
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
	 (destructuring-bind (lhs rhs-len) (second action)
	   (push (list lhs) result-stack)
	   (dotimes (i rhs-len) 
	     (pop stack)
	     (push (pop (cdr result-stack)) (cdar result-stack)))
	   (destructuring-bind (goto state)
	       (aref (gethash lhs table) (first stack))
	     (assert (eql goto 'goto) (state) "Malformed parse table!")
	     (push state stack))))
	(accept (return (car result-stack)))
	(t (error "Parse error at ~A" token))))))


;;;; External functions

(defun make-parser (grammar &key end-symbol start-symbol)
  (awhen end-symbol (setf +end-symbol+ it))
  (awhen start-symbol (setf +start-symbol+ it))
  (process-grammar grammar)
  (compute-prediction-sets)
  (let ((table (create-parse-table (compute-shifts) (compute-reductions))))
    (lambda (&key (next-token (lambda () (list (read)))))
      (parse table next-token))))


;;;; Testing stuff.

(defun test-parser (grammar string)
  (process-grammar grammar)
  (compute-prediction-sets)
  (with-input-from-string (*standard-input* string)
    (parse (create-parse-table (compute-shifts) (compute-reductions))
	   (lambda () (cons (read) nil)))))

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
