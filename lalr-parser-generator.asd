;; -*- Lisp -*-

(defpackage #:lalr-pargen-system (:use #:cl #:asdf))
(in-package #:lalr-pargen-system)

(defsystem lalr-parser-generator
  :depends-on (:anaphora)
  :author "Julian Squires <julian@cipht.net>"
  :version "alpha zero"
  :components
  ((:file "package")
   (:file "macros")
   (:file "prediction")
   (:file "parser"))
  :serial t)

(defsystem lalr-parser-generator-tests
  :depends-on (:lalr-parser-generator :rt)
  :components
  ((:file "tests")))

(defmethod perform ((o test-op) (c (eql (find-system :lalr-parser-generator))))
  (operate 'load-op :lalr-parser-generator-tests)
  (operate 'test-op :lalr-parser-generator-tests :force t))

(defmethod perform ((o test-op) (c (eql (find-system :lalr-parser-generator-tests))))
  (let ((*package* (find-package "LALR-PARSER-GENERATOR-TESTS")))
    (or (funcall (intern "DO-TESTS" :rt))
	(error "test-op failed"))))
