;; -*- Lisp -*-

(defpackage #:lalr-pargen-system (:use #:cl #:asdf))
(in-package #:lalr-pargen-system)

(defsystem lalr-parser-generator
  :depends-on (:anaphora)
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
  ((:file "tests.lisp")))
