;; -*- Lisp -*-

(defpackage #:lalr-pargen-system (:use #:cl #:asdf))
(in-package #:lalr-pargen-system)

(defsystem lalr-parser-generator
  :depends-on (:anaphora)
  :components
  ((:file "package")
   (:file "macros")
   (:file "prediction")
   (:file "parser"))
  :serial t)

(defsystem lalr-parser-generator-test
  :depends-on (:lalr-parser-generator :rt))
