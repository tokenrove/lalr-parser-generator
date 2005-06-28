;; -*- Lisp -*-

(defpackage #:lalr-pargen-system (:use #:cl #:asdf))
(in-package #:lalr-pargen-system)

(defsystem lalr-parser-generator
  :depends-on (:anaphora)
  :components
  ((:file "package")
   (:file "macros" :depends-on ("package"))
   (:file "parser" :depends-on ("package" "macros"))))

(defsystem lalr-parser-generator-test
  :depends-on (:lalr-parser-generator :rt))
