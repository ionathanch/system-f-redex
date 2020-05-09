#lang racket

(require (rename-in (prefix-in F. "./system-f-acc.rkt")
                    [F.λF-ACC λF-ACC])
         (rename-in redex/reduction-semantics
                    [define-judgment-form          define-judgement-form]
                    [define-extended-judgment-form define-extended-judgement-form]
                    [judgment-holds                judgement-holds]))

(module+ test
  (require "./redex-chk.rkt"))

(provide (all-defined-out))

;; (ANF-RESTRICTED) HOISTED SYSTEM F (with ABSTRACT CLOSURES) ;;

;; Syntax

(define-extended-language λF-H λF-ACC
  (P ::= ???) ;; A collection of programs
  (p ::= ???) ;; A program
  (v ::= x (⟨ l [σ ...] (v ...) ⟩)) ;; Values

  #:binding-forms
  ) ;; p will likely bind arguments in its body
