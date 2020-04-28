#lang racket

(require (rename-in redex/reduction-semantics
                    [judgment-holds                judgement-holds])
         (only-in rackunit check-true)
         (rename-in redex-chk
                    [redex-judgment-holds-chk redex-judgement-holds-chk]))

(provide (combine-out (all-defined-out)
                      (all-from-out redex-chk)))

;; (redex-judgement-equals-chk (judgement-form-id pat/term ...) [pat/term ... #:pat pattern #:term term] ...)
;; This calls (judgement-holds (judgement-form-id pat/term ...) pattern) for each branch
;; and checks whether any term bound to the pattern is equivalent to the provided term
;; using default-equiv to compare terms. For example,
#;(redex-let
   L
   ([num-type  num]
    [bool-type bool])
   (redex-judgement-equals-chk
    (types ·)
    [0    t #:pat t #:term num-type]
    [true t #:pat t #:term bool-type]))
;; will check whether num-type  is equivalent to any of (judgement-holds (types · 0    t) t)
;; and  also  whether bool-type is equivalent to any of (judgement-holds (types · true t) t).

(define-syntax-rule (redex-judgement-equals-chk
                     (name dargs ...)
                     [args ... #:pat pat #:term trm] ...)
  (begin
    (check-true
     (ormap (curry (default-equiv) (term trm))
            (judgement-holds (name dargs ... args ...) pat))) ...))