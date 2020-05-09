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
  (l ::= variable-not-otherwise-mentioned) ;; Labels
  (τ σ ::= .... *) ;; Types with kinds
  (P ::= (let (p ...) e)) ;; A collection of programs
  (p ::= [l ↦ (α ...) ([x : τ] ...) (y : σ) e]) ;; Programs
  (v ::= x (⟨ l [σ ...] (v ...) ⟩)) ;; Values

  #:binding-forms
  [l ↦
     (α ...) b #:refers-to (shadow α ...)
     (x : τ)   #:refers-to (shadow α ...)
     e_body    #:refers-to (shadow α ... b x)] #:exports l
  (let (p #:...bind (clauses p (shadow clauses p)))
    e #:refers-to clauses))

(default-language λF-H)

(module+ test
  ;; We now use the same syntax for type and term abstractions
  ;; with types having kind * for uniformity
  (redex-chk
   #:lang λF-H
   #:m P (let ([id-a ↦ (a) () (x : a) x]
               [id   ↦ ()  () (a : *) (id-a [a])])
           (let (id-idtype (id [(∀ a (→ a a))]))
             (id-idtype id))))

  ;; Check that the bindings are working correctly
  ;; The following should therefore be alpha-equivalent
  (redex-chk
   #:eq
   (let ([f ↦ () () (u : a) u] [g ↦ () () (v : b) (f v)]) (let (w (g c)) (f w)))
   (let ([j ↦ () () (x : a) x] [k ↦ () () (y : b) (j y)]) (let (z (k c)) (j z)))))

;; Unroll (λ* (a_1 ... a_n) e) into (L a_1 ... (L a_n e))
;; where (L ::= λ Λ) (a ::= [x : τ] α)
(define-metafunction/extension F.λ* λF-H
  λ* : (any ...) e -> e)

;; Unroll (@ e a_1 ... a_n) into ((e a_1) ... a_n)
;; where (a ::= e [τ])
;; The output technically isn't valid ANF but it's useful to have
(define-metafunction/extension F.@ λF-H
  @ : any ... -> any)

;; Unroll (let* ([x_1 e_1] ... [x_n e_n]) e) into (let [x_1 e_1] ... (let [x_n e_n] e))
(define-metafunction/extension F.let* λF-ACC
  let* : ([x e] ...) e -> e)

;; Unroll (τ_1 → ... → τ_n) into (τ_1 → (... → τ_n))
(define-metafunction/extension F.→* λF-H
  →* : τ ... τ -> τ)

;; Unroll (∀* (α_1 ... a_n) τ) as (∀ α_1 ... (∀ α_n τ))
(define-metafunction/extension F.∀* λF-H
  ∀* : (α ...) τ -> τ)

;; Unroll ((x_1 : τ_1) ... (x_n : τ_n)) into ((· (x_1 : τ_1)) ... (x_n : τ_n))
(define-metafunction/extension F.Γ* λF-H
  Γ* : (x : τ) ... -> Γ)

;; Unroll (α_1 ... α_n) into ((· α_1) ... α_n)
(define-metafunction/extension F.Δ* λF-H
  Δ* : α ... -> Δ)

;; Unroll (Γ (x_1 : τ_1) ... (x_n : τ_n)) into ((Γ (x_1 : τ_1)) ... (x_n : τ_n))
(define-metafunction/extension F.Γ+ λF-H
  Γ+ : Γ (x : τ) ... -> Γ)

;; Unroll (Δ α_1 ... α_n) into ((Δ α_1) ... α_n)
(define-metafunction/extension F.Δ+ λF-H
  Δ+ : Δ α ... -> Δ)


;; Static Semantics
