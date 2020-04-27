#lang racket

(require (rename-in (prefix-in F. "./system-f-anf.rkt")
                    [F.λF-ANF λF-ANF])
         (rename-in redex/reduction-semantics
                    [define-judgment-form          define-judgement-form]
                    [define-extended-judgment-form define-extended-judgement-form]
                    [judgment-holds                judgement-holds]))

(module+ test
  (require (rename-in redex-chk
                      [redex-judgment-holds-chk redex-judgement-holds-chk])))

(provide (all-defined-out))

;; CLOSURE-CONVERTED SYSTEM F ;;

;; Syntax

(define-extended-language λF-ACC λF-ANF
  (y β ::= variable-not-otherwise-mentioned) ;; More variable nonterminals
  (τ σ ::= .... ;; Types
     (vcode (α ...) (τ ...) α τ)  ;; ∀ (α ...). τ → ... → ∀ α. τ
     (tcode (α ...) (τ ...) τ τ)) ;; ∀ (α ...). τ → ... → τ → τ
  (k ::= ;; Code
     (Λ (α ...) ([x : τ] ...) α e)        ;; Λ (α ...). λ (x:τ ...). Λ α.   e
     (λ (α ...) ([x : τ] ...) (x : τ) e)) ;; Λ (α ...). λ (x:τ ...). λ x:τ. e
  (v ::= x (⟨ k [σ ...] (v ...) ⟩)) ;; Values (incl. closures)
  (F ::= E ;; Evaluation contexts (under closures)
       (⟨ F [σ ...] (v ...) ⟩)
       (Λ (α ...) ([x : τ] ...) α F)
       (λ (α ...) ([x : τ] ...) (x : τ) F))

  #:binding-forms
  (Λ (α ...)
     ([x : τ] ...) #:refers-to (shadow α ...)
     α_1 e #:refers-to (shadow α ... x ... α_1))
  #;(λ (α ...)
    ([x : τ] ...) #:refers-to (shadow α ...)
    (x_1 : τ_1) #:refers-to (shadow α ...)
    e #:refers-to (shadow α ... x ... x_1)) ;; TODO: Fix this
  (vcode
   (α ...) (τ ...) #:refers-to (shadow α ...)
   α_1 τ_1 #:refers-to (shadow α ... α_1))
  (tcode
   (α ...) (τ ...) #:refers-to (shadow α ...)
   τ_1 #:refers-to (shadow α ...)
   τ_2 #:refers-to (shadow α ...)))


;; Unroll (λ* (a_1 ... a_n) e) into (L a_1 ... (L a_n e))
;; where (L ::= λ Λ) (a ::= [x : τ] α)
(define-metafunction/extension F.λ* λF-ACC
  λ* : (any ...) e -> e)

;; Unroll (let* ([x_1 e_1] ... [x_n e_n]) e) into (let [x_1 e_1] ... (let [x_n e_n] e))
(define-metafunction/extension F.let* λF-ACC
  let* : ([x e] ...) e -> e)

;; Unroll (τ_1 → ... → τ_n) into (τ_1 → (... → τ_n))
(define-metafunction/extension F.→* λF-ACC
  →* : τ ... τ -> τ)

;; Unroll (∀* (α_1 ... a_n) τ) as (∀ α_1 ... (∀ α_n τ))
(define-metafunction/extension F.∀* λF-ACC
  ∀* : (α ...) τ -> τ)

;; Unroll ((x_1 : τ_1) ... (x_n : τ_n)) into ((· (x_1 : τ_1)) ... (x_n : τ_n))
(define-metafunction/extension F.Γ* λF-ACC
  Γ* : (x : τ) ... -> Γ)

;; Unroll (α_1 ... α_n) into ((· α_1) ... α_n)
(define-metafunction/extension F.Δ* λF-ACC
  Δ* : α ... -> Δ)

;; Unroll (Γ (x_1 : τ_1) ... (x_n : τ_n)) into ((Γ (x_1 : τ_1)) ... (x_n : τ_n))
(define-metafunction λF-ACC
  Γ+ : Γ (x : τ) ... -> Γ
  [(Γ+ Γ) Γ]
  [(Γ+ Γ (x_r : τ_r) ... (x : τ))
   ((Γ+ Γ (x_r : τ_r) ...) (x : τ))])

;; Unroll (Δ α_1 ... α_n) into ((Δ α_1) ... α_n)
(define-metafunction λF-ACC
  Δ+ : Δ α ... -> Δ
  [(Δ+ Δ) Δ]
  [(Δ+ Δ α_r ... α)
   ((Δ+ Δ α_r ...) α)])


;; Static Semantics

;; (x : τ) ∈ Γ
(define-extended-judgement-form λF-ACC F.∈Γ
  #:contract (∈Γ x τ Γ)
  #:mode (∈Γ I O I))

;; α ∈ Δ
(define-extended-judgement-form λF-ACC F.∈Δ
  #:contract (∈Δ α Δ)
  #:mode (∈Δ I I))

;; Δ ⊢ τ
(define-extended-judgement-form λF-ACC F.⊢τ
  #:contract (⊢τ Δ τ)
  #:mode (⊢τ I I)

  [(where Δ_0 (Δ+ Δ α ...))
   (⊢τ Δ_0 τ) ...
   (⊢τ (Δ_0 β) σ)
   ----------------------------------- "τ-vcode"
   (⊢τ Δ (vcode (α ...) (τ ...) β σ))]

  [(where Δ_0 (Δ+ Δ α ...))
   (⊢τ Δ_0 τ) ...
   (⊢τ Δ_0 σ_1)
   (⊢τ Δ_0 σ_2)
   --------------------------------------- "τ-tcode"
   (⊢τ Δ (tcode (α ...) (τ ...) σ_1 σ_2))])

;; Δ Γ ⊢ k : τ
(define-judgement-form λF-ACC
  #:contract (⊢k Δ Γ k τ)
  #:mode (⊢k I I I O)

  [(where Δ_0 (Δ+ Δ α ...))
   (⊢τ Δ_0 τ) ...
   (⊢e (Δ_0 β) (Γ+ Γ (x : τ) ...) e σ)
   ------------------------------------------------------------------- "vcode"
   (⊢k Δ Γ (Λ (α ...) ([x : τ] ...) β e) (vcode (α ...) (τ ...) β σ))]

  [(where Δ_0 (Δ+ Δ α ...))
   (⊢τ Δ_0 τ) ...
   (⊢e Δ_0 (Γ+ Γ (x : τ) ... (y : σ_1)) e σ_2)
   ------------------------------------------------------------------------------- "tcode"
   (⊢k Δ Γ (λ (α ...) ([x : τ] ...) (y : σ_1) e) (tcode (α ...) (τ ...) σ_1 σ_2))])

;; Δ Γ ⊢ v : τ
(define-extended-judgement-form λF-ACC F.⊢v
  #:contract (⊢v Δ Γ v τ)
  #:mode (⊢v I I I O)

  [(⊢k Δ Γ k (vcode (α ..._1) (τ ..._2) β σ_1))
   (⊢τ Δ σ) ...
   (where Δ_0 (Δ+ Δ α ...))
   (⊢v Δ_0 Γ v τ) ...
   ----------------------------------------------- "fun"
   (⊢v Δ Γ (⟨ k [σ ..._1] (v ..._2) ⟩) (∀ β σ_1))]

  [(⊢k Δ Γ k (tcode (α ..._1) (τ ..._2) σ_1 σ_2))
   (⊢τ Δ σ) ...
   (where Δ_0 (Δ+ Δ α ...))
   (⊢v Δ_0 Γ v τ) ...
   ------------------------------------------------ "polyfun"
   (⊢v Δ Γ (⟨ k [σ ..._1] (v ..._2) ⟩) (→ σ_1 σ_2))])

;; Δ Γ ⊢ c : τ
(define-extended-judgement-form λF-ACC F.⊢c
  #:contract (⊢c Δ Γ c τ)
  #:mode (⊢c I I I O))

;; Δ Γ ⊢ e : τ
(define-extended-judgement-form λF-ACC F.⊢e
  #:contract (⊢e Δ Γ e τ)
  #:mode (⊢e I I I O))


;; Dynamic Semantics

(define ⟶
  (extend-reduction-relation
   F.⟶ λF-ACC
   (--> ((⟨ (Λ (α ...) ([x : _] ...) β e) [σ ...] (v ...) ⟩) σ_1)
        () ;; TODO: e[σ/α]...[v/x]...[σ_1/β]
        "β")
   (--> ((⟨ (λ (α ...) ([x : _] ...) (y : _) e) [σ ...] (v ...) ⟩) v_1)
        () ;; TODO: e[σ/α]...[v/x][v_1/y]
        "τ")))

(define ⟶*
  (context-closure ⟶ λF-ACC E))

(define-metafunction λF-ACC
  reduce : e -> v
  [(reduce e)
   ,(first (apply-reduction-relation* ⟶* (term e) #:cache-all? #t))])

(define ⇓
  (context-closure ⟶ λF-ACC F))

(define-metafunction λF-ACC
  normalize : e -> v
  [(normalize e)
   ,(first (apply-reduction-relation* ⇓ (term e) #:cache-all? #t))])