#lang racket

(require (prefix-in s. "./system-f-anf.rkt")
         (prefix-in t. "./system-f-acc.rkt")
         (rename-in redex/reduction-semantics
                    [define-judgment-form          define-judgement-form]
                    [define-extended-judgment-form define-extended-judgement-form]
                    [judgment-holds                judgement-holds]))

(module+ test
  (require "./redex-chk.rkt"))

(define-union-language λACC s.λF-ANF t.λF-ACC)

;; (x : τ) ∈ Γ
(define-extended-judgement-form λACC t.∈Γ
  #:contract (∈Γ x τ Γ)
  #:mode (∈Γ I O I))

;; [τ] ↦ τ
;; In ACC, this does nothing.
(define-judgement-form λACC
  #:contract (↦τ τ τ)
  #:mode (↦τ I O)

  [--------- "τ-var"
   (↦τ α α)]

  [(↦τ σ_s σ_t)
   (↦τ τ_s τ_t)
   --------------------------------- "τ-fun"
   (↦τ (→ σ_s τ_s) (→ σ_t τ_t))]

  [(↦τ τ_s τ_t)
   -------------------------- "τ-poly"
   (↦τ (∀ α τ_s) (∀ α τ_t))])

;; Δ Γ ⊢ v ↦ v : τ
(define-judgement-form λACC
  #:contract (⊢v Δ Γ v ↦ v τ)
  #:mode (⊢v I I I I O O)

  [(∈Γ x τ Γ)
   ------------- "var"
   (⊢v Δ Γ x ↦ x τ)]

  [(↦τ σ σ_1)
   (⊢e Δ (Γ (x : σ_1)) e_s ↦ e_t σ_2)
   (where (β ...) (free-type-vars (λ (x : σ) e_s)))
   (where (y ...) (free-vars (λ (x : σ) e_s)))
   ----------------------------------------------------------------------------------------------- "fun"
   (⊢v Δ Γ (λ (x : σ) e_s) ↦ (⟨ (λ (β ...) (y ...) (x : σ_1) e_t) (β ...) (y ...) ⟩) (→ σ_1 σ_2))]

  [(⊢e (Δ α) Γ e_s ↦ e_t σ)
   (where (β ...) (free-type-vars (Λ α e_s)))
   (where (y ...) (free-vars (Λ α e_s)))
   ----------------------------------------------------------------------------- "polyfun"
   (⊢v Δ Γ (Λ α e_s) ↦ (⟨ (Λ (β ...) (y ...) α e_t) (β ...) (y ...) ⟩) (∀ α σ))])

;; Δ Γ ⊢ c ↦ c : τ
;; Trivial transformation
(define-judgement-form λACC
  #:contract (⊢c Δ Γ c ↦ c τ)
  #:mode (⊢c I I I I O O)

  [(⊢v Δ Γ v_s ↦ v_t τ)
   ---------------------- "val"
   (⊢c Δ Γ v_s ↦ v_t τ)]

  [(⊢v Δ Γ v_2s ↦ v_2t σ)
   (⊢v Δ Γ v_1s ↦ v_1t (→ σ τ))
   -------------------------------------- "app"
   (⊢c Δ Γ (v_1s v_2s) ↦ (v_1t v_2t) τ)]

  [(↦τ σ_s σ_t)
   (⊢v Δ Γ v_s ↦ v_t (∀ α τ))
   --------------------------------------------------------- "polyapp"
   (⊢c Δ Γ (v_s [σ_s]) ↦ (v_t [σ_t]) (substitute τ α σ_t))])

;; Δ Γ ⊢ e ↦ e : τ
;; Trivial transformation
(define-judgement-form λACC
  #:contract (⊢e Δ Γ e ↦ e τ)
  #:mode (⊢e I I I I O O)

  [(⊢c Δ Γ c_s ↦ c_t τ)
   ---------------------- "comp"
   (⊢e Δ Γ c_s ↦ c_t τ)]

  [(⊢c Δ Γ c_s ↦ c_t σ)
   (⊢e Δ (Γ (x : σ)) e_s ↦ e_t τ)
   -------------------------------------------------- "let"
   (⊢e Δ Γ (let [x c_s] e_s) ↦ (let [x c_t] e_t) τ)])

(define-metafunction λACC
  compile : e -> e
  [(compile e_s)
   e_t (judgement-holds (⊢e · · e_s ↦ e_t _))])


;; Metafunctions

;; The following metafunctions are neither desugaring ones
;; nor convenience evaluation ones, and are nontrivial

;; Returns free type variables in given type or term
(define-metafunction s.λF-ANF
  free-type-vars : any -> (α ...)
  [(free-type-vars α) (α)]
  [(free-type-vars (→ σ τ))
   (α ... β ...)
   (where (α ...) (free-type-vars σ))
   (where (β ...) (free-type-vars τ))]
  [(free-type-vars (∀ β τ))
   (- (α ...) (β))
   (where (α ...) (free-type-vars τ))]
  [(free-type-vars x) ()]
  [(free-type-vars (λ (_ : _) e))
   (α_τ ... α_e ...)
   (where (α_τ ...) (free-type-vars τ))
   (where (α_e ...) (free-type-vars e))]
  [(free-type-vars (Λ β e))
   (- (α ...) (β))
   (where (α ...) (free-type-vars e))]
  [(free-type-vars (v_1 v_2))
   (α_1 ... α_2 ...)
   (where (α_1 ...) (free-type-vars v_1))
   (where (α_2 ...) (free-type-vars v_2))]
  [(free-type-vars (v [β]))
   (β α ...)
   (where (α ...) (free-type-vars v))]
  [(free-type-vars (let (_ c) e))
   (α_c ... α_e ...)
   (where (α_c ...) (free-type-vars c))
   (where (α_e ...) (free-type-vars e))])

;; Returns free term variables in given term
(define-metafunction s.λF-ANF
  free-vars : e -> (x ...)
  [(free-vars x) (x)]
  [(free-vars (λ (y : _) e))
   (- (x ...) (y))
   (where (x ...) (free-type-vars e))]
  [(free-vars (Λ _ e))
   (free-vars e)]
  [(free-vars (v_1 v_2))
   (x_1 ... x_2 ...)
   (where (x_1 ...) (free-vars v_1))
   (where (x_2 ...) (free-vars v_2))]
  [(free-vars (v [_]))
   (free-vars v)]
  [(free-vars (let (y c) e))
   (x_c ... x_e ...)
   (where (x_c ...) (free-vars c))
   (where (x_ey ...) (free-vars e))
   (where (x_e ...) (- (x_ey ...) (y)))])

;; Removes the variables in the second list from the first list
;; Literally copied directly from the Redex docs
;; https://docs.racket-lang.org/redex/The_Redex_Reference.html#%28form._%28%28lib._redex%2Freduction-semantics..rkt%29._define-metafunction%29%29
(define-metafunction s.λF-ANF
  - : (x ...) (x ...) -> (x ...)
  [(- (x ...) ()) (x ...)]
  [(- (x_1 ... x_2 x_3 ...) (x_2 x_4 ...))
   (- (x_1 ... x_3 ...) (x_2 x_4 ...))
   (side-condition (not (memq (term x_2) (term (x_3 ...)))))]
  [(- (x_1 ...) (x_2 x_3 ...))
   (- (x_1 ...) (x_3 ...))])
