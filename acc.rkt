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
   ;; TODO: FTVs, FVs
   ------------------------------- "fun"
   (⊢v Δ Γ (λ (x : σ) e_s) ↦ (⟨ (λ () () (x : σ_1) e_t) () () ⟩) (→ σ_1 σ_2))]

  [(⊢e (Δ α) Γ e_s ↦ e_t σ)
   ;; TODO: FTVs, FVs
   ---------------------------------------------------------- "polyfun"
   (⊢v Δ Γ (Λ α e_s) ↦ (⟨ (Λ () () α e_t) () () ⟩) (∀ α σ))])

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
