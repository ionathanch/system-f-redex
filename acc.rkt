#lang racket

(require (prefix-in s. "./system-f-anf.rkt")
         (prefix-in t. "./system-f-acc.rkt")
         (rename-in redex/reduction-semantics
                    [define-judgment-form          define-judgement-form]
                    [define-extended-judgment-form define-extended-judgement-form]
                    [judgment-holds                judgement-holds]))

(module+ test
  (require "./redex-chk.rkt"))

(provide compile)

;; ABSTRACT CLOSURE CONVERSION ;;

(define-union-language λACC s.λF-ANF t.λF-ACC)
(default-language λACC)

;; Unroll (λ* (a_1 ... a_n) e) into (L a_1 ... (L a_n e))
;; where (L ::= λ Λ) (a ::= [x : τ] α)
(define-metafunction/extension t.λ* λACC
  λ* : (any ...) e -> e)

;; Unroll (@ e a_1 ... a_n) into ((e a_1) ... a_n)
;; where (a ::= e [τ])
(define-metafunction/extension t.@ λACC
  @ : any ... -> e)

;; Unroll (let* ([x_1 e_1] ... [x_n e_n]) e) into (let [x_1 e_1] ... (let [x_n e_n] e))
(define-metafunction/extension t.let* λACC
  let* : ([x e] ...) e -> e)

;; Unroll (τ_1 → ... → τ_n) into (τ_1 → (... → τ_n))
(define-metafunction/extension t.→* λACC
  →* : τ ... τ -> τ)

;; Unroll (∀* (α_1 ... a_n) τ) as (∀ α_1 ... (∀ α_n τ))
(define-metafunction/extension t.∀* λACC
  ∀* : (α ...) τ -> τ)

;; (x : τ) ∈ Γ
(define-extended-judgement-form λACC t.∈Γ
  #:contract (∈Γ x τ Γ)
  #:mode (∈Γ I O I))


;; ACC Translation Judgement
;; Note that the translation is defined over the typing rules for ANF
;; because it needs to know the types of the free variables

;; [τ] ↝ τ
;; In ACC, this does nothing.
(define-judgement-form λACC
  #:contract (↝τ τ τ)
  #:mode (↝τ I O)

  [--------- "τ-var"
   (↝τ α α)]

  [(↝τ σ_s σ_t)
   (↝τ τ_s τ_t)
   --------------------------------- "τ-fun"
   (↝τ (→ σ_s τ_s) (→ σ_t τ_t))]

  [(↝τ τ_s τ_t)
   -------------------------- "τ-poly"
   (↝τ (∀ α τ_s) (∀ α τ_t))])

;; Δ Γ ⊢ v ↝ v : τ
(define-judgement-form λACC
  #:contract (⊢v Δ Γ v ↝ v τ)
  #:mode (⊢v I I I I O O)

  [(∈Γ x τ Γ)
   ------------- "var"
   (⊢v Δ Γ x ↝ x τ)]

  [(↝τ σ σ_1)
   (⊢e Δ (Γ (x : σ_1)) e_s ↝ e_t σ_2)
   (where (y ...) (free-vars (λ (x : σ) e_s)))
   (⊢v Δ Γ y ↝ y τ) ...
   (where (β_1 ...) (free-type-vars-types (τ ...)))
   (where (β_2 ...) (free-type-vars-term (λ (x : σ) e_s)))
   ------------------------------------------------------------------------------------------------------------------------- "fun"
   (⊢v Δ Γ (λ (x : σ) e_s) ↝ (⟨ (λ (β_1 ... β_2 ...) ([y : τ] ...) (x : σ_1) e_t) [β_1 ... β_2 ...] (y ...) ⟩) (→ σ_1 σ_2))]

  [(⊢e (Δ α) Γ e_s ↝ e_t σ)
   (where (y ...) (free-vars (Λ α e_s)))
   (⊢v Δ Γ y ↝ y τ) ...
   (where (β_1 ...) (free-type-vars-types (τ ...)))
   (where (β_2 ...) (free-type-vars-term (Λ α e_s)))
   ------------------------------------------------------------------------------------------------------- "polyfun"
   (⊢v Δ Γ (Λ α e_s) ↝ (⟨ (Λ (β_1 ... β_2 ...) ([y : τ] ...) α e_t) [β_1 ... β_2 ...] (y ...) ⟩) (∀ α σ))])

;; Δ Γ ⊢ c ↝ c : τ
;; Trivial transformation
(define-judgement-form λACC
  #:contract (⊢c Δ Γ c ↝ c τ)
  #:mode (⊢c I I I I O O)

  [(⊢v Δ Γ v_s ↝ v_t τ)
   ---------------------- "val"
   (⊢c Δ Γ v_s ↝ v_t τ)]

  [(⊢v Δ Γ v_2s ↝ v_2t σ)
   (⊢v Δ Γ v_1s ↝ v_1t (→ σ τ))
   -------------------------------------- "app"
   (⊢c Δ Γ (v_1s v_2s) ↝ (v_1t v_2t) τ)]

  [(↝τ σ_s σ_t)
   (⊢v Δ Γ v_s ↝ v_t (∀ α τ))
   --------------------------------------------------------- "polyapp"
   (⊢c Δ Γ (v_s [σ_s]) ↝ (v_t [σ_t]) (substitute τ α σ_t))])

;; Δ Γ ⊢ e ↝ e : τ
;; Trivial transformation
(define-judgement-form λACC
  #:contract (⊢e Δ Γ e ↝ e τ)
  #:mode (⊢e I I I I O O)

  [(⊢c Δ Γ c_s ↝ c_t τ)
   ---------------------- "comp"
   (⊢e Δ Γ c_s ↝ c_t τ)]

  [(⊢c Δ Γ c_s ↝ c_t σ)
   (⊢e Δ (Γ (x : σ)) e_s ↝ e_t τ)
   -------------------------------------------------- "let"
   (⊢e Δ Γ (let [x c_s] e_s) ↝ (let [x c_t] e_t) τ)])


;; Compilation Convenience Metafunctions

(define-metafunction λACC
  compile : e -> e
  [(compile e_s)
   e_t (judgement-holds (⊢e · · e_s ↝ e_t _))])

(define-metafunction λACC
  compile-type : τ -> τ
  [(compile-type τ_s)
   τ_t (judgement-holds (↝τ τ_s τ_t))])

(module+ test
  (define-term id
    (λ* (a [x : a]) x))

  (define-term const
    (λ* (a b [x : a] [y : b]) x))

  (define-term id-ACC
    (⟨ (Λ () () a
          (⟨ (λ (a) () (x : a) x) [a] () ⟩))
       () () ⟩))

  (define-term const-ACC
    (⟨ (Λ () () a
          (⟨ (Λ (a) () b
                (⟨ (λ (a b) () (x : a)
                     (⟨ (λ (a b) ([x : a]) (y : b) x)
                        [a b] (x) ⟩))
                   [a b] () ⟩))
             [a] () ⟩))
       [] () ⟩))

  (define-term id-compiled
    (compile id))
  (define-term const-compiled
    (compile const))

  (redex-chk
   #:eq id-compiled id-ACC
   #:eq (t.infer id-compiled) (compile-type (s.infer id))
   #;(#:eq (t.normalize id-compiled) (s.normalize id)))

  (redex-chk
   #:eq const-compiled const-ACC
   #:eq (t.infer const-compiled) (compile-type (s.infer const))
   #;(#:eq (t.normalize const-compiled) (s.normalize const))))


;; Other Metafunctions

;; The following metafunctions are neither desugaring ones
;; nor convenience evaluation ones, and are nontrivial

;; Returns free type variables in given types
(define-metafunction s.λF-ANF
  free-type-vars-types : (τ ...) -> (α ...)
  [(free-type-vars-types ()) ()]
  [(free-type-vars-types (τ τ_r ...))
   (α ... β ...)
   (where (α ...) (free-type-vars-type τ))
   (where (β ...) (free-type-vars-types (τ_r ...)))])

;; Returns free type variables in given type
(define-metafunction s.λF-ANF
  free-type-vars-type : τ -> (α ...)
  [(free-type-vars-type α) (α)]
  [(free-type-vars-type (→ σ τ))
   (α ... β ...)
   (where (α ...) (free-type-vars-type σ))
   (where (β ...) (free-type-vars-type τ))]
  [(free-type-vars-type (∀ β τ))
   (- (α ...) (β))
   (where (α ...) (free-type-vars-type τ))])

;; Returns free type variables in given term
(define-metafunction s.λF-ANF
  free-type-vars-term : any -> (α ...)
  [(free-type-vars-term x) ()]
  [(free-type-vars-term (λ (_ : τ) e))
   (α_τ ... α_e ...)
   (where (α_τ ...) (free-type-vars-type τ))
   (where (α_e ...) (free-type-vars-term e))]
  [(free-type-vars-term (Λ β e))
   (- (α ...) (β))
   (where (α ...) (free-type-vars-term e))]
  [(free-type-vars-term (v_1 v_2))
   (α_1 ... α_2 ...)
   (where (α_1 ...) (free-type-vars-term v_1))
   (where (α_2 ...) (free-type-vars-term v_2))]
  [(free-type-vars-term (v [β]))
   (β α ...)
   (where (α ...) (free-type-vars-term v))]
  [(free-type-vars-term (let (_ c) e))
   (α_c ... α_e ...)
   (where (α_c ...) (free-type-vars-term c))
   (where (α_e ...) (free-type-vars-term e))])

;; Returns free term variables in given term
(define-metafunction s.λF-ANF
  free-vars : e -> (x ...)
  [(free-vars x) (x)]
  [(free-vars (λ (y : _) e))
   (- (x ...) (y))
   (where (x ...) (free-vars e))]
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
