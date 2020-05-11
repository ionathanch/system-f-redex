#lang racket

(require (prefix-in s. "./system-f-acc.rkt")
         (prefix-in t. "./system-f-h.rkt")
         (rename-in redex/reduction-semantics
                    [define-judgment-form define-judgement-form]
                    [judgment-holds       judgement-holds]))

(module+ test
  (require "./redex-chk.rkt"))

(provide compile)

;; HOISTING ;;

(define-union-language λH s.λF-ACC t.λF-H)
(default-language λH)

;; Unroll (λ* (a_1 ... a_n) e) into (L a_1 ... (L a_n e))
;; where (L ::= λ Λ) (a ::= [x : τ] α)
(define-metafunction/extension t.λ* λH
  λ* : (any ...) e -> e)

;; Unroll (@ e a_1 ... a_n) into ((e a_1) ... a_n)
;; where (a ::= e [τ])
(define-metafunction/extension t.@ λH
  @ : any ... -> e)

;; Unroll (let* ([x_1 e_1] ... [x_n e_n]) e) into (let [x_1 e_1] ... (let [x_n e_n] e))
(define-metafunction/extension t.let* λH
  let* : ([x e] ...) e -> e)

;; Unroll (τ_1 → ... → τ_n) into (τ_1 → (... → τ_n))
(define-metafunction/extension t.→* λH
  →* : τ ... τ -> τ)

;; Unroll (∀* (α_1 ... a_n) τ) as (∀ α_1 ... (∀ α_n τ))
(define-metafunction/extension t.∀* λH
  ∀* : (α ...) τ -> τ)

;; [τ] ↝ τ
;; During hoisting, this does nothing.
(define-judgement-form λH
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

;; [k] ↝ Φ l
(define-judgement-form λH
  #:contract (↝k k Φ l)
  #:mode (↝k I O O)

  [(where l ,(variable-not-in (term (Λ (α ...) ([x : τ] ...) β e)) 'l))
   (↝e e_s (p_e ...) e_t)
   (where p (l ↦ (α ...) ([x : τ] ...) (β : *) e_t))
   -------------------------------------------------- "tcode"
   (↝k (Λ (α ...) ([x : τ] ...) β e_s) (p_e ... p) l)]

  [(where l ,(variable-not-in (term (λ (α ...) ([x : τ] ...) (y : σ) e)) 'l))
   (↝e e_s (p_e ...) e_t)
   (where p (l ↦ (α ...) ([x : τ] ...) (y : σ) e_t))
   -------------------------------------------------------- "vcode"
   (↝k (λ (α ...) ([x : τ] ...) (y : σ) e_s) (p_e ... p) l)])

;; [v] ↝ Φ v
(define-judgement-form λH
  #:contract (↝v v Φ v)
  #:mode (↝v I O O)

  [------------- "var"
   (↝v x () x)]

  [(↝k k Φ l)
   ;; do we need to translate σ ... and v ... ???
   -------------------------------------------------------- "(poly)fun"
   (↝v (⟨ k [σ ...] (v ...) ⟩) Φ (⟨ l [σ ...] (v ...) ⟩))])

;; [c] ↝ Φ c
(define-judgement-form λH
  #:contract (↝c c Φ c)
  #:mode (↝c I O O)

  [(↝v v_s Φ v_t)
   --------------- "val"
   (↝c v_s Φ v_t)]

  [(↝v v_1s (p_1 ...) v_1t)
   (↝v v_2s (p_2 ...) v_2t)
   ------------------------------------------------ "app"
   (↝c (v_1s v_2s) (p_1 ... p_2 ...) (v_1t v_2t))]

  [(↝τ σ_s σ_t)
   (↝v v_s Φ v_t)
   -------------------------------- "polyapp"
   (↝c (v_s [σ_s]) Φ (v_t [σ_t]))])

;; [e] ↝ Φ e
(define-judgement-form λH
  #:contract (↝e e Φ e)
  #:mode (↝e I O O)

  [(↝c c_s Φ c_t)
   ---------------- "comp"
   (↝e c_s Φ c_t)]

  [(↝c c_s (p_c ...) c_t)
   (↝e e_s (p_e ...) e_t)
   ------------------------------------------------------------ "let"
   (↝e (let [x c_s] e_s) (p_c ... p_e ...) (let [x c_t] e_t))])


;; Compilation Convenience Metafunctions

(define-metafunction λH
  compile : e -> P
  [(compile e_s)
   (let Φ e_t)
   (judgement-holds (↝e e_s Φ e_t))])

(define-metafunction λH
  compile-type : τ -> τ
  [(compile-type τ_s)
   τ_t (judgement-holds (↝τ τ_s τ_t))])