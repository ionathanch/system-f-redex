#lang racket

(require (prefix-in s. "./system-f.rkt")
         (prefix-in t. "./system-f-anf.rkt")
         (rename-in redex/reduction-semantics
                    [define-judgment-form define-judgement-form]
                    [judgment-holds       judgement-holds])
         redex/gui)

(module+ test
  (require (rename-in redex-chk
                      [redex-judgment-holds-chk redex-judgement-holds-chk])))

(define-union-language λANF s.λF t.λF-ANF)

;; [τ] ↦ τ
;; In System F, this does nothing.
(define-judgement-form λANF
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

;; [e]K ↦ e
(define-judgement-form λANF
  #:contract (↦ e K e)
  #:mode (↦ I I O)

  ;; [x]K = K[x]
  [--------------------------- "var"
   (↦ x K (t.continue (K x)))]

  ;; [(λ (x : τ) e)]K = K[(λ (x : [τ]) [e])]
  [(↦τ τ_s τ_t)
   (↦ e_s ∘ e_t)
   ----------------------------------------------------------- "fun"
   (↦ (λ (x : τ_s) e_s) K (t.continue (K (λ (x : τ_t) e_t))))]

  ;; [(e_1 e_2)] = [e_1](let [x_1 ∘] [e_2](let [x_2 ∘] K[(x_1 x_2)]))
  [(where (x_1 x_2) ,(variables-not-in (term (K e_1s e_2s)) '(y y)))
   (where e (t.continue (K (x_1 x_2))))
   (where K_2 (let [x_2 ∘] e))
   (↦ e_2s K_2 e_2t)
   (where K_1 (let [x_1 ∘] e_2t))
   (↦ e_1s K_1 e_1t)
   ----------------------- "app"
   (↦ (e_1s e_2s) K e_1t)]

  ;; [(Λ α e)]K = K[(Λ α [e])]
  [(↦ e_s ∘ e_t)
   ------------------------------------------- "polyfun"
   (↦ (Λ α e_s) K (t.continue (K (Λ α e_t))))]

  ;; [(e [τ])]K = [e](let [x ∘] K[(x [[τ]])])
  [(↦τ τ_s τ_t)
   (where x ,(variable-not-in (term (K e_s)) 'y))
   (where e (t.continue (K (x [τ_t]))))
   (where K_1 (let [x ∘] e))
   (↦ e_s K_1 e_t)
   ---------------------- "polyapp"
   (↦ (e_s [τ_s]) K e_t)]

  ;; [(let [x e_1] e_2)]K = [e_1](let [x ∘] [e_2]K)
  [(↦ e_2s K e_2t)
   (where K_1 (let [x ∘] e_2t))
   (↦ e_1s K_1 e_1t)
   ------------------------------- "let"
   (↦ (let [x e_1s] e_2s) K e_1t)])

;; Eliminate redundant bindings:
;; - (let [x_1 x_2] e) ⟶ e[x_2/x_1]
;; - (let [x c] x)     ⟶ c

(define-extended-language λANF⇓ λANF
  ;; This context causes ambiguous evaluation order!
  (G ::= hole (λ (x : τ) G) (Λ α G) (let [x G] e) (let [x c] G)))

;; Reduction of redundant bindings
(define ⟶
  (reduction-relation
   λANF
   (--> (let [x_1 x_2] e)
        (substitute e x_1 x_2)
        "ζ-bind")
   (--> (let [x c] x)
        c
        "ζ-body")))

;; Compatible closure of ⟶
(define ⟶*
  (context-closure ⟶ λANF⇓ G))

;; Reflexive, transitive closure of ⟶*
(define-metafunction λANF
  compile : e -> e
  [(compile e)
   ,(first (apply-reduction-relation* ⟶* (term e_anf) #:cache-all? #t))
   (judgement-holds (↦ e ∘ e_anf))])
