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


;; Static Semantics

;; (x : τ) ∈ Γ
(define-extended-judgement-form λF-H F.∈Γ
  #:contract (∈Γ x τ Γ)
  #:mode (∈Γ I O I))

;; α ∈ Δ
(define-extended-judgement-form λF-H F.∈Δ
  #:contract (∈Δ α Δ)
  #:mode (∈Δ I I))

;; Δ ⊢ τ
(define-extended-judgement-form λF-H F.⊢τ
  #:contract (⊢τ Δ τ)
  #:mode (⊢τ I I))

;; Δ Γ ⊢ v : τ
;; Copied from λF-ACC, but with k ↝ l
(define-extended-judgement-form λF-H F.⊢v
  #:contract (⊢v Δ Γ v τ)
  #:mode (⊢v I I I O)

  [(⊢v Δ Γ l (vcode (α ..._1) (τ ..._2) β σ_1))
   (⊢τ Δ σ) ...
   (where (τ_0 ..._2) (substitute** (τ ...) (α ...) (σ ...)))
   (where σ_2 (substitute* (∀ β σ_1) (α ...) (σ ...)))
   (⊢v Δ Γ v τ_0) ...
   ---------------------------------------- "polyfun"
   (⊢v Δ Γ (⟨ l [σ ..._1] (v ..._2) ⟩) σ_2)]

  [(⊢v Δ Γ l (tcode (α ..._1) (τ ..._2) σ_1 σ_2))
   (⊢τ Δ σ) ...
   (where (τ_0 ..._2) (substitute** (τ ...) (α ...) (σ ...)))
   (where σ_12 (substitute* (→ σ_1 σ_2) (α ...) (σ ...)))
   (⊢v Δ Γ v τ_0) ...
   ----------------------------------------- "fun"
   (⊢v Δ Γ (⟨ l [σ ..._1] (v ..._2) ⟩) σ_12)])

;; Δ Γ ⊢ c : τ
;; Copied from λF-ACC
(define-judgement-form λF-H
  #:contract (⊢c Δ Γ c τ)
  #:mode (⊢c I I I O)

  [(⊢v Δ Γ v τ)
   ------------- "val"
   (⊢c Δ Γ v τ)]

  [(⊢v Δ Γ v_2 σ)
   (⊢v Δ Γ v_1 (→ σ τ))
   --------------------- "app"
   (⊢c Δ Γ (v_1 v_2) τ)]

  [(⊢τ Δ σ)
   (⊢v Δ Γ v (∀ α τ))
   ------------------------------------ "polyapp"
   (⊢c Δ Γ (v [σ]) (substitute τ α σ))])

;; Δ Γ ⊢ e : τ
;; Copied from λF-ACC
(define-judgement-form λF-H
  #:contract (⊢e Δ Γ e τ)
  #:mode (⊢e I I I O)

  [(⊢c Δ Γ c τ)
   ------------- "comp"
   (⊢e Δ Γ c τ)]

  [(⊢c Δ Γ c σ)
   (⊢e Δ (Γ (x : σ)) e τ)
   ------------------------- "let"
   (⊢e Δ Γ (let [x c] e) τ)])

;; ⊢ p : τ
;; Copied from λF-ACC's ⊢k, but with λ, Λ ↝ l ↦
;; If P contained letrecs, then l : (code (α ...) (τ ...) σ_1 σ_2) would be in Γ+
(define-judgement-form λF-H
  #:contract (⊢p p τ)
  #:mode (⊢p I O)

  [(where Δ_0 (Δ* α ...))
   (⊢τ Δ_0 τ) ...
   (⊢e (Δ_0 β) (Γ* (x : τ) ...) e σ)
   ------------------------------------------------------------------- "vcode"
   (⊢p (l ↦ (α ...) ([x : τ] ...) (β : *) e) (vcode (α ...) (τ ...) β σ))]

  [(where Δ_0 (Δ* α ...))
   (⊢τ Δ_0 τ) ...
   (⊢e Δ_0 (Γ* (x : τ) ... (y : σ_1)) e σ_2)
   ------------------------------------------------------------------------------- "tcode"
   (⊢p (l ↦ (α ...) ([x : τ] ...) (y : σ_1) e) (tcode (α ...) (τ ...) σ_1 σ_2))])

(module+ test
  (redex-judgement-holds-chk
   (⊢p)
   [(l ↦ (a b) ([x : a] [y : (∀ b b)]) (c : *) (y [c])) (vcode (α_1 β_1) (α_1 (∀ β_2 β_2)) α_2 α_2)]
   [(l ↦ (a b) ([x : a] [y : (→ a b)]) (z : a) (y z))   (tcode (α β) (α (→ α β)) α β)]))

;; ⊢ P : τ
;; This is the most significant new typing rule
(define-judgement-form λF-H
  #:contract (⊢ P τ)
  #:mode (⊢ I O)

  [(⊢p p σ) ...
   (where ((l ↦ _ _ _ _) ..._0) (p ...))
   (where Γ (Γ* (l : σ) ...))
   (⊢e · Γ e τ)
   ---------------------- "program"
   (⊢ (let (p ..._0) e) τ)])