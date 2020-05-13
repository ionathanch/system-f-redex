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
  (s ::= τ *) ;; Sorts (types or the * kind)
  (l ::= variable-not-otherwise-mentioned) ;; Labels
  (v ::= x (⟨ l [σ ...] (v ...) ⟩)) ;; Values
  (p ::= [l ↦ (α ...) ([x : τ] ...) (y : s) e]) ;; Code
  (Φ ::= (p ...)) ;; Code context
  (P ::= (let Φ e)) ;; Programs

  #:binding-forms
  (let ([l ↦
           (α ...) b #:refers-to (shadow α ...)
           (x : s)   #:refers-to (shadow α ...)
           e_body    #:refers-to (shadow α ... b x)]
        ...) #:refers-to (shadow l ...)
    e #:refers-to (shadow l ...)))

(default-language λF-H)

(module+ test
  ;; We now use the same syntax for type and term abstractions
  ;; with types having kind * for uniformity
  (redex-chk
   #:lang λF-H
   #:m P (let ([id-a ↦ (a) () (x : a) x]
               [id   ↦ ()  () (a : *) (id-a [a])])
           (let [id-idtype (id [(∀ a (→ a a))])]
             (id-idtype id))))

  ;; Check that the bindings are working correctly
  ;; The following should therefore be alpha-equivalent
  (redex-chk
   #:eq
   (let ([f ↦ (a) ([x : a]) (y : a) (x y)]) f)
   (let ([f ↦ (b) ([u : b]) (v : b) (u v)]) f)
   #:eq
   (let ([f ↦ () () (u : a) u] [g ↦ () () (v : b) v]) (let [w (g c)] (f w)))
   (let ([j ↦ () () (x : a) x] [k ↦ () () (y : b) y]) (let [z (k c)] (j z)))
   #:eq
   (let ([l0 ↦ () () (a : *) x]) x)
   (let ([l1 ↦ () () (a : *) x]) x)
   #:eq
   (let ([l0 ↦ (a) () (x : a) x] [l1 ↦ () () (a : *) (⟨ l0 [a] () ⟩)]) (⟨ l1 [] () ⟩))
   (let ([k0 ↦ (a) () (x : a) x] [k1 ↦ () () (a : *) (⟨ k0 [a] () ⟩)]) (⟨ k1 [] () ⟩))))

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
(define-metafunction/extension F.let* λF-H
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
;; Copied from λF since tcode/vcode can now enter the environment
(define-judgement-form λF-H
  #:contract (∈Γ x τ Γ)
  #:mode (∈Γ I O I)

  [-------------------- "Γ-car"
   (∈Γ x τ (Γ (x : τ)))]

  [(∈Γ x τ Γ)
   ------------------------- "Γ-cdr"
   (∈Γ x τ (Γ (x_0 : σ)))])

;; α ∈ Δ
(define-extended-judgement-form λF-H F.∈Δ
  #:contract (∈Δ α Δ)
  #:mode (∈Δ I I))

;; Δ ⊢ τ
(define-extended-judgement-form λF-H F.⊢τ
  #:contract (⊢τ Δ τ)
  #:mode (⊢τ I I))

;; Δ Γ ⊢ v : τ
;; Copied from λF-ANF and λF-ACC, but with k ↝ l
(define-judgement-form λF-H
  #:contract (⊢v Δ Γ v τ)
  #:mode (⊢v I I I O)

  [(∈Γ x τ Γ)
   ------------- "var"
   (⊢v Δ Γ x τ)]

  [(⊢v Δ Γ l (tcode (α ..._1) (τ ..._2) β σ_1))
   (⊢τ Δ σ) ...
   (where (τ_0 ..._2) (substitute** (τ ...) (α ...) (σ ...)))
   (where σ_2 (substitute* (∀ β σ_1) (α ...) (σ ...)))
   (⊢v Δ Γ v τ_0) ...
   ---------------------------------------- "polyfun"
   (⊢v Δ Γ (⟨ l [σ ..._1] (v ..._2) ⟩) σ_2)]

  [(⊢v Δ Γ l (vcode (α ..._1) (τ ..._2) σ_1 σ_2))
   (⊢τ Δ σ) ...
   (where (τ_0 ..._2) (substitute** (τ ...) (α ...) (σ ...)))
   (where σ_12 (substitute* (→ σ_1 σ_2) (α ...) (σ ...)))
   (⊢v Δ Γ v τ_0) ...
   ----------------------------------------- "fun"
   (⊢v Δ Γ (⟨ l [σ ..._1] (v ..._2) ⟩) σ_12)])

(module+ test
  (redex-judgement-holds-chk
   (⊢v (· b) (Γ* (l : (vcode (a) () a a))))
   [l (vcode (a) () a a)])
  (redex-judgement-equals-chk
   (⊢v (· b) (Γ* (l : (vcode (a) () a a))))
   [(⟨ l (b) () ⟩) τ #:pat τ #:term (→ b b)]))

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
;; Copied from λF-ACC's ⊢k, but with λ, Λ -> l ↦
;; If P contained letrecs, then l : (code (α ...) (τ ...) σ_1 σ_2) would be in Γ+
(define-judgement-form λF-H
  #:contract (⊢p p τ)
  #:mode (⊢p I O)

  [(where Δ_0 (Δ* α ...))
   (⊢τ Δ_0 τ) ...
   (⊢e (Δ_0 β) (Γ* (x : τ) ...) e σ)
   ------------------------------------------------------------------------ "tcode"
   (⊢p (l ↦ (α ...) ([x : τ] ...) (β : *) e) (tcode (α ...) (τ ...) β σ))]

  [(where Δ_0 (Δ* α ...))
   (⊢τ Δ_0 τ) ...
   (⊢e Δ_0 (Γ* (x : τ) ... (y : σ_1)) e σ_2)
   ------------------------------------------------------------------------------ "vcode"
   (⊢p (l ↦ (α ...) ([x : τ] ...) (y : σ_1) e) (vcode (α ...) (τ ...) σ_1 σ_2))])

(module+ test
  (redex-judgement-holds-chk
   (⊢p)
   [(l ↦ (a b) ([x : a] [y : (∀ b b)]) (c : *) (y [c])) (tcode (α_1 β_1) (α_1 (∀ β_2 β_2)) α_2 α_2)]
   [(l ↦ (a b) ([x : a] [y : (→ a b)]) (z : a) (y z))   (vcode (α β) (α (→ α β)) α β)]))

;; ⊢ P : τ
;; This is the most significant new typing rule
(define-judgement-form λF-H
  #:contract (⊢ P τ)
  #:mode (⊢ I O)

  [(⊢p p σ) ...
   (where ((l ↦ _ _ _ _) ...) (p ...))
   (where Γ (Γ* (l : σ) ...))
   (⊢e · Γ e τ)
   ---------------------- "program"
   (⊢ (let (p ...) e) τ)])

(module+ test
  (define-term id-id-term
    (let ([id-x ↦ (a) () (x : a) x]
          [id-a ↦ () ([id-x : (vcode (a) () a a)]) (a : *) (⟨ id-x [a] () ⟩)])
      (let* ([id (⟨ id-a () (id-x) ⟩)]
             [id-id-type (id [(∀ a (→ a a))])]
             [id-id (id-id-type id)])
        id-id)))

  (redex-judgement-equals-chk
   (⊢)
   [id-id-term τ #:pat τ #:term (∀ a (→ a a))]))


;; Dynamic Semantics

;; Big step semantics is more convenient here
(define-judgement-form λF-H
  #:contract (⇓ Φ e v)
  #:mode (⇓ I I O)

  [---------- "val"
   (⇓ Φ v v)]

  [(where x ,(variable-not-in (term c) 'y))
   (⇓ Φ (let [x (v_1 v_2)] x) v)
   ------------------ "comp-app"
   (⇓ Φ (v_1 v_2) v)]

  [(where x ,(variable-not-in (term c) 'y))
   (⇓ Φ (let [x (v_1 [σ])] x) v)
   ------------------ "comp-polyapp"
   (⇓ Φ (v_1 [σ]) v)]

  [(⇓ Φ (substitute e x v) v_0)
   ------------------------ "let"
   (⇓ Φ (let [x v] e) v_0)]

  [(where (l ↦ (α ...) ([x : _] ...) (y : _) e) (get-code l Φ))
   (where e_2 (substitute
               (substitute*
                (substitute* e (α ...) (σ ...))
                (x ...) (v ...))
               y v_1))
   (⇓ Φ e_2 v_2)
   (⇓ Φ (let [x_1 v_2] e_1) v_0)
   ------------------------------------------------------- "app"
   (⇓ Φ (let [x_1 ((⟨ l [σ ...] (v ...) ⟩) v_1)] e_1) v_0)]

  [(where (l ↦ (α ...) ([x : _] ...) (β : *) e) (get-code l Φ))
   (where e_2 (substitute
               (substitute*
                (substitute* e (α ...) (σ ...))
                (x ...) (v ...))
               β σ_1))
   (⇓ Φ e_2 v_2)
   (⇓ Φ (let [x_1 v_2] e_1) v_0)
   --------------------------------------------------------- "polyapp"
   (⇓ Φ (let [x_1 ((⟨ l [σ ...] (v ...) ⟩) [σ_1])] e_1) v_0)])

(define-metafunction λF-H
  reduce : P -> P
  [(reduce (let Φ e))
   ,(first (judgement-holds (⇓ Φ e v) (let Φ v)))])

;; [Note] Program Equality
;; This isn't really a good way to test, since compilation isn't guaranteed to
;; produce code blocks in a certain order, or to produce only those code blocks
;; that are actually needed. Ideally, we'd define a ≼ relation between programs,
;; where P ≼ Q iff P contains a permutation of a subset of the code blocks in Q.
;; A whole-program compiler correctness test would then look something like this:
;;   (compile (s.normalize P)) ≼ (t.normalize (compile P))
;; where t.normalize must also normalize each code block.
;; I suspect normalizing the source may only reduce the number of closures.
(module+ test
  (define-term id-id-term-reduced
    (let ([id-x ↦ (a) () (x : a) x]
          [id-a ↦ () ([id-x : (vcode (a) () a a)]) (a : *) (⟨ id-x [a] () ⟩)])
      (⟨ id-a [] (id-x) ⟩)))

  (redex-chk
   #:eq (reduce id-id-term) id-id-term-reduced))


;; Metafunctions
;; substitute*(*) copied from λF-ACC

;; (substitute** (τ_0 ... τ_n) (α ...) (σ ...))
;; Returns (τ_0[σ .../α ...] ... τ_n[σ .../α ...])
(define-metafunction/extension F.substitute** λF-H
  substitute** : (τ ..._0) (x ..._1) (any ..._1) -> (any ..._0))

;; (substitute* e (x ...) (v ...)) or (substitute* e (α ...) (σ ...))
;; Returns e[v_1/x_1]...[v_n/x_n], also denoted e[v_1 .../x_1 ...]
(define-metafunction/extension F.substitute* λF-H
  substitute* : any (x ..._1) (any ..._1) -> any)

;; Get the code associated with given label
(define-metafunction λF-H
  get-code : l Φ -> p
  ;; No base case: if the label isn't found, it's an error
  [(get-code l ([l ↦ any_types any_terms any_arg e_body] _ ...))
   (l ↦ any_types any_terms any_arg e_body)]
  [(get-code l ([_ ↦ _ _ _ _] p ...))
   (get-code l (p ...))])
