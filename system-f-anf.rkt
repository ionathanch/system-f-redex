#lang racket

(require (rename-in (prefix-in F. "./system-f.rkt")
                    [F.λF λF])
         (rename-in redex/reduction-semantics
                    [define-judgment-form          define-judgement-form]
                    [define-extended-judgment-form define-extended-judgement-form]
                    [judgment-holds                judgement-holds]))

(module+ test
  (require "./redex-chk.rkt"))

(provide (all-defined-out))

;; ANF-RESTRICTED SYSTEM F ;;

;; Syntax

(define-extended-language λF-ANF λF
  (v ::= x (λ (x : τ) e) (Λ α e)) ;; Values
  (c ::= v (v v) (v [σ])) ;; Computations
  (e ::= c (let [x c] e)) ;; Configurations

  (E ::= hole (let [x hole] e)) ;; Evaluation contexts
  (F ::= .... (let [x c] F))    ;; Evaluation contexts (normalization)

  (K ::= hole (let [x hole] e)) ;; Continuation contexts
  (M ::= hole (let [x c] M))    ;; Composition contexts

  #:binding-forms
  (let [x ∘] e #:refers-to x))

(default-language λF-ANF)

(module+ test
  (redex-chk
   #:lang λF-ANF
   #:m e (λ (y : β) y)
   #:m e (Λ α x)
   #:m e ((λ (y : β) y) (λ (y : β) y))
   #:m e ((Λ α x) [(∀ β (→ β β))])
   #:m e (let [x (λ (y : β) y)] x)
   #:m e (let [x ((λ (y : β) y) (λ (y : β) y))] x)
   #:m e (let [x (λ (y : β) y)] (let [y (x x)] y))
   #:m e (let [x (Λ α (λ (x : α) x))] (let [y (x [β])] (y z)))
   #:f #:m e (((Λ α (λ (x : α) x)) [β]) y)))

;; Unroll (λ* (a_1 ... a_n) e) into (L a_1 ... (L a_n e))
;; where (L ::= λ Λ) (a ::= [x : τ] α)
(define-metafunction/extension F.λ* λF-ANF
  λ* : (any ...) e -> e)

;; Unroll (@ e a_1 ... a_n) into ((e a_1) ... a_n)
;; where (a ::= e [τ])
;; The output technically isn't valid ANF but it's useful to have
(define-metafunction/extension F.@ λF-ANF
  @ : any ... -> any)

;; Unroll (let* ([x_1 e_1] ... [x_n e_n]) e) into (let [x_1 e_1] ... (let [x_n e_n] e))
(define-metafunction/extension F.let* λF-ANF
  let* : ([x e] ...) e -> e)

;; Unroll (τ_1 → ... → τ_n) into (τ_1 → (... → τ_n))
(define-metafunction/extension F.→* λF-ANF
  →* : τ ... τ -> τ)

;; Unroll (∀* (α_1 ... a_n) τ) as (∀ α_1 ... (∀ α_n τ))
(define-metafunction/extension F.∀* λF-ANF
  ∀* : (α ...) τ -> τ)

;; Unroll ((x_1 : τ_1) ... (x_n : τ_n)) into ((· (x_1 : τ_1)) ... (x_n : τ_n))
(define-metafunction/extension F.Γ* λF-ANF
  Γ* : (x : τ) ... -> Γ)

;; Unroll (α_1 ... α_n) into ((· α_1) ... α_n)
(define-metafunction/extension F.Δ* λF-ANF
  Δ* : α ... -> Δ)

(module+ test
  (redex-chk
   (λ* ([x : a]) x) (λ (x : a) x)
   (λ* (a) x) (Λ a x)
   (λ* ([x : a] b [z : d]) (x z)) (λ (x : a) (Λ b (λ (z : d) (x z))))
   (let* ([x (λ (x : a) x)]) x) (let [x (λ (x : a) x)] x)
   (let* ([x (λ (x : a) x)] [y x] [z y]) z) (let [x (λ (x : a) x)] (let [y x] (let [z y] z)))
   (→* a) a
   (→* a b d) (→ a (→ b d))
   (→* (→ a b) d) (→ (→ a b) d)
   (∀* (a) a) (∀ a a)
   (∀* (a b d) b) (∀ a (∀ b (∀ d b)))
   (Γ*) ·
   (Γ* (x : a) (y : b)) ((· (x : a)) (y : b))
   (Δ*) ·
   (Δ* a b) ((· a) b)))


;; Static Semantics

;; (x : τ) ∈ Γ
(define-extended-judgement-form λF-ANF F.∈Γ
  #:contract (∈Γ x τ Γ)
  #:mode (∈Γ I O I))

;; α ∈ Δ
(define-extended-judgement-form λF-ANF F.∈Δ
  #:contract (∈Δ α Δ)
  #:mode (∈Δ I I))

;; Δ ⊢ τ
(define-extended-judgement-form λF-ANF F.⊢τ
  #:contract (⊢τ Δ τ)
  #:mode (⊢τ I I))

(module+ test
  (redex-judgement-holds-chk
   ∈Γ
   [#:f x a ·]
   [#:f x a (· (y : a))]
   [#:f x b (· (x : a))]
   [x a (· (x : a))]
   [x (→ a b) (Γ* (y : a) (x : (→ a b)))])

  (redex-judgement-holds-chk
   ∈Δ
   [a (Δ* a b c)]
   [#:f a (· b)])

  (redex-judgement-holds-chk
   ⊢τ
   [(· a) a]
   [(· a) (→ a a)]
   [(· a) (∀ a a)]
   [#:f (· b) a]))

;; Δ Γ ⊢ v : τ
(define-judgement-form λF-ANF
  #:contract (⊢v Δ Γ v τ)
  #:mode (⊢v I I I O)

  [(∈Γ x τ Γ)
   ------------- "var"
   (⊢v Δ Γ x τ)]

  [(⊢τ Δ σ)
   (⊢e Δ (Γ (x : σ)) e τ)
   ------------------------------- "fun"
   (⊢v Δ Γ (λ (x : σ) e) (→ σ τ))]

  [(⊢e (Δ α) Γ e τ)
   -------------------------- "polyfun"
   (⊢v Δ Γ (Λ α e) (∀ α τ))])

;; Δ Γ ⊢ c : τ
(define-judgement-form λF-ANF
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
(define-judgement-form λF-ANF
  #:contract (⊢e Δ Γ e τ)
  #:mode (⊢e I I I O)

  [(⊢c Δ Γ c τ)
   ------------- "comp"
   (⊢e Δ Γ c τ)]

  [(⊢c Δ Γ c σ)
   (⊢e Δ (Γ (x : σ)) e τ)
   ------------------------- "let"
   (⊢e Δ Γ (let [x c] e) τ)])

;; Places where α is used to pattern-match to any type variable
;; to test for an alpha-equivalent type have been marked with ;; α
(module+ test  
  (redex-judgement-holds-chk
   (⊢v (Δ* a b) (· (z : a)))
   [z a]
   [(λ (x : a) x) (→ a a)]
   [(Λ a (λ (x : a) x)) (∀ α (→ α α))])  ;; α

  (redex-judgement-holds-chk
   (⊢c (Δ* a b) ·)
   [((λ (x : (→ a a)) x) (λ (x : a) x)) (→ a a)]
   [((Λ a (λ (x : a) x)) [b]) (→ b b)]
   [((Λ a (λ (x : a) (Λ a (λ (y : a) x)))) [b])
    (→ b (∀ α (→ α b)))]) ;; α

  (redex-judgement-holds-chk
   (⊢e (Δ* a b) ·)
   [(let [x (Λ a (λ (y : a) y))] x) (∀ α (→ α α))] ;; α
   [(let* ([x (Λ a (λ (y : a) y))]
           [y x])
      y)
    (∀ α (→ α α))] ;; α
   [(let* ([x (Λ a (λ (y : a) y))]
           [y x])
      (y [(∀ b (→ b b))]))
    (→ (∀ b (→ b b)) (∀ b (→ b b)))]
   [(let* ([x (Λ a (λ (y : a) y))]
           [y (x [(∀ b (→ b b))])])
      y)
    (→ (∀ b (→ b b)) (∀ b (→ b b)))]))

;; Δ Γ ⊢ K : τ ⇒ τ
(define-judgement-form λF-ANF
  #:contract (⊢K Δ Γ K τ τ)
  #:mode (⊢K I I I I O)

  [--------------- "K-empty"
   (⊢K Δ Γ hole τ τ)]

  [(⊢e Δ (Γ (x : σ)) e τ)
   --------------------------- "K-bind"
   (⊢K Δ Γ (let [x hole] e) σ τ)])

(module+ test
  (redex-judgement-holds-chk
   (⊢K (· a) ·)
   [hole a a]
   [hole (→ a a) (→ a a)]
   [(let [x hole] x) a a]
   [(let [x hole]
      (let [y (λ (z : a) z)]
        (y x)))
    a a]))

(define-metafunction λF-ANF
  infer : e -> τ
  [(infer e)
   τ
   (judgement-holds (⊢e · · e τ))])


;; Dynamic Semantics

(define ⟶
  (reduction-relation
   λF-ANF
   (--> (let [x v] e)
        (substitute e x v)
        "ζ")
   (--> (in-hole E ((λ (x : τ) e) v))
        (in-hole M (in-hole E c))
        (where (in-hole M c) (substitute e x v))
        "β")
   (--> (in-hole E ((Λ α e) [τ]))
        (in-hole M (in-hole E c))
        (where (in-hole M c) (substitute e α τ))
        "τ")))

(define-metafunction λF-ANF
  reduce : e -> v
  [(reduce e)
   ,(first (apply-reduction-relation* ⟶ (term e) #:cache-all? #t))])

(define ⇓
  (context-closure ⟶ λF-ANF F))

(define-metafunction λF-ANF
  normalize : e -> v
  [(normalize e)
   ,(first (apply-reduction-relation* ⇓ (term e) #:cache-all? #t))])

(module+ test
  (test-->
   ⟶
   (term ((λ (x : a) x) (λ (y : b) y)))
   (term (λ (y : b) y)))
  (test-->
   ⟶
   (term ((Λ a (λ (x : a) x)) [(∀ b b)]))
   (term (λ (x : (∀ b b)) x)))
  (test-->
   ⟶
   (term (let [x y] (x x)))
   (term (y y)))
  (test-->
   ⟶
   (term (let [f ((λ (x : a)
                    (let [y x] y)) z)]
           f))
   (term (let* ([y z]
                [f y])
           f)))
  (test-->>
   ⟶
   (term (let* ([x (λ* (a [y : a]) y)]
                [y (x [(∀ a (→ a a))])]
                [z (y x)]
                [w (z [(∀ b (→ b b))])]
                [u (w (λ (y : b) y))])
           u))
   (term (λ (y : b) y)))
  (test-->>
   ⇓
   (term (λ (x : a) ((λ (y : b) y) x)))
   (term (λ (x : a) x)))
  (test-->>
   ⇓
   (term (λ* ([x : a] [f : (→ a a)]) (let* ([z x] [y (f z)]) y)))
   (term (λ* ([x : a] [f : (→ a a)]) (let [y (f x)] y))))
  (test-->>
   ⇓
   (term (λ (g : b) (let* ([h (g g)] [f (λ (y : a) y)]) (g f))))
   (term (λ (g : b) (let* ([h (g g)]) (g (λ (y : a) y)))))))
