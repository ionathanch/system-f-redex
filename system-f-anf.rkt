#lang racket

(require (rename-in redex/reduction-semantics
                    ;; This is obviously the correct spelling of "judgement"
                    [define-judgment-form define-judgement-form]
                    [judgment-holds       judgement-holds]))

(module+ test
  (require (rename-in redex-chk
                      [redex-judgment-holds-chk redex-judgement-holds-chk])))

(provide (all-defined-out))

;; ANF-RESTRICTED SYSTEM F ;;

;; Syntax

(define-language λF-ANF
  (x α ::= variable-not-otherwise-mentioned) ;; Term and type variables
  (τ σ ::= α (→ τ τ) (∀ α τ)) ;; Types

  (v   ::= x (λ (x : τ) e) (Λ α e)) ;; Values
  (c   ::= v (v v) (v [τ])) ;; Computations
  (e   ::= c (let [x c] e)) ;; Configurations

  (Δ   ::= · (Δ α)) ;; Type contexts
  (Γ   ::= · (Γ (x : τ))) ;; Term contexts
  
  (E   ::= hole (let [x E] e)) ;; Evaluation contexts

  (K   ::= ∘ (let [x ∘] e)) ;; Continuations
  (k   ::= (∘ c) ((let [x ∘] k) c)) ;; Continuation expressions

  #:binding-forms
  (λ (x : τ) e #:refers-to x)
  (Λ α e #:refers-to α)
  (∀ α τ #:refers-to α)
  (let [x e_1] e_2 #:refers-to x)
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
(define-metafunction λF-ANF
  λ* : (any ...) e -> e
  [(λ* () e) e]
  [(λ* ([x : τ] any ...) e)
   (λ (x : τ) (λ* (any ...) e))]
  [(λ* (α any ...) e)
   (Λ α (λ* (any ...) e))])

;; Unroll (@ e a_1 ... a_n) into ((e a_1) ... a_n)
;; where (a ::= e [τ])
;; Doesn't apply to ANF terms
#;(define-metafunction λF-ANF
    @ : any ... -> e
    [(@ e) e]
    [(@ e_1 e_2 any ...)
     (@ (e_1 e_2) any ...)]
    [(@ e [τ] any ...)
     (@ (e [τ]) any ...)])

;; Unroll (let* ([x_1 a_1] ... [x_n a_n]) e) into (let [x_1 a_1] ... (let [x_n a_n] e))
;; where (a ::= c ∘)
(define-metafunction λF-ANF
  let* : ([x any] ...) e -> e
  [(let* () e) e]
  [(let* ([x any] [x_r any_r] ...) e)
   (let [x any] (let* ([x_r any_r] ...) e))])

;; Unroll (τ_1 → ... → τ_n) into (τ_1 → (... → τ_n))
(define-metafunction λF-ANF
  →* : τ ... τ -> τ
  [(→* τ) τ]
  [(→* τ τ_r ...)
   (→ τ (→* τ_r ...))])

;; Unroll (∀* (α_1 ... a_n) τ) as (∀ α_1 ... (∀ α_n τ))
(define-metafunction λF-ANF
  ∀* : (α ...) τ -> τ
  [(∀* () τ) τ]
  [(∀* (α α_r ...) τ)
   (∀ α (∀* (α_r ...) τ))])

;; Unroll ((x_1 : τ_1) ... (x_n : τ_n)) into ((· (x_1 : τ_1)) ... (x_n : τ_n))
(define-metafunction λF-ANF
  Γ* : (x : τ) ... -> Γ
  [(Γ*) ·]
  [(Γ* (x_r : τ_r) ... (x : τ))
   ((Γ* (x_r : τ_r) ...) (x : τ))])

;; Unroll (α_1 ... α_n) into ((· α_1) ... α_n)
(define-metafunction λF-ANF
  Δ* : α ... -> Δ
  [(Δ*) ·]
  [(Δ* α_r ... α)
   ((Δ* α_r ...) α)])

(module+ test
  (redex-chk
   (λ* ([x : α]) x) (λ (x : α) x)
   (λ* (α) x) (Λ α x)
   (λ* ([x : α] β [z : γ]) (x z)) (λ (x : α) (Λ β (λ (z : γ) (x z))))
   (let* ([x (λ (x : α) x)]) x) (let [x (λ (x : α) x)] x)
   (let* ([x (λ (x : α) x)] [y x] [z y]) z) (let (x (λ (x : α) x)) (let (y x) (let (z y) z)))
   (→* α) α
   (→* α β γ) (→ α (→ β γ))
   (→* (→ α β) γ) (→ (→ α β) γ)
   (∀* (α) α) (∀ α α)
   (∀* (α β γ) β) (∀ α (∀ β (∀ γ β)))
   (Γ*) ·
   (Γ* (x : α) (y : β)) ((· (x : α)) (y : β))
   (Δ*) ·
   (Δ* α β) ((· α) β)))


;; Static Semantics

;; (x : τ) ∈ Γ
(define-judgement-form λF-ANF
  #:contract (∈Γ x τ Γ)
  #:mode (∈Γ I O I)

  [-------------------- "Γ-car"
   (∈Γ x τ (Γ (x : τ)))]

  [(∈Γ x τ Γ)
   ------------------------- "Γ-cdr"
   (∈Γ x τ (Γ (x_1 : τ_1)))])

;; α ∈ Δ
(define-judgement-form λF-ANF
  #:contract (∈Δ α Δ)
  #:mode (∈Δ I I)

  [------------- "Δ-car"
   (∈Δ α (Δ α))]

  [(∈Δ α Δ)
   --------------- "Δ-cdr"
   (∈Δ α (Δ α_1))])

(module+ test
  (redex-judgement-holds-chk
   ∈Γ
   [#:f x α ·]
   [#:f x α (· (y : α))]
   [#:f x β (· (x : α))]
   [x α (· (x : α))]
   [x (→ α β) (Γ* (y : α) (x : (→ α β)))])

  (redex-judgement-holds-chk
   ∈Δ
   [α (Δ* α β γ)]
   [#:f α (· β)]))

;; Δ ⊢ τ
(define-judgement-form λF-ANF
  #:contract (⊢τ Δ τ)
  #:mode (⊢τ I I)

  [(∈Δ α Δ)
   ----------- "τ-var"
   (⊢τ Δ α)]

  [(⊢τ Δ τ_1)
   (⊢τ Δ τ_2)
   -------------------- "τ-fun"
   (⊢τ Δ (→ τ_1 τ_2))]

  [(⊢τ (Δ α) τ)
   ----------------- "τ-poly"
   (⊢τ Δ (∀ α τ))])

(module+ test
  (redex-judgement-holds-chk
   ⊢τ
   [(· α) α]
   [(· α) (→ α α)]
   [(· α) (∀ α α)]
   [#:f (· β) α]))

;; Δ Γ ⊢ v : τ
(define-judgement-form λF-ANF
  #:contract (⊢v Δ Γ v τ)
  #:mode (⊢v I I I O)

  [(∈Γ x τ Γ)
   -------------- "var"
   (⊢v Δ Γ x τ)]

  [(⊢τ Δ τ_1)
   (⊢e Δ (Γ (x : τ_1)) e τ_2)
   ------------------------------------ "fun"
   (⊢v Δ Γ (λ (x : τ_1) e) (→ τ_1 τ_2))]

  [(⊢e (Δ α) Γ e τ)
   ------------------------- "polyfun"
   (⊢v Δ Γ (Λ α e) (∀ α τ))])

;; Δ Γ ⊢ c : τ
(define-judgement-form λF-ANF
  #:contract (⊢c Δ Γ c τ)
  #:mode (⊢c I I I O)

  [(⊢v Δ Γ v τ)
   ------------ "val"
   (⊢c Δ Γ v τ)]

  [(⊢v Δ Γ v_2 τ_1)
   (⊢v Δ Γ v_1 (→ τ_1 τ_2))
   ------------------------ "app"
   (⊢c Δ Γ (v_1 v_2) τ_2)]

  [(⊢τ Δ τ)
   (⊢v Δ Γ v (∀ α τ_1))
   ------------------------------------- "polyapp"
   (⊢c Δ Γ (v [τ]) (substitute τ_1 α τ))])

;; Δ Γ ⊢ e : τ
(define-judgement-form λF-ANF
  #:contract (⊢e Δ Γ e τ)
  #:mode (⊢e I I I O)

  [(⊢c Δ Γ c τ)
   ------------ "comp"
   (⊢e Δ Γ c τ)]

  [(⊢c Δ Γ c τ_c)
   (⊢e Δ (Γ (x : τ_c)) e τ)
   ---------------------------- "let"
   (⊢e Δ Γ (let [x c] e) τ)])

(module+ test  
  (redex-judgement-holds-chk
   (⊢v (Δ* α β) (· (z : α)))
   [z α]
   [(λ (x : α) x) (→ α α)]
   #;[(Λ γ (λ (x : γ) x)) (∀ γ (→ γ γ))])

  (redex-judgement-holds-chk
   (⊢c (Δ* α β) ·)
   [((λ (x : (→ α α)) x) (λ (x : α) x)) (→ α α)]
   [((Λ γ (λ (x : γ) x)) [α]) (→ α α)]
   #;[((Λ α (λ (x : α) (Λ α (λ (y : α) x)))) [γ])
    (→ γ (∀ β (→ β γ)))])

  (redex-judgement-holds-chk
   (⊢e (Δ* α β) ·)
   [(let [x (Λ α (λ (y : α) y))] x) (∀ α (→ α α))]
   [(let* ([x (Λ α (λ (y : α) y))]
           [y x])
      y)
    (∀ α (→ α α))]
   [(let* ([x (Λ α (λ (y : α) y))]
           [y x])
      (y [(∀ β (→ β β))]))
    (→ (∀ β (→ β β)) (∀ β (→ β β)))]
   [(let* ([x (Λ α (λ (y : α) y))]
           [y (x [(∀ β (→ β β))])])
      y)
    (→ (∀ β (→ β β)) (∀ β (→ β β)))])

  (test-equal
   (first (judgement-holds (⊢v · · (Λ γ (λ (x : γ) x)) τ) τ))
   (term (∀ γ (→ γ γ))))

  (test-equal
   (first (judgement-holds (⊢c (· γ) · ((Λ α (λ (x : α) (Λ α (λ (y : α) x)))) [γ]) τ) τ))
   (term (→ γ (∀ α (→ α γ))))))

;; Δ Γ ⊢ K : τ ⇒ τ
(define-judgement-form λF-ANF
  #:contract (⊢K Δ Γ K τ τ)
  #:mode (⊢K I I I I O)

  [-------------- "K-empty"
   (⊢K Δ Γ ∘ τ τ)]

  [(⊢e Δ (Γ (x : τ_x)) e τ)
   ----------------------------- "K-bind"
   (⊢K Δ Γ (let [x ∘] e) τ_x τ)])

;; Δ Γ ⊢ k : τ
(define-judgement-form λF-ANF
  #:contract (⊢k Δ Γ k τ)
  #:mode (⊢k I I I O)

  [(⊢c Δ Γ c τ)
   (⊢K Δ Γ ∘ τ τ)
   ---------------- "k-empty"
   (⊢k Δ Γ (∘ c) τ)]

  [(⊢c Δ Γ c τ_c)
   (⊢k Δ (Γ (x : τ_c)) k τ)
   ----------------------------- "k-bind"
   (⊢k Δ Γ ((let [x ∘] k) c) τ)])

(module+ test
  (redex-judgement-holds-chk
   (⊢K (· α) ·)
   [∘ α α]
   [∘ (→ α α) (→ α α)]
   [(let [x ∘] x) α α]
   [(let [x ∘]
      (let [y (λ (z : α) z)]
        (y x)))
    α α])

  (redex-judgement-holds-chk
   (⊢k (Δ* α) (Γ* (a : α)))
   [((let [x ∘]
       ((let [y ∘]
          ((let [z ∘]
             (∘ z)) y)) x)) a)
    α]))


;; Dynamic Semantics

(define ⟶
  (reduction-relation
   λF-ANF
   (--> ((λ (x : τ) e) v)
        (substitute e x v)
        "β")
   (--> ((Λ α e) [τ])
        (substitute e α τ)
        "τ")
   (--> (let [x v] e)
        (substitute e x v)
        "ζ")))

(define ⟶*
  (context-closure ⟶ λF-ANF E))

(define-metafunction λF-ANF
  reduce : e -> v
  [(reduce e)
   ,(first (apply-reduction-relation* ⟶* (term e) #:cache-all? #t))])

(module+ test
  (test-->
   ⟶*
   (term ((λ (x : α) x) (λ (y : β) y)))
   (term (λ (y : β) y)))
  (test-->
   ⟶*
   (term ((Λ α (λ (x : α) x)) [(∀ β β)]))
   (term (λ (x : (∀ β β)) x)))
  (test-->
   ⟶*
   (term (let [x y] (x x)))
   (term (y y)))
  (test-->>
   ⟶*
   (term (let* ([x (λ* (α [y : α]) y)]
                [y (x [(∀ α (→ α α))])]
                [z (y x)]
                [a (z [(∀ β (→ β β))])]
                [b (a (λ (y : β) y))])
           b))
   (term (λ (y : β) y))))

(define plug
  (reduction-relation
   λF-ANF
   (--> (∘ e) e)
   (--> ((let [x ∘] e) c) (let [x c] e))))

(define plug*
  (compatible-closure plug λF-ANF k))

(define-metafunction λF-ANF
  continue : (K c) -> e
  [(continue (K c))
   ,(first (apply-reduction-relation* plug (term (K c)) #:cache-all? #t))])

(module+ test
  (test-->
   plug*
   (term (∘ x))
   (term x))
  (test-->
   plug*
   (term ((let [x ∘] x) y))
   (term (let [x y] x)))
  (test-->>
   plug*
   (term ((let [x ∘]
            ((let [y ∘]
               ((let [z ∘]
                  (∘ z)) c)) b)) a))
   (term (let* ([x a] [y b] [z c]) z))))
