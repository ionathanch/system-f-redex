#lang racket

(require (rename-in redex/reduction-semantics
                    ;; This is obviously the correct spelling of "judgement"
                    [define-judgment-form define-judgement-form]
                    [judgment-holds       judgement-holds]))

(module+ test
  (require (rename-in redex-chk
                      [redex-judgment-holds-chk redex-judgement-holds-chk])))

(provide (all-defined-out))

;; SYSTEM F ;;

;; Syntax

(define-language λF
  (x α ::= variable-not-otherwise-mentioned) ;; Term and type variables
  (τ σ ::= α (→ τ τ) (∀ α τ)) ;; Types
  (e   ::= x (λ (x : τ) e) (e e) (Λ α e) (e [τ]) (let [x e] e)) ;; Terms

  (Δ   ::= · (Δ α)) ;; Type contexts
  (Γ   ::= · (Γ (x : τ))) ;; Term contexts

  (v   ::= x (λ (x : τ) e) (Λ α e)) ;; Values
  (E   ::= hole (E e) (v E) (E [τ]) (let [x E] e) (let [x v] E)) ;; Evaluation contexts (call-by-value)

  #:binding-forms
  (λ (x : τ) e #:refers-to x)
  (Λ α e #:refers-to α)
  (∀ α τ #:refers-to α)
  (let [x e_1] e_2 #:refers-to x))

(default-language λF)

;; There's this little problem that because e and τ are defined in separate nonterminals,
;; when typing (Λ α e) as (∀ α τ), the two αs are different because Redex does funny things
;; with the binding as if they were meant to be separate, shadowed variables...
;; The solution seems to be to use alpha-equivalent? as needed

;; Unroll (λ* (a_1 ... a_n) e) into (L a_1 ... (L a_n e))
;; where (L ::= λ Λ) (a ::= [x : τ] α)
(define-metafunction λF
  λ* : (any ...) e -> e
  [(λ* () e) e]
  [(λ* ([x : τ] any ...) e)
   (λ (x : τ) (λ* (any ...) e))]
  [(λ* (α any ...) e)
   (Λ α (λ* (any ...) e))])

;; Unroll (@ e a_1 ... a_n) into ((e a_1) ... a_n)
;; where (a ::= e [τ])
(define-metafunction λF
  @ : any ... -> e
  [(@ e) e]
  [(@ e_1 e_2 any ...)
   (@ (e_1 e_2) any ...)]
  [(@ e [τ] any ...)
   (@ (e [τ]) any ...)])

;; Unroll (let* ([x_1 e_1] ... [x_n e_n]) e) into (let [x_1 e_1] ... (let [x_n e_n] e))
(define-metafunction λF
  let* : ([x e] ...) e -> e
  [(let* () e) e]
  [(let* ([x e] [x_r e_r] ...) e_body)
   (let [x e] (let* ([x_r e_r] ...) e_body))])

;; Unroll (τ_1 → ... → τ_n) into (τ_1 → (... → τ_n))
(define-metafunction λF
  →* : τ ... τ -> τ
  [(→* τ) τ]
  [(→* τ τ_r ...)
   (→ τ (→* τ_r ...))])

;; Unroll (∀* (α_1 ... a_n) τ) as (∀ α_1 ... (∀ α_n τ))
(define-metafunction λF
  ∀* : (α ...) τ -> τ
  [(∀* () τ) τ]
  [(∀* (α α_r ...) τ)
   (∀ α (∀* (α_r ...) τ))])

;; Unroll ((x_1 : τ_1) ... (x_n : τ_n)) into ((· (x_1 : τ_1)) ... (x_n : τ_n))
(define-metafunction λF
  Γ* : (x : τ) ... -> Γ
  [(Γ*) ·]
  [(Γ* (x_r : τ_r) ... (x : τ))
   ((Γ* (x_r : τ_r) ...) (x : τ))])

;; Unroll (α_1 ... α_n) into ((· α_1) ... α_n)
(define-metafunction λF
  Δ* : α ... -> Δ
  [(Δ*) ·]
  [(Δ* α_r ... α)
   ((Δ* α_r ...) α)])

(module+ test
  (redex-chk
   (λ* ([x : α]) x) (λ (x : α) x)
   (λ* (α) x) (Λ α x)
   (λ* ([x : α] β [z : γ]) (x z)) (λ (x : α) (Λ β (λ (z : γ) (x z))))
   (@ x) x
   (@ x [β] z) ((x [β]) z)
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
(define-judgement-form λF
  #:contract (∈Γ x τ Γ)
  #:mode (∈Γ I O I)

  [-------------------- "Γ-car"
   (∈Γ x τ (Γ (x : τ)))]

  [(∈Γ x τ Γ)
   ------------------------- "Γ-cdr"
   (∈Γ x τ (Γ (x_1 : τ_1)))])

;; α ∈ Δ
(define-judgement-form λF
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
(define-judgement-form λF
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

;; Δ Γ ⊢ e : τ
(define-judgement-form λF
  #:contract (⊢ Δ Γ e τ)
  #:mode (⊢ I I I O)

  [(∈Γ x τ Γ)
   -------------- "var"
   (⊢ Δ Γ x τ)]

  [(⊢τ Δ τ_1)
   (⊢ Δ (Γ (x : τ_1)) e τ_2)
   ------------------------------------ "fun"
   (⊢ Δ Γ (λ (x : τ_1) e) (→ τ_1 τ_2))]

  [(⊢ Δ Γ e_2 τ_1)
   (⊢ Δ Γ e_1 (→ τ_1 τ_2))
   ------------------------ "app"
   (⊢ Δ Γ (e_1 e_2) τ_2)]

  [(⊢ (Δ α) Γ e τ)
   ------------------------- "polyfun"
   (⊢ Δ Γ (Λ α e) (∀ α τ))]

  [(⊢τ Δ τ)
   (⊢ Δ Γ e (∀ α τ_1))
   ------------------------------------- "polyapp"
   (⊢ Δ Γ (e [τ]) (substitute τ_1 α τ))]

  [(⊢ Δ Γ e_1 τ_1)
   (⊢ Δ (Γ (x : τ_1)) e_2 τ)
   ---------------------------- "let"
   (⊢ Δ Γ (let [x e_1] e_2) τ)])

(module+ test  
  (redex-judgement-holds-chk
   (⊢ (Δ* α β) ·) ;; We need some base types, after all
   [(λ (x : α) x) (→ α α)]
   [((λ (x : (→ α α)) x) (λ (x : α) x)) (→ α α)]
   #;[(Λ γ (λ (x : γ) x)) (∀ γ (→ γ γ))]
   #;[((Λ α (λ (x : α) (Λ α (λ (y : α) x)))) [γ])
    (→ γ (∀ β (→ β γ)))]
   [((Λ γ (λ (x : γ) x)) [α]) (→ α α)]
   [(let [x (Λ α (λ (y : α) y))] (@ x [(∀ α (→ α α))] x)) (∀ α (→ α α))])

  ;; The ⊢ judgement will return (∀ γ«n» (→ γ«n» γ«n»)) to "prevent"
  ;; shadowing between the term's γ and the type's γ, so the test above
  ;; commented out does not work, and we have to instead mantually test
  ;; that the judgement produces an alpha-equivalent type
  ;; The default #:equiv for test-equal is the default-language's alpha-equivalent?

  (test-equal
   (first (judgement-holds (⊢ · · (Λ γ (λ (x : γ) x)) τ) τ))
   (term (∀ γ (→ γ γ))))

  (test-equal
   (first (judgement-holds (⊢ (· γ) · ((Λ α (λ (x : α) (Λ α (λ (y : α) x)))) [γ]) τ) τ))
   (term (→ γ (∀ α (→ α γ))))))


;; Dynamic Semantics

(define ⟶
  (reduction-relation
   λF
   (--> ((λ (x : τ) e) v) ;; CBV
        (substitute e x v)
        "β")
   (--> ((Λ α e) [τ])
        (substitute e α τ)
        "τ")
   (--> (let [x v] e) ;; CBV
        (substitute e x v)
        "ζ")))

(define ⟶*
  (context-closure ⟶ λF E))

(define-metafunction λF
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
   (term (@ (let [x (λ* (α [y : α]) y)]
              (@ x [(∀ α (→ α α))] x))
            [(∀ β (→ β β))]
            (λ (y : β) y)))
   (term (λ (y : β) y))))


;; Bonus Content

;; Normalization
;; The following extensions reduce lambda terms to normal form,
;; which isn't necessarily something we want if we're compiling;
;; instead, we want to keep computations abstracted.

(define-extended-language λF⇓ λF
  (F ::= E (λ (x : τ) F) (Λ α F)))

(define ⇓
  (context-closure ⟶ λF⇓ F))

(define-metafunction λF
  normalize : e -> v
  [(normalize e)
   ,(first (apply-reduction-relation* ⇓ (term e) #:cache-all? #t))])

;; Church encoding

(define-metafunction λF
  number->term : number (λ (x : τ) (λ (x : τ) e)) -> e
  [(number->term 0 e) e]
  [(number->term number (λ (x_1 : τ_1) (λ (x_2 : τ_2) e)))
   (number->term ,(sub1 (term number)) (λ (x_1 : τ_1) (λ (x_2 : τ_2) (x_1 e))))])
(define-metafunction λF
  ♯ : number -> e
  [(♯ number) (Λ α (number->term number (λ* ([f : (→ α α)] [x : α]) x)))])

(define-term nat (∀ α (→* (→ α α) α α)))

(define-term succ
  (λ* ([n : nat] α [f : (→ α α)] [x : α])
      (f (@ n [α] f x))))

(define-term plus
  (λ* ([n : nat] [m : nat] α [f : (→ α α)] [x : α])
      (@ n [α] f (@ m [α] f x))))

;; putting this on hold, because I wanted to implement ANF, not go through the motions of Church encoding
;; I am satisfied knowing that the basic arithmetic operations are probably all typeable in System F
