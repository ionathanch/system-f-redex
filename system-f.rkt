#lang racket

(require (rename-in redex/reduction-semantics
                    ;; This is obviously the correct spelling of "judgement"
                    [define-judgment-form define-judgement-form]
                    [judgment-holds       judgement-holds]))

(module+ test
  (require "./redex-chk.rkt"))

(provide (all-defined-out))

;; SYSTEM F ;;

;; Syntax

(define-language λF
  (α β ::= variable-not-otherwise-mentioned) ;; Type variables
  (x y ::= variable-not-otherwise-mentioned) ;; Term variables
  (τ σ ::= α (→ τ τ) (∀ α τ) bool) ;; Types
  (b   ::= #t #f) ;; Booleans
  (e   ::= x (λ (x : τ) e) (e e) (Λ α e) (e [τ]) (let [x e] e) b (if e e e)) ;; Terms

  (Δ   ::= · (Δ α)) ;; Type contexts
  (Γ   ::= · (Γ (x : τ))) ;; Term contexts

  (v   ::= x (λ (x : τ) e) (Λ α e) #t #f) ;; Values
  (E   ::= hole (E e) (v E) (E [τ]) (let [x E] e) (if E e e)) ;; Evaluation contexts
  (F   ::= E (λ (x : τ) F) (Λ α F)) ;; Evaluation contexts (normalization)

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
   (λ* ([x : a]) x) (λ (x : a) x)
   (λ* (a) x) (Λ a x)
   (λ* ([x : a] b [z : c]) (x z)) (λ (x : a) (Λ b (λ (z : c) (x z))))
   (@ x) x
   (@ x [a] y) ((x [a]) y)
   (let* ([x (λ (x : a) x)]) x) (let [x (λ (x : a) x)] x)
   (let* ([x (λ (x : a) x)] [y x] [z y]) z) (let [x (λ (x : a) x)] (let [y x] (let [z y] z)))
   (→* a) a
   (→* a b c) (→ a (→ b c))
   (→* (→ a b) c) (→ (→ a b) c)
   (∀* (a) a) (∀ a a)
   (∀* (a b c) b) (∀ a (∀ b (∀ c b)))
   (Γ*) ·
   (Γ* (x : a) (y : b)) ((· (x : a)) (y : b))
   (Δ*) ·
   (Δ* a b) ((· a) b)))


;; Static Semantics

;; (x : τ) ∈ Γ
(define-judgement-form λF
  #:contract (∈Γ x τ Γ)
  #:mode (∈Γ I O I)

  [-------------------- "Γ-car"
   (∈Γ x τ (Γ (x : τ)))]

  [(∈Γ x τ Γ)
   ------------------------- "Γ-cdr"
   (∈Γ x τ (Γ (x_0 : σ)))])

;; α ∈ Δ
(define-judgement-form λF
  #:contract (∈Δ α Δ)
  #:mode (∈Δ I I)

  [------------- "Δ-car"
   (∈Δ α (Δ α))]

  [(∈Δ α Δ)
   --------------- "Δ-cdr"
   (∈Δ α (Δ α_0))])

(module+ test
  (redex-judgement-holds-chk
   ∈Γ
   [#:f x a ·]
   [#:f x a (· (y : a))]
   [#:f x b (· (x : a))]
   [x a (· (x : a))]
   [x (→ u w) (Γ* (y : a) (x : (→ u w)))])

  (redex-judgement-holds-chk
   ∈Δ
   [a (Δ* a b c)]
   [#:f a (· b)]))

;; Δ ⊢ τ
(define-judgement-form λF
  #:contract (⊢τ Δ τ)
  #:mode (⊢τ I I)

  [(∈Δ α Δ)
   --------- "τ-var"
   (⊢τ Δ α)]

  [(⊢τ Δ σ)
   (⊢τ Δ τ)
   --------------- "τ-arr"
   (⊢τ Δ (→ σ τ))]

  [(⊢τ (Δ α) τ)
   ---------------- "τ-forall"
   (⊢τ Δ (∀ α τ))]

  [------------ "τ-bool"
   (⊢τ Δ bool)])

(module+ test
  (redex-judgement-holds-chk
   ⊢τ
   [(· a) a]
   [(· a) (→ a a)]
   [(· a) (∀ a a)]
   [#:f (· b) a]))

;; Δ Γ ⊢ e : τ
(define-judgement-form λF
  #:contract (⊢ Δ Γ e τ)
  #:mode (⊢ I I I O)

  [(∈Γ x τ Γ)
   ------------ "var"
   (⊢ Δ Γ x τ)]

  [(⊢τ Δ σ)
   (⊢ Δ (Γ (x : σ)) e τ)
   ------------------------------ "fun"
   (⊢ Δ Γ (λ (x : σ) e) (→ σ τ))]

  [(⊢ Δ Γ e_2 σ)
   (⊢ Δ Γ e_1 (→ σ τ))
   -------------------- "app"
   (⊢ Δ Γ (e_1 e_2) τ)]

  [(⊢ (Δ α) Γ e τ)
   ------------------------- "polyfun"
   (⊢ Δ Γ (Λ α e) (∀ α τ))]

  [(⊢τ Δ σ)
   (⊢ Δ Γ e (∀ α τ))
   ----------------------------------- "polyapp"
   (⊢ Δ Γ (e [σ]) (substitute τ α σ))]

  [(⊢ Δ Γ e_x σ)
   (⊢ Δ (Γ (x : σ)) e τ)
   -------------------------- "let"
   (⊢ Δ Γ (let [x e_x] e) τ)]

  [--------------- "bool"
   (⊢ Δ Γ b bool)]

  [(⊢ Δ Γ e_0 bool)
   (⊢ Δ Γ e_1 τ)
   (⊢ Δ Γ e_2 τ)
   --------------------------- "if"
   (⊢ Δ Γ (if e_0 e_1 e_2) τ)])

;; Places where α is used to pattern-match to any type variable
;; to test for an alpha-equivalent type have been marked with ;; α
(module+ test  
  (redex-judgement-holds-chk
   (⊢ (Δ* a u) ·)
   [(λ (x : a) x) (→ a a)]
   [((λ (x : (→ a a)) x) (λ (x : a) x)) (→ a a)]
   [(Λ a (λ (x : a) x)) (∀ α (→ α α))] ;; α
   [((Λ a (λ (x : a) x)) [u]) (→ u u)]
   [((Λ a (λ (x : a) (Λ a (λ (y : a) x)))) [u])
    (→ u (∀ α (→ α u)))] ;; α
   [(let [x (Λ a (λ (y : a) y))] (@ x [(∀ a (→ a a))] x)) (∀ a (→ a a))]
   [#t bool]
   [#f bool]
   [(if ((λ (b : bool) b) #t) (λ (b : bool) b) (λ (b : bool) b)) (→ bool bool)]
   [(if #t (if #f #t #f) #f) bool]))

(define-metafunction λF
  infer : e -> τ
  [(infer e)
   τ (judgement-holds (⊢ · · e τ))])


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
        "ζ")
   (--> (if #t e_1 e_2)
        e_1
        "ιt")
   (--> (if #f e_1 e_2)
        e_2
        "ιf")))

;; Compatible closure of ⟶
(define ⟶*
  (context-closure ⟶ λF E))

;; Reflexive, transitive closure of ⟶*
(define-metafunction λF
  reduce : e -> v
  [(reduce e)
   ,(first (apply-reduction-relation* ⟶* (term e) #:cache-all? #t))])

;; We let ((x v) ... v) be a value as well
;; in order to reduce the inside of lambdas
(define-extended-language λF⇓ λF
  (app ::= x (app v) (app [τ]))
  (v ::= .... app))

;; Compatible closure of ⟶
;; including under lambdas
(define ⇓
  (context-closure ⟶ λF⇓ F))

;; Reflexive, transitive closure of ⇓
(define-metafunction λF⇓
  normalize : e -> v
  [(normalize e)
   ,(first (apply-reduction-relation* ⇓ (term e) #:cache-all? #t))])

(module+ test
  (test-->
   ⟶*
   (term ((λ (x : a) x) (λ (y : b) y)))
   (term (λ (y : b) y)))
  (test-->
   ⟶*
   (term ((Λ a (λ (x : a) x)) [(∀ b b)]))
   (term (λ (x : (∀ b b)) x)))
  (test-->
   ⟶*
   (term (let [x y] (x x)))
   (term (y y)))
  (test-->>
   ⟶*
   (term ((λ (b : bool) (if b #f #t)) #f))
   (term #t))
  (test-->>
   ⟶*
   (term ((λ (b : bool) (if b #f #t)) #t))
   (term #f))
  (test-->>
   ⟶*
   (term (@ (let [x (λ* (a [y : a]) y)]
              (@ x [(∀ a (→ a a))] x))
            [(∀ b (→ b b))]
            (λ (y : b) y)))
   (term (λ (y : b) y)))
  (test-->>
   ⇓
   (term (λ (x : a) ((λ (y : b) y) x)))
   (term (λ (x : a) x)))
  (test-->>
   ⇓
   (term (λ* ([x : a] [f : (→ a a)]) (let [y (f x)] y)))
   (term (λ* ([x : a] [f : (→ a a)]) (f x))))
  (test-->
   ⇓
   (term ((λ (x : a) x) (@ z [a] (λ (y : b) y))))
   (term (@ z [a] (λ (y : b) y)))))


;; Church Encoding

(define-metafunction λF
  number->term : number (λ (x : τ) (λ (x : τ) e)) -> e
  [(number->term 0 e) e]
  [(number->term number (λ (x_1 : τ_1) (λ (x_2 : τ_2) e)))
   (number->term ,(sub1 (term number)) (λ (x_1 : τ_1) (λ (x_2 : τ_2) (x_1 e))))])
(define-metafunction λF
  ♯ : number -> e
  [(♯ number) (Λ a (number->term number (λ* ([f : (→ a a)] [x : a]) x)))])

(define-term nat (∀ a (→* (→ a a) a a)))

(define-term succ
  (λ* ([n : nat] a [f : (→ a a)] [x : a])
      (f (@ n [a] f x))))

(define-term plus
  (λ* ([n : nat] [m : nat] a [f : (→ a a)] [x : a])
      (@ n [a] f (@ m [a] f x))))

;; putting this on hold, because I wanted to implement ANF, not go through the motions of Church encoding
;; I am satisfied knowing that the basic arithmetic operations are probably all typeable in System F
