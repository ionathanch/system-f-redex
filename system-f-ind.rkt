#lang racket

(require (rename-in redex/reduction-semantics
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
  (c d ::= variable-not-otherwise-mentioned) ;; Inductive type/constructor names
  (τ σ ::= α (→ τ τ) (∀ α τ) (d τ ...)) ;; Types
  (e   ::= x c
       (λ (x : τ) e) (e e)
       (Λ α e) (e [τ])
       (let [x e] e)
       (case e ([c ⇒ e] ...))) ;; Terms

  ;; Inductive signatures:
  ;; - Δ are the type parameters
  ;; - Γ are the constructors
  (Σ   ::= ((d Δ := Γ) ...))

  (Δ   ::= (α ...)) ;; Type contexts
  (Γ   ::= ((x : τ) ...)) ;; Term contexts

  (v   ::= x (λ (x : τ) e) (Λ α e) #t #f) ;; Values
  (E   ::= hole (E e) (v E) (E [τ]) (let [x E] e) (case E ([c ⇒ e] ...))) ;; Evaluation contexts
  (F   ::= E (λ (x : τ) F) (Λ α F)) ;; Evaluation contexts (normalization)

  #:binding-forms
  (λ (x : τ) e #:refers-to x)
  (Λ α e #:refers-to α)
  (∀ α τ #:refers-to α)
  (let [x e_1] e_2 #:refers-to x)
  #;(d (α ...) := Γ #:refers-to (shadow d α ...)))

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

;; A signature with some common inductive definitions
(define-term Sig
  ((Bottom () := ())
   (Unit () := ((unit : Unit)))
   (Nat () := ((Zero : Nat)
               (Succ : (→ Nat Nat))))
   (Option (a) := ((None : (∀ a (Option a)))
                   (Some : (∀ a (→ a (Option a))))))
   (List (a) := ((Nil : (∀ a (List a)))
                 (Cons : (∀ a (→* a (List a) (List a))))))
   (Either (a b) := ((Left : (∀* (a b) (→ a (Either a b))))
                     (Right : (∀* (a b) (→ b (Either a b))))))))

(module+ test
  (redex-chk
   #:lang λF
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
   #:m Γ ()
   #:m Γ ((x : a) (y : b))
   #:m Δ ()
   #:m Δ (a b)
   #:m Σ Sig))


;; Static Semantics

;; (c : τ) ∈ Γ where (d Δ := Γ) ∈ Σ
(define-judgement-form λF
  #:contract (c∈Σ c τ Σ)
  #:mode (c∈Σ I O I)

  [(where (_ ... (c : τ) _ ...) Γ)
   -------------------------------------------- "c∈Σ"
   (c∈Σ c τ (_ ... (d Δ := Γ) _ ...))])

;; (d Δ := Γ) ∈ Σ
(define-judgement-form λF
  #:contract (d∈Σ d Δ Γ Σ)
  #:mode (d∈Σ I O O I)

  [------------------------------------ "∈Σ"
   (d∈Σ d Δ Γ (_ ... (d Δ := Γ) _ ...))])

;; (x : τ) ∈ Γ
(define-judgement-form λF
  #:contract (∈Γ x τ Γ)
  #:mode (∈Γ I O I)

  [------------------------------- "∈Γ"
   (∈Γ x τ (_ ... (x : τ) _ ...))])

;; α ∈ Δ
(define-judgement-form λF
  #:contract (∈Δ α Δ)
  #:mode (∈Δ I I)

  [----------------------- "∈Δ"
   (∈Δ α (_ ... α _ ...))])

(module+ test
  (redex-judgement-holds-chk
   c∈Σ
   [#:f Zero Nat ()]
   [Zero Nat Sig]
   [Nil (∀ a (List a)) Sig]
   [Cons (∀ a (→ a (→ (List a) (List a)))) Sig])
  
  (redex-judgement-holds-chk
   d∈Σ
   [#:f False () () ()]
   [#:f False () () ((Empty () := ()))]
   [False () () ((False () := ()))]
   [Nat () ((Zero : Nat) (Succ : (→ Nat Nat))) Sig]
   [List (a) ((Nil : (∀ a (List a)))
              (Cons : (∀ a (→ a (→ (List a) (List a)))))) Sig])

  (redex-judgement-equals-chk
   (d∈Σ)
   [List Δ Γ Sig
         #:pat (Δ Γ)
         #:term ((a)
                 ((Nil : (∀ a (List a)))
                  (Cons : (∀ a (→* a (List a) (List a))))))]
   [Either Δ Γ Sig
           #:pat (Δ Γ)
           #:term ((a b)
                   ((Left : (∀* (a b) (→ a (Either a b))))
                    (Right : (∀* (a b) (→ b (Either a b))))))])
  
  (redex-judgement-holds-chk
   ∈Γ
   [#:f x a ()]
   [#:f x a ((y : a))]
   [#:f x b ((x : a))]
   [x a ((x : a))]
   [x (→ u w) ((y : a) (x : (→ u w)))])

  (redex-judgement-holds-chk
   ∈Δ
   [a (a b c)]
   [#:f a (b)]))

;; Σ Δ ⊢ τ
(define-judgement-form λF
  #:contract (⊢τ Σ Δ τ)
  #:mode (⊢τ I I I)

  [(∈Δ α Δ)
   --------- "τ-var"
   (⊢τ Σ Δ α)]

  [(⊢τ Σ Δ σ)
   (⊢τ Σ Δ τ)
   --------------- "τ-arr"
   (⊢τ Σ Δ (→ σ τ))]

  [(⊢τ Σ (β ... α) τ)
   ---------------- "τ-forall"
   (⊢τ Σ (β ...) (∀ α τ))]

  [(d∈Σ d (σ ..._0) _ Σ)
   (⊢τ Σ Δ τ) ...
   ----------------- "τ-ind"
   (⊢τ Σ Δ (d τ ..._0))])

(module+ test
  (redex-judgement-holds-chk
   (⊢τ Sig)
   [(a) a]
   [(a) (→ a a)]
   [(a) (∀ a a)]
   [#:f (b) a]
   [(a) (List a)]
   [(a b) (Either b a)]))

;; Given (splay a (e ...)), return a repeated (length (e ...)) times.
(define-metafunction λF
  splay : any (any ...) -> (any ...)
  [(splay any ()) ()]
  [(splay any (any_hd any_tl ...))
   (any any_s ...)
   (where (any_s ...) (splay any (any_tl ...)))])

;; Given (join a ...), return a if all the a's are the same.
(define-metafunction λF
  join : any ... -> any
  [(join any) any]
  [(join any any any_r ...)
   (join any any_r ...)])

(module+ test
  (redex-chk
   #:= (splay d ()) ()
   #:= (splay d (a b c d e)) (d d d d d)
   #:= (join a) a
   #:= (join a a a a) a))

;; TODO: Return the branch type,
;; i.e. σ_c but with parameters σ_d applied
;; and with τ as the return type.
(define-metafunction λF
  branch-type : c σ d (σ ...) τ -> τ
  [(branch-type c σ_c d (σ_d ...) τ) τ])

;; Δ Γ ⊢ e : τ
(define-judgement-form λF
  #:contract (⊢ Σ Δ Γ e τ)
  #:mode (⊢ I I I I O)

  [(∈Γ x τ Γ)
   -------------- "var"
   (⊢ Σ Δ Γ x τ)]

  [(⊢τ Σ Δ σ)
   (where ((x_0 : σ_0) ...) Γ)
   (⊢ Σ Δ ((x_0 : σ_0) ... (x : σ)) e τ)
   -------------------------------- "fun"
   (⊢ Σ Δ Γ (λ (x : σ) e) (→ σ τ))]

  [(⊢ Σ Δ Γ e_2 σ)
   (⊢ Σ Δ Γ e_1 (→ σ τ))
   ---------------------- "app"
   (⊢ Σ Δ Γ (e_1 e_2) τ)]

  [(⊢ Σ (β ... α) Γ e τ)
   -------------------------------- "polyfun"
   (⊢ Σ (β ...) Γ (Λ α e) (∀ α τ))]

  [(⊢τ Σ Δ σ)
   (⊢ Σ Δ Γ e (∀ α τ))
   ------------------------------------- "polyapp"
   (⊢ Σ Δ Γ (e [σ]) (substitute τ α σ))]

  [(⊢ Σ Δ Γ e_x σ)
   (where ((x_0 : σ_0) ...) Γ)
   (⊢ Σ Δ ((x_0 : σ_0) ... (x : σ)) e τ)
   ---------------------------- "let"
   (⊢ Σ Δ Γ (let [x e_x] e) τ)]

  [(c∈Σ c τ Σ)
   -------------- "constr"
   (⊢ Σ Δ Γ c τ)]

  [(⊢ Σ Δ Γ e (d σ ...))
   (d∈Σ d Δ_d Γ_d Σ)
   (where ((c_d : _) ...) Γ_d)
   (where ((_ ... (c : σ_c) _ ...) ...) (splay Γ_d (c ...))) ;; All branches are valid
   (where ((_ ... c_d _ ...) ...) (splay (c ...) Γ_d)) ;; All branches are covered
   (where ((d_c σ_d ...) ...) (splay (d σ ...) (c ...)))
   (⊢ Σ Δ Γ e_c (branch-type c σ_c d_c (σ_d ...) τ_c)) ...
   (where τ (join τ_c ...))
   ------------------------------------- "case"
   (⊢ Σ Δ Γ (case e ([c ⇒ e_c] ...)) τ)])

;; Places where α is used to pattern-match to any type variable
;; to test for an alpha-equivalent type have been marked with ;; α
(module+ test  
  (redex-judgement-holds-chk
   (⊢ Sig (Δ* a u) ())
   [(λ (x : a) x) (→ a a)]
   [((λ (x : (→ a a)) x) (λ (x : a) x)) (→ a a)]
   [(Λ a (λ (x : a) x)) (∀ α (→ α α))] ;; α
   [((Λ a (λ (x : a) x)) [u]) (→ u u)]
   [((Λ a (λ (x : a) (Λ a (λ (y : a) x)))) [u])
    (→ u (∀ α (→ α u)))] ;; α
   [(let [x (Λ a (λ (y : a) y))] (@ x [(∀ a (→ a a))] x)) (∀ a (→ a a))]
   [Cons (∀ a (→ a (→ (List a) (List a))))]))

(define-metafunction λF
  infer : Σ e -> τ
  [(infer Σ e)
   τ (judgement-holds (⊢ Σ · · e τ))])


;; Dynamic Semantics

(define ⟶
  (reduction-relation
   λF
   (--> ((λ (x : τ) e) v)
        (substitute e x v)
        "β")
   (--> ((Λ α e) [τ])
        (substitute e α τ)
        "τ")
   (--> (let [x v] e)
        (substitute e x v)
        "ζ")
   ;; TODO: Figure out how to identify and extract fully-applied constructors
   #;(--> (case () (_ ... [c ⇒ e] _ ...))
        ()
        "ι")))

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
