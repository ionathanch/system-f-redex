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
   ----------------------------- "τ-fun"
   (↝τ (→ σ_s τ_s) (→ σ_t τ_t))]

  [(↝τ τ_s τ_t)
   ------------------------- "τ-poly"
   (↝τ (∀ α τ_s) (∀ α τ_t))]

  [--------------- "τ-bool"
   (↝τ bool bool)])

;; [k] ↝ Φ l
(define-judgement-form λH
  #:contract (↝k k Φ l)
  #:mode (↝k I O O)

  [(↝e e_s (p_e ...) e_t)
   (where l ,(variable-not-in (term (let (p_e ...) (Λ (α ...) ([x : τ] ...) β e))) 'l))
   (where p (l ↦ (α ...) ([x : τ] ...) (β : *) e_t))
   ---------------------------------------------------- "tcode"
   (↝k (Λ (α ...) ([x : τ] ...) β e_s) (p_e ... p) l)]

  [(↝e e_s (p_e ...) e_t)
   (where l ,(variable-not-in (term (let (p_e ...) (λ (α ...) ([x : τ] ...) (y : σ) e))) 'l))
   (where p (l ↦ (α ...) ([x : τ] ...) (y : σ) e_t))
   ---------------------------------------------------------- "vcode"
   (↝k (λ (α ...) ([x : τ] ...) (y : σ) e_s) (p_e ... p) l)])

;; [v] ↝ Φ v
(define-judgement-form λH
  #:contract (↝v v Φ v)
  #:mode (↝v I O O)

  [------------ "var"
   (↝v x () x)]

  [(↝k k Φ_k l)
   (↝τ σ_s σ_t) ...
   (↝v v_s Φ_v v_t) ...
   (where Φ (concat (Φ_k Φ_v ...)))
   --------------------------------------------------------------- "(poly)fun"
   (↝v (⟨ k [σ_s ...] (v_s ...) ⟩) Φ (⟨ l [σ_t ...] (v_t ...) ⟩))]

  [------------ "bool"
   (↝v b () b)])

;; [c] ↝ Φ c
(define-judgement-form λH
  #:contract (↝c c Φ c)
  #:mode (↝c I O O)

  [(↝v v_s Φ v_t)
   -------------- "val"
   (↝c v_s Φ v_t)]

  [(↝v v_1s (p_1 ...) v_1t)
   (↝v v_2s (p_2 ...) v_2t)
   ----------------------------------------------- "app"
   (↝c (v_1s v_2s) (p_1 ... p_2 ...) (v_1t v_2t))]

  [(↝τ σ_s σ_t)
   (↝v v_s Φ v_t)
   ------------------------------- "polyapp"
   (↝c (v_s [σ_s]) Φ (v_t [σ_t]))])

;; [e] ↝ Φ e
(define-judgement-form λH
  #:contract (↝e e Φ e)
  #:mode (↝e I O O)

  [(↝c c_s Φ c_t)
   --------------- "comp"
   (↝e c_s Φ c_t)]

  [(↝c c_s (p_c ...) c_t)
   (↝e e_s (p_e ...) e_t)
   ----------------------------------------------------------- "let"
   (↝e (let [x c_s] e_s) (p_c ... p_e ...) (let [x c_t] e_t))]

  [(↝v v_s (p_v ...) v_t)
   (↝e e_1s (p_e1 ...) e_1t)
   (↝e e_2s (p_e2 ...) e_2t)
   ----------------------------------------------------------------------- "if"
   (↝e (if v_s e_1s e_2s) (p_v ... p_e1 ... p_e2 ...) (if v_t e_1t e_2t))])


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

(module+ test
  (define-term id
    (⟨ (Λ () () a
          (⟨ (λ (a) () (x : a) x) [a] () ⟩))
       () () ⟩))

  (define-term const
    (⟨ (Λ () () a
          (⟨ (Λ (a) () b
                (⟨ (λ (a b) () (x : a)
                     (⟨ (λ (a b) ([x : a]) (y : b) x)
                        [a b] (x) ⟩))
                   [a b] () ⟩))
             [a] () ⟩))
       [] () ⟩))

  (define-term id-id-term
    (let* ([id-poly id]
           [id-forall (id-poly [(∀ a (→ a a))])]
           [id-id (id-forall id-poly)])
      id-id))

  (define-term id-H
    (let ([l0 ↦ (a) () (x : a) x]
          [l1 ↦ () () (a : *) (⟨ l0 [a] () ⟩)])
      (⟨ l1 () () ⟩)))

  (define-term const-H
    (let ([l0 ↦ (a b) ([x : a]) (y : b) x]
          [l1 ↦ (a b) () (x : a) (⟨ l0 [a b] (x) ⟩)]
          [l2 ↦ (a) () (b : *) (⟨ l1 [a b] () ⟩)]
          [l3 ↦ () () (a : *) (⟨ l2 [a] () ⟩)])
      (⟨ l3 () () ⟩)))

  (define-term id-id-term-H
    (let ([l0 ↦ (a) () (x : a) x]
          [l1 ↦ () () (a : *) (⟨ l0 [a] () ⟩)])
      (let* ([id-poly (⟨ l1 () () ⟩)]
             [id-forall (id-poly [(∀ a (→ a a))])]
             [id-id (id-forall id-poly)])
        id-id)))

  (define-term id-compiled
    (compile id))
  (define-term const-compiled
    (compile const))
  (define-term id-id-term-compiled
    (compile id-id-term))

  ;; See the Program Equality note in system-f-h.rkt for why
  ;; these tests lack a compiler correctness test

  (redex-chk
   #:eq id-compiled id-H
   #:eq (t.infer id-compiled) (compile-type (s.infer id)))

  (redex-chk
   #:eq const-compiled const-H
   #:eq (t.infer const-compiled) (compile-type (s.infer const)))

  (redex-chk
   #:eq id-id-term-compiled id-id-term-H
   #:eq (t.infer id-id-term-compiled) (compile-type (s.infer id-id-term))))


;; Other Metafunctions

(define-metafunction λH
  concat : ((p ...) ...) -> (p ...)
  [(concat ()) ()]
  [(concat ((p ...) any_r ...))
   (p ... p_r ...)
   (where (p_r ...) (concat (any_r ...)))])
