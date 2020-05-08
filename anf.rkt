#lang racket

(require (prefix-in s. "./system-f.rkt")
         (prefix-in t. "./system-f-anf.rkt")
         (rename-in redex/reduction-semantics
                    [define-judgment-form define-judgement-form]
                    [judgment-holds       judgement-holds]))

(module+ test
  (require "./redex-chk.rkt"))

;; A-NORMAL FORM TRANSLATION ;;

(define-union-language λANF s.λF t.λF-ANF)
(default-language λANF)

;; Unroll (λ* (a_1 ... a_n) e) into (L a_1 ... (L a_n e))
;; where (L ::= λ Λ) (a ::= [x : τ] α)
(define-metafunction/extension t.λ* λANF
  λ* : (any ...) e -> e)

;; Unroll (@ e a_1 ... a_n) into ((e a_1) ... a_n)
;; where (a ::= e [τ])
(define-metafunction/extension t.@ λANF
  @ : any ... -> e)

;; Unroll (let* ([x_1 e_1] ... [x_n e_n]) e) into (let [x_1 e_1] ... (let [x_n e_n] e))
(define-metafunction/extension t.let* λANF
  let* : ([x e] ...) e -> e)

;; Unroll (τ_1 → ... → τ_n) into (τ_1 → (... → τ_n))
(define-metafunction/extension t.→* λANF
  →* : τ ... τ -> τ)

;; Unroll (∀* (α_1 ... a_n) τ) as (∀ α_1 ... (∀ α_n τ))
(define-metafunction/extension t.∀* λANF
  ∀* : (α ...) τ -> τ)


;; ANF Translation Judgement

;; [τ] ↦ τ
;; In ANF, this does nothing.
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


;; Compilation Convenience Metafunctions

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

(define-metafunction λANF
  compile-type : τ -> τ
  [(compile-type τ)
   τ_anf
   (judgement-holds (↦τ τ τ_anf))])

(module+ test
  (define-term id-id
    (@ (λ* (a [x : a]) x)
       [(∀ b (→ b b))]
       (λ* (a [x : a]) x)))

  (define-term id-id-ANF
    (let* ([u (Λ a (λ (x : a) x))]
           [v (u [(∀ b (→ b b))])]
           [w (Λ a (λ (x : a) x))])
      (v w)))

  (define-term id-id-compiled
    (compile id-id))

  (redex-chk
   #:eq id-id-compiled id-id-ANF
   #:eq (t.infer id-id-compiled) (compile-type (s.infer id-id))
   #:eq (t.normalize id-id-compiled) (s.normalize id-id))

  (define-term bool
    (∀ b (→* b b b)))
  (define-term true
    (λ* (a [x : a] [y : a]) x))
  (define-term false
    (λ* (a [x : a] [y : a]) y))
  (define-term if-bool
    (λ* (a [t : a] [f : a] [b : bool]) (@ b [a] t f)))
  (define-term neg
    (@ if-bool [bool] false true))

  (define-term neg-compiled
    (compile neg))

  (define-term if-bool-ANF
    (λ* (a [t : a] [f : a] [b : bool])
        (let* ([ba (b [a])]
               [bat (ba t)])
          (bat f))))
  (define-term neg-ANF
    (let* ([ifb if-bool-ANF]
           [ifbb (ifb [bool])]
           [f false]
           [ifbbf (ifbb f)]
           [t true])
      (ifbbf t)))

  (redex-chk
   #:eq neg-compiled neg-ANF
   #:eq (t.infer neg-compiled) (compile-type (s.infer neg))
   #:eq (t.normalize neg-compiled) (s.normalize neg))

  #;(for ([_ (range 10)])
    (redex-let* λANF
      ([(⊢ · · e_F τ_F) (generate-term s.λF #:satisfying (s.⊢ · · e τ) 10)] ;; source term and its type
       [e_ANF (term (compile e_F))] ;; compiled term
       [τ_compiled (term (compile-type τ_F))] ;; compiled type
       [τ_ANF (term (t.infer e_ANF))] ;; type of compiled term
       [v_F (term (s.normalize e_F))]
       [v_ANF (term (t.normalize e_ANF))])
      (redex-chk
       #:eq τ_compiled τ_ANF ;; · · ⊢ e : τ ⇒ · · ⊢ [e] : [τ]
       #:eq v_F v_ANF))))
