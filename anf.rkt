#lang racket

(require (prefix-in s. "./system-f.rkt")
         (prefix-in t. "./system-f-anf.rkt")
         (rename-in redex/reduction-semantics
                    [define-judgment-form          define-judgement-form]
                    [define-extended-judgment-form define-extended-judgement-form]
                    [judgment-holds                judgement-holds]))

(module+ test
  (require "./redex-chk.rkt"))

(provide compile)

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

;; Unroll (let* ([x_1 a_1] ... [x_n a_n]) e) into (let [x_1 a_1] ... (let [x_n a_n] e))
;; where (a ::= e hole)
(define-metafunction λANF
  let* : ([x any] ...) e -> any
  [(let* () e) e]
  [(let* ([x any] [x_r any_r] ...) e_body)
   (let [x any] (let* ([x_r any_r] ...) e_body))])

;; Unroll (τ_1 → ... → τ_n) into (τ_1 → (... → τ_n))
(define-metafunction/extension t.→* λANF
  →* : τ ... τ -> τ)

;; Unroll (∀* (α_1 ... a_n) τ) as (∀ α_1 ... (∀ α_n τ))
(define-metafunction/extension t.∀* λANF
  ∀* : (α ...) τ -> τ)


;; ANF Translation Judgement

;; Δ Γ ⊢ K : τ ⇒ τ
(define-extended-judgement-form λANF t.⊢K
  #:contract (⊢K Δ Γ K τ τ)
  #:mode (⊢K I I I I O))

;; (x : τ) ∈ Γ
(define-extended-judgement-form λANF t.∈Γ
  #:contract (∈Γ x τ Γ)
  #:mode (∈Γ I O I))

;; α ∈ Δ
(define-extended-judgement-form λANF t.∈Δ
  #:contract (∈Δ α Δ)
  #:mode (∈Δ I I))

;; Δ ⊢ [τ] ↝ τ
;; In ANF, this does nothing.
(define-judgement-form λANF
  #:contract (⊢τ Δ τ ↝ τ)
  #:mode (⊢τ I I I O)

  [(∈Δ α Δ)
   ------------- "τ-var"
   (⊢τ Δ α ↝ α)]

  [(⊢τ Δ σ_s ↝ σ_t)
   (⊢τ Δ τ_s ↝ τ_t)
   --------------------------------- "τ-fun"
   (⊢τ Δ (→ σ_s τ_s) ↝ (→ σ_t τ_t))]

  [(⊢τ (Δ α) τ_s ↝ τ_t)
   ----------------------------- "τ-poly"
   (⊢τ Δ (∀ α τ_s) ↝ (∀ α τ_t))]

  [------------------- "bool"
   (⊢τ Δ bool ↝ bool)])


;; Δ Γ ⊢ e : τ
;; This is a shorthand for getting the type of a term
(define-judgement-form λANF
  #:contract (⊢e Δ Γ e τ)
  #:mode (⊢e I I I O)

  [(⊢ Δ Γ e hole ↝ _ τ)
   ------------- "infer"
   (⊢e Δ Γ e τ)])

;; [e]K ↝ e
(define-judgement-form λANF
  #:contract (⊢ Δ Γ e K ↝ e τ)
  #:mode (⊢ I I I I I O O)

  ;; [x]K = K[x]
  [(∈Γ x σ Γ)
   (⊢K Δ Γ K σ τ)
   --------------------------------- "var"
   (⊢ Δ Γ x K ↝ (in-hole* K x) τ)]

  ;; [(λ (x : τ) e)]K = K[(λ (x : [τ]) [e])]
  [(⊢τ Δ σ_s ↝ σ_t)
   (⊢ Δ (Γ (x : σ_t)) e_s hole ↝ e_t τ_t)
   (⊢K Δ Γ K (→ σ_t τ_t) τ)
   --------------------------------------------------------------- "fun"
   (⊢ Δ Γ (λ (x : σ_s) e_s) K ↝ (in-hole* K (λ (x : σ_t) e_t)) τ)]

  ;; [(e_1 e_2)] = [e_1](let [x_1 ∘] [e_2](let [x_2 ∘] K[(x_1 x_2)]))
  [(where (x_1 x_2) ,(variables-not-in (term (K e_1s e_2s)) '(f y)))
   (where e (in-hole* K (x_1 x_2)))
   (where K_2 (let [x_2 hole] e))
   (⊢e Δ Γ e_1s σ)
   (⊢ Δ (Γ (x_1 : σ)) e_2s K_2 ↝ e_2t _)
   (where K_1 (let [x_1 hole] e_2t))
   (⊢ Δ Γ e_1s K_1 ↝ e_1t τ)
   ------------------------------- "app"
   (⊢ Δ Γ (e_1s e_2s) K ↝ e_1t τ)]

  ;; [(Λ α e)]K = K[(Λ α [e])]
  [(⊢ (Δ α) Γ e_s hole ↝ e_t σ)
   (⊢K Δ Γ K (∀ α σ) τ)
   ----------------------------------------------- "polyfun"
   (⊢ Δ Γ (Λ α e_s) K ↝ (in-hole* K (Λ α e_t)) τ)]

  ;; [(e [τ])]K = [e](let [x ∘] K[(x [[τ]])])
  [(⊢τ Δ σ_s ↝ σ_t)
   (where x ,(variable-not-in (term (K e_s)) 'f))
   (where e (in-hole* K (x [σ_t])))
   (where K_1 (let [x hole] e))
   (⊢ Δ Γ e_s K_1 ↝ e_t τ)
   ------------------------------ "polyapp"
   (⊢ Δ Γ (e_s [σ_s]) K ↝ e_t τ)]

  ;; [(let [x e_1] e_2)]K = [e_1](let [x ∘] [e_2]K)
  [(⊢e Δ Γ e_1s σ)
   (⊢ Δ (Γ (x : σ)) e_2s K ↝ e_2t _)
   (where K_1 (let [x hole] e_2t))
   (⊢ Δ Γ e_1s K_1 ↝ e_1t τ)
   --------------------------------------- "let"
   (⊢ Δ Γ (let [x e_1s] e_2s) K ↝ e_1t τ)]

  ;; [b]K = K[b]
  [(⊢K Δ Γ K bool τ)
   ------------------------------- "bool"
   (⊢ Δ Γ b K ↝ (in-hole* K b) τ)]

  ;; [(if e_0 e_1 e_2)]K =
  ;;   [e_0](let* ([x ∘]
  ;;               [f (λ (x : τ) K[x])])
  ;;          (if x [e_1](let [x ∘] (f x))
  ;;                [e_2](let [x ∘] (f x))))
  [(where (x_1 x_2) ,(variables-not-in (term (K (if e_0 e_1 e_2))) '(f y)))
   (where K_2 (let [x_2 hole] (x_1 x_2)))
   (⊢e Δ Γ e_1s σ_1)
   (⊢e Δ Γ e_2s σ_1)
   (⊢K Δ Γ K σ_1 σ_2)
   (⊢ Δ (Γ (x_1 : (→ σ_1 σ_2))) e_1s K_2 ↝ e_1t _)
   (⊢ Δ (Γ (x_1 : (→ σ_1 σ_2))) e_2s K_2 ↝ e_2t _)
   (where e_t (in-hole* (let [x_1 hole] (if x_2 e_1t e_2t))
                        (λ (x_2 : σ_1) (in-hole* K x_2))))
   (where K_1 (let [x_2 hole] e_t))
   (⊢ Δ Γ e_0s K_1 ↝ e_0t τ)
   --------------------------------------- "if"
   (⊢ Δ Γ (if e_0s e_1s e_2s) K ↝ e_0t τ)])


;; Compilation Convenience Metafunctions

(define-metafunction λANF
  compile : e -> e
  [(compile e)
   e_anf
   (judgement-holds (⊢ · · e hole ↝ e_anf _))])

(define-metafunction λANF
  compile-type : τ -> τ
  [(compile-type τ)
   τ_anf
   (judgement-holds (⊢τ · τ ↝ τ_anf))])

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

  (define-term boolean
    (∀ b (→* b b b)))
  (define-term true
    (λ* (a [x : a] [y : a]) x))
  (define-term false
    (λ* (a [x : a] [y : a]) y))
  (define-term if-bool
    (λ* (a [t : a] [f : a] [b : boolean]) (@ b [a] t f)))
  (define-term neg
    (@ if-bool [boolean] false true))

  (define-term neg-compiled
    (compile neg))

  (define-term if-bool-ANF
    (λ* (a [t : a] [f : a] [b : boolean])
        (let* ([ba (b [a])]
               [bat (ba t)])
          (bat f))))
  (define-term neg-ANF
    (let* ([ifb if-bool-ANF]
           [ifbb (ifb [boolean])]
           [f false]
           [ifbbf (ifbb f)]
           [t true])
      (ifbbf t)))

  (redex-chk
   #:eq neg-compiled neg-ANF
   #:eq (t.infer neg-compiled) (compile-type (s.infer neg))
   #:eq (t.normalize neg-compiled) (t.normalize (compile (s.normalize neg))))

  (define-term not
    (λ (b : bool)
      ((λ (x : bool) x)
       (if ((λ (x : bool) x) b)
           (let [bb #f] bb)
           (let [bb #t] bb)))))

  (define-term not-compiled
    (compile not))

  (define-term not-ANF
    (λ (b : bool)
      (let* ([id (λ (x : bool) x)]
             [f1 (λ (x : bool) x)]
             [y1 (f1 b)])
        (if y1
            (let [bb #f]
              (id bb))
            (let [bb #t]
              (id bb))))))

  (redex-chk
   #:eq not-compiled not-ANF
   #:eq (t.infer not-compiled) (compile-type (s.infer not))
   #:eq (t.normalize not-compiled) (t.normalize (compile (s.normalize not))))

  #;(for ([_ (range 10)])
      (redex-let*
       λANF
       ([(⊢ · · e_F τ_F) (generate-term s.λF #:satisfying (s.⊢ · · e τ) 10)] ;; source term and its type
        [e_ANF (term (compile e_F))] ;; compiled term
        [τ_compiled (term (compile-type τ_F))] ;; compiled type
        [τ_ANF (term (t.infer e_ANF))] ;; type of compiled term
        [v_F (term (s.normalize e_F))]
        [v_ANF (term (t.normalize e_ANF))])
       (redex-chk
        #:eq τ_compiled τ_ANF ;; · · ⊢ e : τ ⇒ · · ⊢ [e] : [τ]
        #:eq v_F v_ANF))))


;; Other Metafunctions

(define-metafunction t.λF-ANF
  in-hole* : K c -> e
  ;; (let [x y] e) --> e[y/x] [ζ-reduction, eliminate var-var bindings]
  [(in-hole* (let [x_1 hole] e) x_2)
   (substitute e x_1 x_2)]
  ;; (let [x c] x) --> c [ζ-reduction, eliminate var body bindings]
  [(in-hole* (let [x hole] x) c) c]
  ;; (let [f (λ (x : τ) (v x))] e) --> (let [f v] e) [η-reduction]
  [(in-hole* (let [x_1 hole] e) (λ (x_2 : _) (v x_2)))
   (in-hole* (let [x_1 hole] e) v)]
  ;; (let [x c] e) --> (let [x c] e)
  [(in-hole* K c) (in-hole K c)])
