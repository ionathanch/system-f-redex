#lang racket

(require (prefix-in s. "./system-f.rkt")
         (prefix-in t. "./system-f-anf.rkt")
         (rename-in redex/reduction-semantics
                    [define-judgment-form define-judgement-form]
                    [judgment-holds       judgement-holds]))

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

;; [τ] ↝ τ
;; In ANF, this does nothing.
(define-judgement-form λANF
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

  [---------------- "bool"
   (↝τ bool bool)])

;; [e]K ↝ e
(define-judgement-form λANF
  #:contract (↝ e K e)
  #:mode (↝ I I O)

  ;; [x]K = K[x]
  [---------------------- "var"
   (↝ x K (in-hole* K x))]

  ;; [(λ (x : τ) e)]K = K[(λ (x : [τ]) [e])]
  [(↝τ τ_s τ_t)
   (↝ e_s hole e_t)
   ------------------------------------------------------ "fun"
   (↝ (λ (x : τ_s) e_s) K (in-hole* K (λ (x : τ_t) e_t)))]

  ;; [(e_1 e_2)] = [e_1](let [x_1 ∘] [e_2](let [x_2 ∘] K[(x_1 x_2)]))
  [(where (x_1 x_2) ,(variables-not-in (term (K e_1s e_2s)) '(f y)))
   (where e (in-hole* K (x_1 x_2)))
   (where K_2 (let [x_2 hole] e))
   (↝ e_2s K_2 e_2t)
   (where K_1 (let [x_1 hole] e_2t))
   (↝ e_1s K_1 e_1t)
   ----------------------- "app"
   (↝ (e_1s e_2s) K e_1t)]

  ;; [(Λ α e)]K = K[(Λ α [e])]
  [(↝ e_s hole e_t)
   -------------------------------------- "polyfun"
   (↝ (Λ α e_s) K (in-hole* K (Λ α e_t)))]

  ;; [(e [τ])]K = [e](let [x ∘] K[(x [[τ]])])
  [(↝τ τ_s τ_t)
   (where x ,(variable-not-in (term (K e_s)) 'f))
   (where e (in-hole* K (x [τ_t])))
   (where K_1 (let [x hole] e))
   (↝ e_s K_1 e_t)
   ---------------------- "polyapp"
   (↝ (e_s [τ_s]) K e_t)]

  ;; [(let [x e_1] e_2)]K = [e_1](let [x ∘] [e_2]K)
  [(↝ e_2s K e_2t)
   (where K_1 (let [x hole] e_2t))
   (↝ e_1s K_1 e_1t)
   ------------------------------- "let"
   (↝ (let [x e_1s] e_2s) K e_1t)]

  ;; [b]K = K[b]
  [----------------------- "bool"
   (↝ b K (in-hole* K b))]

  ;; [(if e_0 e_1 e_2)]K = [e_0](let [x ∘] (if x [e_1]K [e_2]K))
  [(↝ e_1s K e_1t)
   (↝ e_2s K e_2t)
   (where x ,(variable-not-in (term (K (if e_0 e_1 e_2))) 'y))
   (where K_0 (let [x hole] (if x e_1t e_2t)))
   (↝ e_0s K_0 e_0t)
   -------------------------------- "if"
   (↝ (if e_0s e_1s e_2s) K e_0t)])


;; Compilation Convenience Metafunctions

(define-metafunction λANF
  compile : e -> e
  [(compile e)
   e_anf
   (judgement-holds (↝ e hole e_anf))])

(define-metafunction λANF
  compile-type : τ -> τ
  [(compile-type τ)
   τ_anf
   (judgement-holds (↝τ τ τ_anf))])

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
  [(in-hole* (let [x_1 hole] e) x_2)
   (substitute e x_1 x_2)]
  [(in-hole* (let [x hole] x) c) c]
  [(in-hole* K c) (in-hole K c)])
