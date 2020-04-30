#lang racket

(require (for-syntax racket/syntax
                     redex/reduction-semantics)
         (rename-in redex/reduction-semantics
                    [define-judgment-form          define-judgement-form]
                    [define-extended-judgment-form define-extended-judgement-form]
                    [judgment-holds                judgement-holds]))

(module+ test
  (require "./redex-chk.rkt"))

;; Before we Begin...

;; (reductions name context)
;; Generates the following:
;; * `name`⟶*: The contextual closure of `name`⟶ using `context`
;; * step-`name`: A metafunction for applying `name`⟶*
;; * reduce-`name`: A metafunction for the transitive closure of `name`⟶*
(define-syntax (reductions stx)
  (syntax-case stx ()
    [(_ name context)
     (with-syntax ([lang (format-id #'name "λ~a" #'name)]
                   [⟶ (format-id #'name "~a⟶" #'name)]
                   [⟶* (format-id #'name "~a⟶*" #'name)]
                   [step (format-id #'name "step-~a" #'name)]
                   [reduce (format-id #'name "reduce-~a" #'name)]
                   [ellipses (quote-syntax ...)])
       #'(begin
           (define ⟶*
             (context-closure ⟶ lang context))

           (define-metafunction lang
             step : e -> (e ellipses)
             [(step e)
              ,(apply-reduction-relation ⟶* (term e))])

           (define-metafunction lang
             reduce : e -> v
             [(reduce e)
              ,(first (apply-reduction-relation* ⟶* (term e)))])))]))


;; A Handy Chart of Reduction Strategies
;; Based on this paper: https://www.itu.dk/~sestoft/papers/sestoft-lamreduce.pdf
;; DOI: https://doi.org/10.1016/S1571-0661(04)80973-3

;; RUL: reduce under lambdas?
;; RFF: reduce functions fully before application?
;; RAF: reduce arguments fully before application?
;; Type | RUL | RFF | RAF
;; CBN  | N   | N   | N
;; CBV  | N   | N   | Y
;; HS   | N   | Y   | N
;; NO   | Y   | N   | N
;; HAO  | Y   | N   | Y
;; HNO  | Y   | Y   | N
;; AO   | *   | Y   | Y
;; * For applicative order, it doesn't matter if we reduce under lambdas
;;   because the function and the argument have both been reduced fully,
;;   so after application lambdas are already in normal form.


;; Untyped Lambda Calculus

(define-language λ
  (x ::= variable-not-otherwise-mentioned)
  (e ::= x (λ x e) (e e))

  #:binding-forms
  (λ x e #:refers-to x))

(default-language λ)

(define-term t
  ((λ x (λ y ((x y) x)))
   ((λ x x) (λ x x))))
(define-term u
  ((λ x ((λ y y) x)) (λ z ((λ y y) z))))


;; Call By Name
;; Reduces to weak head normal form
;; whnf ::= x | λx.e | (x e ...)
;; Reduction: (λx.e)e' --> e[e'/x]

(define-extended-language λCBN λ
  (E ::= hole (E e))
  (a ::= x (a e))
  (v ::= (λ x e) a))

(define CBN⟶
  (reduction-relation
   λCBN
   (--> ((λ x e_1) e_2)
        (substitute e_1 x e_2)
        "β")))

(reductions CBN E)

(test-->>
 CBN⟶*
 (term t)
 (term (λ y ((((λ x x) (λ x x)) y) ((λ x x) (λ x x))))))


;; Call By Value
;; Reduces closed terms to weak normal form
;; wnf ::= x | λx.e | (x wnf ...)
;; Reduction: (λx.e)v --> e[v/x]

(define-extended-language λCBV λ
  (E ::= hole (E e) (v E))
  (a ::= x (a v))
  (v ::= (λ x e) a))

(define CBV⟶
  (reduction-relation
   λCBV
   (--> ((λ x e) v)
        (substitute e x v)
        "β")))

(reductions CBV E)

(test-->>
 CBV⟶*
 (term t)
 (term (λ y (((λ x x) y) (λ x x)))))


;; Head Spine
;; Reduces closed terms to head normal form
;; hnf ::= x | λx.hnf | (x e ...)
;; Reduction: (λx.v)e --> v[e/x]

(define-extended-language λHS λ
  (E ::= hole (E e) (λ x E))
  (a ::= x (a e))
  (v ::= (λ x v) a))

(define HS⟶
  (reduction-relation
   λHS
   (--> ((λ x v) e)
        (substitute v x e)
        "β")))

(reductions HS E)

(test-->>
 HS⟶*
 (term t)
 (term (λ y (y ((λ x x) (λ x x))))))


;; Applicative Order
;; Reduces to normal form
;; nf ::= x | λx.nf | (x nf ...)
;; Reduction: (λx.v)v' --> v[v'/x]

(define-extended-language λAO λ
  (E ::= hole (E e) (v E) (λ x E))
  (a ::= x (a v))
  (v ::= (λ x v) a))

(define AO⟶
  (reduction-relation
   λAO
   (--> ((λ x v_1) v_2)
        (substitute v_1 x v_2)
        "β")))

(reductions AO E)

(test-->>
 AO⟶*
 (term t)
 (term (λ y (y (λ x x)))))


;; Normal Order
;; Reduces to NF
;; CBN, but also reduce under lambdas
;; In other words: reduce application, then reduce under lambdas

(define-extended-language λNO λ
  (F ::= hole (F e))
  (E ::= F (λ x E) (a E))
  (a ::= x (a v))
  (v ::= (λ x v) a))

(define NO⟶
  (reduction-relation
   λNO
   (--> ((λ x e_1) e_2)
        (substitute e_1 x e_2)
        "β")))

(reductions NO E)

(test-->>
 NO⟶*
 (term t)
 (term (λ y (y (λ x x)))))

(test-->
 NO⟶*
 (term u)
 (term ((λ y y) (λ z ((λ y y) z)))))

(test-->
 NO⟶*
 (term ((λ y y) (λ z ((λ y y) z))))
 (term (λ z ((λ y y) z))))


;; Hybrid Applicative Order
;; Reduces to NF
;; CBV, but also reduce under lambdas
;; In other words: reduce argument, reduce application, then reduce under lambdas

(define-extended-language λHAO λ
  (F ::= hole (F e))
  (E ::= F (λ x E) (w E))
  (a ::= x (a v))
  (v ::= (λ x v) a)
  ;; When evaluating, leave lambdas alone on the LHS
  (b ::= x (b v))
  (w ::= (λ x e) b))

(define HAO⟶
  (reduction-relation
   λHAO
   (--> ((λ x e) v)
        (substitute e x v)
        "β")))

(reductions HAO E)

(test-->>
 HAO⟶*
 (term t)
 (term (λ y (y (λ x x)))))

(test-->
 HAO⟶*
 (term u)
 (term ((λ x ((λ y y) x)) (λ z z))))

(test-->
 HAO⟶*
 (term ((λ x ((λ y y) x)) (λ z z)))
 (term ((λ y y) (λ z z))))


;; Hybrid Normal Order
;; Reduces to NF
;; HS, but also reduce under lambdas
;; In other words: reduce function, reduce application, then reduce under lambdas

(define-extended-language λHNO λ
  (F ::= hole (λ x F) (F e))
  (E ::= F (λ x E) (a E))
  (a ::= x (a v))
  (v ::= (λ x v) a)
  ;; When evaluating, leave applications alone on the LHS
  (b ::= x (b e))
  (w ::= (λ x w) b))

(define HNO⟶
  (reduction-relation
   λHNO
   (--> ((λ x w) e)
        (substitute w x e)
        "β")))

(reductions HNO E)

(test-->>
 HNO⟶*
 (term t)
 (term (λ y (y (λ x x)))))

(test-->
 HNO⟶*
 (term u)
 (term ((λ x x) (λ z ((λ y y) z)))))

(test-->
 HNO⟶*
 (term ((λ x x) (λ z ((λ y y) z))))
 (term (λ z ((λ y y) z))))
