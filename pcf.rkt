#lang racket
(require redex)

(define-language pcf
  (eτ n fτ x (λ (x τ) eτ) (eτ eτ))
  (e0 n f x)
  (e   e0 (λ x e) (e e))
  (e/x e0 ski (app e/x e/x) ⊥) ; e expanded (app = "apply" from paper (mostly))
  (ski S K I)
  (e+ski e ski)
  (fnoY add1 sub1 if0)
  (f fnoY Y)
  (f+ski f ski)
  (e0+f+ski e0 f+ski)
  (fτ fnoY (Y τ))
  (n natural)
  (x variable-not-otherwise-mentioned)
  
  (τ nat (τ → τ))
  (Γ ([x τ]...))
  
  (pa (ε f+ski any ...)) ; partial application
  (f+pa f+ski pa)
  (e+pa e pa)
  (e+tmp-apply e (apply* e+tmp-apply e+tmp-apply))
  )

(define-judgment-form pcf
  #:mode (typeof I I O)
  #:contract (typeof Γ eτ τ)
  [(typeof Γ n nat)]
  [(typeof Γ add1 (nat → nat))]
  [(typeof Γ sub1 (nat → nat))]
  #;[(typeof Γ e_1 nat)
   (typeof Γ e_2 τ)
   (typeof Γ e_3 τ)
   ------------------------------
   (typeof Γ (if0 e_1 e_2 e_3) τ)]
  [(typeof Γ if0 (nat → (nat → (nat → nat))))]
  [(typeof Γ (Y τ) ((τ → τ) → τ))]
  [(typeof Γ eτ (τ → τ))
   --------------------
   (typeof Γ (Y eτ) τ)]
  [(where τ (lookup Γ x))
   ----------------------
   (typeof Γ x τ)]
  [(typeof Γ eτ_1 (τ_2 → τ))
   (typeof Γ eτ_2 τ_2)
   ------------------------
   (typeof Γ (eτ_1 eτ_2) τ)]
  [(typeof (extend Γ x τ_1) eτ τ_2)
   ------------------------------------
   (typeof Γ (λ (x τ_1) eτ) (τ_1 → τ_2))])

(define-metafunction pcf
  extend : Γ x τ -> Γ
  [(extend ([x_0 τ_0] ... [x_i τ_i] [x_i+1 τ_i+1] ...) x_i τ)
   ([x_0 τ_0] ... [x_i τ] [x_i+1 τ_i+1] ...)]
  [(extend ([x_1 τ_1] ...) x_0 τ_0)
   ([x_0 τ_0] [x_1 τ_1] ...)])

(define-metafunction pcf
  lookup : Γ x -> τ
  [(lookup ([x_0 τ_0] ... [x_i τ_i] [x_i+1 τ_i+1] ...) x_i) 
   τ_i])

(define left+fn
  (term (λ (+ (nat → (nat → nat))) 
          (λ (x nat) (λ (y nat) (((if0 x) y) (add1 ((+ (sub1 x)) y))))))))
(define right+fn
  (term (λ (+ (nat → (nat → nat))) 
          (λ (x nat) (λ (y nat) (((if0 y) x) (add1 ((+ x) (sub1 y)))))))))
(define left+  (term ((Y (nat → (nat → nat))) ,left+fn)))
(define right+ (term ((Y (nat → (nat → nat))) ,right+fn)))

(define Ω (term ((Y nat) (λ (x nat) x))))

(test-equal (not (redex-match pcf eτ left+)) false)
(test-equal (not (redex-match pcf eτ right+)) false)
(test-equal (judgment-holds (typeof () ,left+ τ) τ) (term ((nat → (nat → nat)))))
(test-equal (judgment-holds (typeof () ,right+ τ) τ) (term ((nat → (nat → nat)))))

(test-equal (judgment-holds (typeof () ,Ω τ) τ) (term (nat)))


(define-metafunction pcf
  no-τ : eτ -> e
  [(no-τ x) x]
  [(no-τ (Y τ)) Y]
  [(no-τ fτ) fτ]
  [(no-τ (λ (x τ) eτ)) (λ x (no-τ eτ))]
  [(no-τ (eτ_1 eτ_2)) ((no-τ eτ_1) (no-τ eτ_2))])

(test-equal (not (redex-match pcf e (term (no-τ ,left+)))) false)
(test-equal (not (redex-match pcf e (term (no-τ ,right+)))) false)



(define (fv-e t)
  (define fvs null)
  (define (add! x) (set! fvs (cons x fvs)))
  (define-metafunction pcf
    fv_ : e -> any ; void
    [(fv_ x) ,(add! (term x))]
    [(fv_ n) ,(void)]
    [(fv_ f) ,(void)]
    [(fv_ (λ x e)) ,(set! fvs (append fvs (remove (term x) (fv-e (term e)))))]
    [(fv_ (e_1 e_2)) ,(begin (term (fv_ e_1)) (term (fv_ e_2)))])
  (term (fv_ ,t))
  fvs)


(define (fv t)
  (define fvs null)
  (define (add! x) (set! fvs (cons x fvs)))
  #;(define-metafunction pcf
    fv_ap : ap -> any ; void
    [(fv_ap x) ,(add! (term x))]
    [(fv_ap e0+f+ski) ,(void)]
    [(fv_ap (app ap e/x)) ,(begin (term (fv_ap ap)) (term (fv_ e/x)))])
  (define-metafunction pcf
    fv_ : e/x -> any ; void
    [(fv_ x) ,(add! (term x))]
    [(fv_ n) ,(void)]
    [(fv_ f) ,(void)]
    [(fv_ ski) ,(void)]
    [(fv_ (app e/x_1 e/x_2)) ,(begin (term (fv_ e/x_1)) (term (fv_ e/x_2)))])
  (term (fv_ ,t))
  fvs)

(define fv-term1 (term x))
(define fv-term2 (term (λ x x)))
(define fv-term3 (term (λ x y)))
(define fv-term4 (term (x (λ x x))))
(define fv-term5 (term (x (λ x y))))

(test-equal (fv-e fv-term1) '(x))
(test-equal (fv-e fv-term2) '())
(test-equal (fv-e fv-term3) '(y))
(test-equal (fv-e fv-term4) '(x))
(test-equal (fv-e fv-term5) '(x y))

(test-equal (fv-e (term (no-τ ,right+))) '())
(test-equal (fv-e (term (no-τ ,left+))) '())

; meaning fn
(define-metafunction pcf
  eval : e -> e/x
  [(eval e) (apply (expand e))])

;; expand function: expand into application of combinators, so we can use apply fn
(define-metafunction pcf
  expand : e -> e/x
  [(expand n) n]
  [(expand f) f]
  [(expand x) x]
  [(expand (e_1 e_2)) (app (expand e_1) (expand e_2))]
  [(expand (λ x e)) (λ* x (expand e))])

(define-metafunction pcf
  λ* : x e/x -> e/x
  [(λ* x x) I]
  [(λ* x e/x) (app K e/x)
   (side-condition (not (member (term x) (fv (term e/x)))))]
  [(λ* x (app e/x_1 e/x_2)) (app (app S (λ* x e/x_1)) (λ* x e/x_2))])

(define (var-sort xs) (sort xs string<? #:key symbol->string))
(test-equal (var-sort (fv-e fv-term1)) (var-sort (fv (term (expand ,fv-term1)))))
(test-equal (var-sort (fv-e fv-term2)) (var-sort (fv (term (expand ,fv-term2)))))
(test-equal (var-sort (fv-e fv-term3)) (var-sort (fv (term (expand ,fv-term3)))))
(test-equal (var-sort (fv-e fv-term4)) (var-sort (fv (term (expand ,fv-term4)))))
(test-equal (var-sort (fv-e fv-term5)) (var-sort (fv (term (expand ,fv-term5)))))


(define-metafunction pcf
  apply : e/x -> e/x
  [(apply ⊥) ⊥]
  [(apply e0) e0]
  [(apply ski) ski]
  [(apply (app I e/x)) (apply e/x)]
  [(apply (app K e/x)) (app K e/x)]
  [(apply (app ⊥ e/x)) ⊥]
  [(apply (app (app K e/x_1) e/x_2)) (apply e/x_1)]
  [(apply (app S e/x)) (app S e/x)]
  [(apply (app (app S e/x_1) e/x_2)) (app (app S e/x_1) e/x_2)]
  [(apply (app (app (app S e/x_1) e/x_2) e/x_3)) 
   (apply (app (app e/x_1 e/x_3) (app e/x_2 e/x_3)))]
  [(apply (app add1 n)) ,(add1 (term n))]
  [(apply (app add1 ⊥)) ⊥]
  [(apply (app add1 e/x)) (apply (app add1 (apply e/x)))]
  [(apply (app sub1 0)) ⊥]
  [(apply (app sub1 n)) ,(sub1 (term n))]
  [(apply (app sub1 ⊥)) ⊥]
  [(apply (app sub1 e/x)) (apply (app sub1 (apply e/x)))]
  [(apply (app if0 e/x)) (app if0 e/x)]
  [(apply (app (app if0 e/x) e/x_1)) (app (app if0 e/x) e/x_1)]
  [(apply (app (app (app if0 0) e/x_1) e/x_2)) (apply e/x_1)]
  [(apply (app (app (app if0 n) e/x_1) e/x_2)) (apply e/x_2)]
  [(apply (app (app (app if0 ⊥) e/x_1) e/x_2)) ⊥]
  [(apply (app (app (app if0 e/x) e/x_1) e/x_2))
   (apply (app (app (app if0 (apply e/x)) e/x_1) e/x_2))]
  [(apply (app Y e/x)) (apply (app e/x (app e/x ⊥)))]
  [(apply (app e/x_1 e/x_2)) (apply (app (apply e/x_1) e/x_2))
   #;(side-condition (printf "~a\n" (term (app e/x_1 e/x_2))))]
  )
;  [(apply add1 any) (δ add1 any)]
;  [(apply sub1 any) (δ sub1 any)]
;  [(apply I any) (δ I any)]
;  [(apply (ε K any_1) any_2) (δ K any_1 any_2)]
;  [(apply (ε S any_1 any_2) any_3) (δ S any_1 any_2 any_3)]
;  [(apply (ε if0 any_1 any_2) any_3) (δ if0 any_1 any_2 any_3)]
;  [(apply f+ any) (ε f+ any)]
;  [(apply (ε f+ any ...) any_1) (ε f+ any ... any_1)])

;(define-metafunction pcf
;  δ : f+ any ... -> e+ski
;  [(δ I any) any]
;  [(δ K any_1 any_2) any_1]
;  [(δ S any_1 any_2 any_3) ((any_1 any_3) (any_2 any_3))]
;  [(δ add1 n) ,(add1 (term n))]
;  [(δ add1 ⊥) ⊥]
;  [(δ sub1 0) ⊥]
;  [(δ sub1 n) ,(sub1 (term n))]
;  [(δ sub1 ⊥) ⊥]
;  [(δ if0 0 any_1 any_2) any_1]
;  [(δ if0 n any_1 any_2) any_2]
;  [(δ if0 ⊥ any_1 any_2) ⊥]
;  #;[(δ Y f) (δ f ⊥)
;   (side-condition (not (redex-match ⊥ (term (δ f ⊥)))))])

(define-syntax (test-eval-term stx)
  (syntax-case stx ()
    [(_ trm expected) 
     (syntax/loc stx (test-equal (term (eval trm)) (term expected)))]))

(test-eval-term 13 13)
(test-eval-term if0 if0)
(test-eval-term add1 add1)
(test-eval-term sub1 sub1)
(test-eval-term x x)
(test-eval-term (λ x x) I)
(test-eval-term ((λ x x) (λ y y)) I)
(test-eval-term (((λ x x) (λ y y)) (λ z z)) I)
(test-eval-term ((λ z z) ((λ x x) (λ y y))) I)
(test-eval-term (((λ x x) (λ y y)) ((λ z z) (λ w w))) I)
(test-eval-term (add1 10) 11)
(test-eval-term (sub1 0) ⊥)
;(test-eval-term (add1 ⊥) ⊥)
(test-eval-term (add1 (add1 20)) 22)
;(test-eval-term (add1 (sub1 ⊥)) ⊥)
(test-eval-term (add1 (sub1 0)) ⊥)
(test-eval-term (sub1 (add1 0)) 0)
(test-eval-term (if0 0) (app if0 0))
(test-eval-term ((if0 0) 10) (app (app if0 0) 10))
(test-eval-term ((if0 (sub1 0)) (add1 10)) (app (app if0 (app sub1 0)) (app add1 10)))
(test-eval-term (((if0 0) 10) 11) 10)
(test-eval-term (((if0 1) 10) 11) 11)
;(test-eval-term (((if0 ⊥) 10) 11) ⊥)
(test-eval-term (((if0 (sub1 0)) 10) 11) ⊥)
(test-eval-term (((if0 (add1 (sub1 0))) 10) 11) ⊥)
(test-eval-term (((if0 (sub1 (add1 0))) 10) 11) 10)
;(test-eval-term ((λ x (add1 20)) ⊥) 21)
(test-eval-term ((λ x (add1 20)) (sub1 0)) 21)
(test-eval-term (λ x (add1 20)) (app K (app add1 20)))
(test-eval-term (λ x (sub1 0)) (app K (app sub1 0)))
(test-eval-term (λ x (sub1 x)) (app (app S (app K sub1)) I))
(test-eval-term ((λ x (sub1 x)) (add1 10)) 10)
(test-eval-term (λ x (λ y (add1 x))) 
                (app (app S (app K K)) (app (app S (app K add1)) I)))
(test-eval-term ((λ x (λ y (add1 x))) 10)
                (app K (app (app (app S (app K add1)) I) 10)))
(test-eval-term (((λ x (λ y (add1 x))) 10) 12) 11)
(test-eval-term ((λ x (λ y (sub1 x))) 0) 
                (app K (app (app (app S (app K sub1)) I) 0)))
(test-eval-term (no-τ ,left+fn)
                (app (app S (app K (app S (app (app S (app K S)) (app (app S (app (app S (app K S)) (app (app S (app K K)) (app (app S (app K if0)) I)))) (app K I)))))) (app (app S (app K (app S (app K (app S (app K add1)))))) (app (app S (app (app S (app K S)) (app (app S (app K (app S (app K S)))) (app (app S (app K (app S (app K K)))) (app (app S (app (app S (app K S)) (app (app S (app K K)) I))) (app K (app (app S (app K sub1)) I))))))) (app K (app K I))))))

(test-eval-term (((λ x (λ y y)) 0) 10) 10)
(test-eval-term (((λ x (λ y x)) 0) 10) 0)
(test-eval-term (((λ x (λ y (((if0 x) x) y))) 0) 10) 0)

(define left+fn-simp (term (λ f (λ x (λ y (((if0 x) y) ((f (sub1 x)) y)))))))
(test-equal (not (redex-match pcf e left+fn-simp)) false)
(test-eval-term ,left+fn-simp
                (app (app S (app K (app S (app (app S (app K S)) (app (app S (app (app S (app K S)) (app (app S (app K K)) (app (app S (app K if0)) I)))) (app K I)))))) (app (app S (app (app S (app K S)) (app (app S (app K (app S (app K S)))) (app (app S (app K (app S (app K K)))) (app (app S (app (app S (app K S)) (app (app S (app K K)) I))) (app K (app (app S (app K sub1)) I))))))) (app K (app K I)))))

(test-eval-term (((,left+fn-simp (λ x (λ y y))) 0) 10) 10)
;; first two (x=0,1) work because (Y f) in apply applies f twice
(test-eval-term (((Y ,left+fn-simp) 0) 11) 11)
(test-eval-term (((Y ,left+fn-simp) 1) 11) 11)
; doesnt work because needs f applies three times
(test-eval-term (((Y ,left+fn-simp) 2) 11) ⊥)
;(test-eval-term (Y (no-τ ,left+fn)) x)