#lang racket
(require redex)

(define-language pcf
  (e n f x (λ (x τ) e) (e e) (if0 e e e) (Y e)) ; Y and if0 should not be 1st class?
  (f add1 sub1 if0)
  (n natural)
  (x variable-not-otherwise-mentioned)
  
  (τ nat (τ → τ))
  (Γ ([x τ]...)))

(define-judgment-form pcf
  #:mode (typeof I I O)
  #:contract (typeof Γ e τ)
  [(typeof Γ n nat)]
  [(typeof Γ add1 (nat → nat))]
  [(typeof Γ sub1 (nat → nat))]
  [(typeof Γ e_1 nat)
   (typeof Γ e_2 τ)
   (typeof Γ e_3 τ)
   ------------------------------
   (typeof Γ (if0 e_1 e_2 e_3) τ)]
  [(typeof Γ e (τ → τ))
   --------------------
   (typeof Γ (Y e) τ)]
  [(where τ (lookup Γ x))
   ----------------------
   (typeof Γ x τ)]
  [(typeof Γ e_1 (τ_2 → τ))
   (typeof Γ e_2 τ_2)
   ------------------------
   (typeof Γ (e_1 e_2) τ)]
  [(typeof (extend Γ x τ_1) e τ_2)
   ------------------------------------
   (typeof Γ (λ (x τ_1) e) (τ_1 → τ_2))])

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

(define left+ 
  (term (Y (λ (+ (nat → (nat → nat))) (λ (x nat) (λ (y nat) (if0 x y (add1 ((+ (sub1 x)) y)))))))))
(define right+ 
  (term (Y (λ (+ (nat → (nat → nat))) (λ (x nat) (λ (y nat) (if0 y x (add1 ((+ x) (sub1 y))))))))))

(test-equal (not (redex-match pcf e left+)) false)
(test-equal (not (redex-match pcf e right+)) false)
(test-equal (judgment-holds (typeof () ,left+ τ) τ) (term ((nat → (nat → nat)))))
(test-equal (judgment-holds (typeof () ,right+ τ) τ) (term ((nat → (nat → nat)))))