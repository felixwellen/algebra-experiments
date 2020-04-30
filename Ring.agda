{-# OPTIONS --cubical --safe  #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Basics

module Ring where

record ring-structure {A : Type₀} : Type₀ where
  field
    _+_ : A → A → A
    -_ : A → A
    0′ : A                    -- 0\'
    
    +-is-associative : (x y z : A) → x + (y + z) ≡ (x + y) + z
    +-is-unital : (x : A) → x + 0′ ≡ x
    +-is-commutative : (x y : A) → x + y ≡ y + x
    +-has-inverses : (x : A) → x + (- x) ≡ 0′

    _·_ : A → A → A            -- \cdot
    1′ : A                     -- 1\'
    ·-is-associative : (x y z : A) → x · (y · z) ≡ (x · y) · z
    ·-is-unital : (x : A) → 1′ · x ≡ x
    ·-is-commutative : (x y : A) → x · y ≡ y · x

    distributive : (x y z : A) → (x + y) · z ≡ x · z + y · z

  infixl 15 _·_
  infixl 10 _+_


  right-distributive : (x y z : A) → x · (y + z) ≡ x · y + x · z
  right-distributive x y z = x · (y + z)    ≡⟨ ·-is-commutative _ _ ⟩
                             (y + z) · x    ≡⟨ distributive _ _ _ ⟩ 
                             y · x + z · x  ≡⟨ cong (λ u → u + z · x) (·-is-commutative _ _) ⟩ 
                             x · y + z · x  ≡⟨ cong (λ u → x · y + u) (·-is-commutative _ _) ⟩ 
                             x · y + x · z  ∎

  0-idempotent : 0′ + 0′ ≡ 0′
  0-idempotent = +-is-unital 0′

  +-idempotency→0 : (x : A) → x ≡ x + x → 0′ ≡ x
  +-idempotency→0 x p = 0′              ≡⟨ sym (+-has-inverses _) ⟩
                        x + (- x)       ≡⟨ cong (λ u → u + (- x)) p ⟩
                        x + x + (- x)   ≡⟨ sym (+-is-associative _ _ _) ⟩
                        x + (x + (- x)) ≡⟨ cong (λ u → x + u) (+-has-inverses _) ⟩
                        x + 0′          ≡⟨ +-is-unital x ⟩
                        x               ∎

  0-nullifies : (x : A) → 0′ ≡ x · 0′
  0-nullifies x =
              let x·0-is-idempotent : x · 0′ ≡ x · 0′ + x · 0′
                  x·0-is-idempotent =
                    x · 0′           ≡⟨ cong (λ u → x · u) (sym 0-idempotent) ⟩
                    x · (0′ + 0′)    ≡⟨ right-distributive _ _ _ ⟩ 
                    x · 0′ + x · 0′  ∎
              in +-idempotency→0 _ x·0-is-idempotent

  0-nullifies′ : (x : A) → 0′ · x ≡ 0′
  0-nullifies′ x = sym (0-nullifies x ∙ ·-is-commutative x 0′)
  
  infixl 10 _-_
  _-_ : A → A → A
  x - y = x + (- y)

  +-has-inverses′ : (x : A) → (- x) + x ≡ 0′
  +-has-inverses′ x = (- x) + x ≡⟨ +-is-commutative _ _ ⟩
                      x - x     ≡⟨ +-has-inverses _ ⟩
                      0′        ∎

  +-is-unital′ : (x : A) → 0′ + x ≡ x
  +-is-unital′ x = 0′ + x    ≡⟨ +-is-commutative _ _ ⟩
                   x + 0′    ≡⟨ +-is-unital _ ⟩
                   x        ∎

  +-is-associative′ : (x y z : A) → (x + y) + z ≡ x + (y + z)
  +-is-associative′ x y z = sym (+-is-associative x y z) 

  isInverseTo- : (x y : A)
                 → x + y ≡ 0′
                 → y ≡ - x
  isInverseTo- x y p = y               ≡⟨ sym (+-is-unital′ y) ⟩
                       0′ + y          ≡⟨ cong (λ u → u + y)
                                               (sym (+-has-inverses′ x)) ⟩
                       (- x + x) + y   ≡⟨ +-is-associative′ _ _ _ ⟩
                       (- x) + (x + y) ≡⟨ cong (λ u → (- x) + u) p ⟩
                       (- x) + 0′      ≡⟨ +-is-unital _ ⟩
                       - x             ∎ 
  
  -isDistributive : (x y : A) →  (- x) + (- y) ≡ - (x + y)
  -isDistributive x y =
    isInverseTo- _ _
          (x + y + ((- x) + (- y))  ≡⟨ +-is-associative′ _ _ _ ⟩
          x + (y + ((- x) + (- y))) ≡⟨ cong
                                       (λ u → x + (y + u))
                                       (+-is-commutative (- x) (- y )) ⟩
          x + (y + ((- y) + (- x))) ≡⟨ cong (λ u → x + u) (+-is-associative _ _ _) ⟩
          x + ((y + (- y)) + (- x)) ≡⟨ cong (λ u → x + (u + (- x)))
                                            (+-has-inverses _) ⟩
          x + (0′ + (- x))          ≡⟨ cong (λ u → x + u) (+-is-unital′ _) ⟩
          x + (- x)                 ≡⟨ +-has-inverses _ ⟩
          0′ ∎)

  -commutes-with-· : (x y : A) →  x · (- y) ≡ - (x · y)
  -commutes-with-· x y = isInverseTo- (x · y) (x · (- y))
                                      ((x · y) + (x · (- y))   ≡⟨ sym (right-distributive _ _ _) ⟩
                                       x · (y + (- y))         ≡⟨ cong (λ u → x · u) (+-has-inverses y) ⟩
                                       x · 0′                  ≡⟨ sym (0-nullifies x) ⟩
                                       0′ ∎) 
  
data ZeroRing : Type₀ where
  0″ : ZeroRing

0-ring-structure : ring-structure {ZeroRing}
0-ring-structure = record
                     { _+_ = λ _ _ → 0″
                     ; -_ = λ _ → 0″
                     ; 0′ = 0″
                     ; +-is-associative = λ _ _ _ → refl
                     ; +-is-unital = λ {0″ → refl}
                     ; +-is-commutative = λ _ _ → refl
                     ; +-has-inverses = λ _ → refl
                     ; _·_ = λ _ _ → 0″
                     ; 1′ = 0″
                     ; ·-is-associative = λ _ _ _ → refl
                     ; ·-is-unital = λ {0″ → refl}
                     ; ·-is-commutative = λ _ _ → refl
                     ; distributive = λ _ _ _ → refl
                     }

module _ (R : Type₀) ⦃ _ : ring-structure {R} ⦄ where

  record algebra-structure {A : Set} ⦃ _ : ring-structure {A} ⦄ : Type₀ where
    open ring-structure ⦃...⦄
    field
      _⋆_ : R → A → A        -- \*
      ⋆-associates-with-· : (s t : R) (x : A) → s ⋆ (t ⋆ x) ≡ (s · t) ⋆ x
      ⋆-distributes-with-+ : (s t : R) (x : A) → (s + t) ⋆ x ≡ s ⋆ x + t ⋆ x
      1-acts-trivial : (x : A) → 1′ ⋆ x ≡ x

    infixl 14 _⋆_

    0-acts-nullifying : (x : A) → 0′ ≡ 0′ ⋆ x
    0-acts-nullifying x =
                    let 0x-is-idempotent : 0′ ⋆ x ≡ 0′ ⋆ x + 0′ ⋆ x
                        0x-is-idempotent =
                          0′ ⋆ x           ≡⟨ cong (λ u → u ⋆ x) (sym 0-idempotent) ⟩
                          (0′ + 0′) ⋆ x    ≡⟨ ⋆-distributes-with-+ _ _ _ ⟩
                          0′ ⋆ x + 0′ ⋆ x  ∎
                    in +-idempotency→0 _ 0x-is-idempotent

  trivial-algebra-structure : algebra-structure
  trivial-algebra-structure =
    let open ring-structure {{...}}
    in record
       { _⋆_ = _·_
         ; ⋆-associates-with-· = ·-is-associative
         ; ⋆-distributes-with-+ = distributive
         ; 1-acts-trivial = ·-is-unital
       }

  record _-algebra-homomorphism-structure
          {A : Type₀} ⦃ _ : ring-structure {A} ⦄ ⦃ _ : algebra-structure {A} ⦄
          {B : Type₀} ⦃ _ : ring-structure {B} ⦄ ⦃ _ : algebra-structure {B} ⦄
          (f : A → B) : Type₀ where
    open ring-structure ⦃...⦄
    open algebra-structure ⦃...⦄
    field
      ·-homomorphic : (x y : A) → f (x · y) ≡ f x · f y 
      +-homomorphic : (x y : A) → f (x + y) ≡ f x + f y 
      ·-unital : f 1′ ≡ 1′
      ⋆-homomorphic : (s : R) (x : A) → f (s ⋆ x) ≡ s ⋆ f x

    0-unital : 0′ ≡ f 0′
    0-unital =
      let idempotent = f 0′         ≡⟨ cong f (sym 0-idempotent) ⟩
                       f (0′ + 0′)  ≡⟨ +-homomorphic _ _ ⟩
                       f 0′ + f 0′  ∎
      in +-idempotency→0 (f 0′) idempotent

    inversion-homomorphic : (x : A) → - (f x) ≡ f (- x)
    inversion-homomorphic x =
      let
          p = 0′             ≡⟨ 0-unital ⟩
              f 0′           ≡⟨ cong f (sym (+-has-inverses _)) ⟩
              f (x - x)      ≡⟨ +-homomorphic _ _ ⟩
              f x + f (- x)  ∎
      in - f x                   ≡⟨ sym (+-is-unital _) ⟩
         - f x + 0′              ≡⟨ cong (λ u → - f x + u) p ⟩
         - f x + (f x + f (- x)) ≡⟨ +-is-associative _ _ _ ⟩
         (- f x + f x) + f (- x) ≡⟨ cong (λ u → u + f (- x)) (+-has-inverses′ _) ⟩
         0′ + f (- x)            ≡⟨ +-is-unital′ _ ⟩
         f (- x)                 ∎

