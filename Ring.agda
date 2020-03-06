{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Basics
open import AbelianGroup

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

data ZeroRing : Set where
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



module _ (R : Set) ⦃ _ : ring-structure {R} ⦄ where

  record algebra-structure {A : Set} ⦃ _ : ring-structure {A} ⦄ : Set where
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
          {A : Set} {{ _ : ring-structure {A} }} {{ _ : algebra-structure {A} }} 
          {B : Set} {{ _ : ring-structure {B} }} {{ _ : algebra-structure {B} }}
          (f : A → B) : Set where
    open ring-structure {{...}}
    open algebra-structure {{...}}
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

module ideal {R : Type₀}  ⦃ _ : ring-structure {R} ⦄ where
  open ring-structure ⦃...⦄
  record is-ideal (I : R → hProp₀) : Type₀ where
    field
      +-closed : {x y : R} (_ : I(x) holds) (_ : I(y) holds) → I(x + y) holds
      -closed : {x : R} (_ : I(x) holds) → I(- x) holds
      0′-closed : I(0′) holds
      ·-closed : {r x : R} (_ : I(x) holds) → I(r · x) holds

    I′ : Type₀
    I′ = Σₛ I

    _+′_ : I′ → I′ → I′
    (x , p) +′ (y , q) = (x + y , +-closed p q)

    +-is-associative′ : (x y z : I′) → x +′ (y +′ z) ≡ (x +′ y) +′ z
    +-is-associative′ (x , p) (y , q) (z , r) =
                      subtypeEqual′ {P = I}
                        ((x , p) +′ ((y , q) +′ (z , r)))
                        (((x , p) +′ (y , q)) +′ (z , r))
                        (+-is-associative x y z)

    is-abelian-group : abelian-group-structure {I′}
    is-abelian-group = record
                         { _+_ = _+′_
                         ; -_ = λ {(x , p) → (- x) , -closed p}
                         ; 0′ = 0′ , 0′-closed
                         ; +-is-associative = +-is-associative′
                         ; +-is-unital = λ {(x , _) → subtypeEqual′ {P = I} _ _ (+-is-unital x)}
                         ; +-is-commutative = λ {(x , _) (y , _)
                                                → subtypeEqual′ {P = I} _ _ (+-is-commutative x y)}
                         ; +-has-inverses = λ {(x , _)
                                            →  subtypeEqual′ {P = I} _ _ (+-has-inverses x) }
                         }

  data QuotientRing (I : R → hProp₀) (isIdeal : is-ideal I) : Type₀ where
    proj : R → QuotientRing I isIdeal
    mod : (r : R) (m : Σₛ I) → proj r ≡ proj (r + fst m)
    is0truncated : (x y : QuotientRing I isIdeal) (p q : x ≡ y) → p ≡ q

  
