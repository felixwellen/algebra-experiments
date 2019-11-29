{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Ring

module FreeAlgebra (𝔸 : Set) {{ ring-structure-on-𝔸 : ring-structure {𝔸} }} where
infixl 15 _·_
infixl 10 _+_

open ring-structure ring-structure-on-𝔸 using ()
  renaming (_·_ to _·s_; _+_ to _+s_; -_ to -s_; 0′ to 0s; 1′ to 1s)

data A : Set where
  const : 𝔸 → A
  _+_ : A → A → A
  -_ : A → A
  0′ : A

  +-is-associative : (x y z : A) → x + (y + z) ≡ (x + y) + z
  +-is-unital : (x : A) → x + 0′ ≡ x
  +-is-commutative : (x y : A) → x + y ≡ y + x
  +-has-inverses : (x : A) → x + (- x) ≡ 0′

  _·_ : A → A → A            -- \cdot
  1′ : A
  ·-is-associative : (x y z : A) → x · (y · z) ≡ (x · y) · z
  ·-is-unital : (x : A) → 1′ · x ≡ x
  ·-is-commutative : (x y : A) → x · y ≡ y · x

  distributive : (x y z : A) → (x + y) · z ≡ x · z + y · z
  
  _⋆_ : 𝔸 → A → A        -- \*
  ⋆-associates-with-· : (s t : 𝔸) (x : A) → s ⋆ (t ⋆ x) ≡ (s ·s t) ⋆ x
  ⋆-distributes-with-+ : (s t : 𝔸) (x : A) → (s +s t) ⋆ x ≡ s ⋆ x + t ⋆ x
  1-acts-trivial : (x : A) → 1s ⋆ x ≡ x

  is-0-truncated : (x y : A) (p q : x ≡ y) → p ≡ q
