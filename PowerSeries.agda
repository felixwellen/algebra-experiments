{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Ring
-- open import List

module PowerSeries (A : Set) ⦃ _ : ring-structure {A} ⦄ where
  open ring-structure ⦃...⦄

  data bounded-list (n : ℕ) : Type₀ where
    [] : bounded-list n
    _∷_ : (k : ℕ) → k ≤ n → bounded-list n → bounded-list n

  ℕ≤ : (n : ℕ) → Type₀
  ℕ≤ n = Σ[ k ∈ ℕ ] k ≤ n
