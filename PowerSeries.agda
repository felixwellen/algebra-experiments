{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Prod
open import Cubical.Data.List.Base
open import Ring
-- open import List

module PowerSeries (R : Type₀) ⦃ _ : ring-structure {R} ⦄ where
  open ring-structure ⦃...⦄

  seq = ℕ → R

  _+ₚ_ : seq → seq → seq
  a +ₚ b = λ n → a n + b n

  _⋆ₚ_ : R → seq → seq
  r ⋆ₚ a = λ n → r · (a n)

  [0,⋯,_] : ℕ → List ℕ
  [0,⋯, zero ] = [ zero ]
  [0,⋯, suc l ] =  [0,⋯, l ] ++ [ suc l ]

  zip : ∀ {A B : Type₀} → List A → List B → List (A × B)
  zip [] _ = []
  zip _ [] = []
  zip (x ∷ l) (y ∷ l′) = (x , y) ∷ zip l l′

  indices-for-cauchy-product : ℕ → List (ℕ × ℕ)
  indices-for-cauchy-product n = zip [0,⋯, n ] (rev [0,⋯, n ])

  ∑ : List R → R
  ∑ [] = 0′
  ∑ (x ∷ l) = x + (∑ l)

  map : {A B : Type₀} → (A → B) → List A → List B
  map f [] = []
  map f (x ∷ l) = f x ∷ map f l

  _·ₚ_ : seq → seq → seq
  a ·ₚ b = λ n → ∑ (map (λ {(k , l) → a k · b l}) (indices-for-cauchy-product n) )

  is-ring : ring-structure {seq}
  is-ring = record
              { _+_ = λ a b → λ n → (a n) + (b n)
              ; -_ = λ a → λ n → - (a n)
              ; 0′ = λ n → 0′
              ; +-is-associative = λ a b c → funExt λ n → +-is-associative (a n) (b n) (c n)
              ; +-is-unital = λ a → funExt (λ n → +-is-unital _)
              ; +-is-commutative = λ a b → funExt (λ _ → +-is-commutative _ _)
              ; +-has-inverses = λ a → funExt (λ _ → +-has-inverses _)
              ; _·_ = _·ₚ_
              ; 1′ = λ n → 1′
              ; ·-is-associative = {!!}
              ; ·-is-unital = {!!}
              ; ·-is-commutative = {!!}
              ; distributive = {!!}
              }
  

