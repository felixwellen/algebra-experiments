{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Ring
-- open import List

module PowerSeries (A : Set) {{ _ : ring-structure {A} }} where
  open ring-structure {{...}}

  data bounded-list (n : ℕ) : Type₀ where
    [] : bounded-list n
    _∷_ : (k : ℕ) → k ≤ n → bounded-list n → bounded-list n

  ℕ≤ : (n : ℕ) → Type₀
  ℕ≤ n = Σ[ k ∈ ℕ ] k ≤ n

  _-ℕ_ : (n : ℕ) → ℕ≤ n → ℕ
  n -ℕ (k , k≤n) = {!!}


  seq =  ℕ → A
{-
  [0,⋯,_] : ℕ → list ℕ
  [0,⋯, zero ] = [ zero ]
  [0,⋯, suc l ] =  [0,⋯, l ] ⊕ [ suc l ]

  ∑ : list A → A
  ∑ [] = 0′
  ∑ (x ∷ l) = x + (∑ l)
  
  cauchy-product : seq → seq → seq
  cauchy-product a b n = ∑ [ (a i)·(b {!n - i!}) ∣ i ∈ [0,⋯, n ] ]
-}
{-

  take_from_ : ℕ → seq → list A
  take zero from s = []
  take succ k from s = (s zero) ∷ (take k from (shift-by-one s)) 


  is-ring : ring-structure {seq}
  is-ring = record
              { _+_ = λ a b → λ n → (a n) + (b n)
              ; -_ = λ a → λ n → - (a n)
              ; 0′ = λ n → 0′
              ; +-is-associative = λ a b c → funExt λ n → +-is-associative (a n) (b n) (c n)
              ; +-is-unital = λ a → funExt (λ n → +-is-unital _)
              ; +-is-commutative = λ a b → funExt (λ _ → +-is-commutative _ _)
              ; +-has-inverses = λ a → funExt (λ _ → +-has-inverses _)
              ; _·_ = {!!}
              ; 1′ = {!!}
              ; ·-is-associative = {!!}
              ; ·-is-unital = {!!}
              ; ·-is-commutative = {!!}
              ; distributive = {!!}
              }
  
-}
