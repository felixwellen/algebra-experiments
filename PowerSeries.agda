{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Ring
open import List
open import Naturals

module PowerSeries (A : Set) {{ _ : ring-structure {A} }} where
  open ring-structure {{...}}

  seq =  ℕ → A

  shift-by : ℕ → seq → seq
  shift-by zero s = s
  shift-by (succ k) s = λ n → (shift-by k s) (succ n)

  shift-by-one = shift-by (succ zero)

  [0,⋯,_] : ℕ → list ℕ
  [0,⋯, zero ] = [ zero ]
  [0,⋯, succ l ] =  [0,⋯, l ] ⊕ [ succ l ]

  ∑ : list A → A
  ∑ [] = 0′
  ∑ (x ∷ l) = x + ∑ l
  
{-

  take_from_ : ℕ → seq → list A
  take zero from s = []
  take succ k from s = (s zero) ∷ (take k from (shift-by-one s)) 

  cauchy-product : seq → seq → seq
  cauchy-product a b n = ∑ [ (a i)·(b {!!}) ∣ i ∈ [0,⋯, n ] ]

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
