{-# OPTIONS --without-K #-}

open import Basics
open import Naturals
open import Ring
open import FunctionExtensionality

module PowerSeries (A : Set) {{ _ : ring-structure {A} }} where
  open ring-structure {{...}}

  seq =  ℕ → A


  cauchy-product : seq → seq → seq
  cauchy-product a b = ?

  is-ring : ring-structure {seq}
  is-ring = record
              { _+_ = λ a b → λ n → (a n) + (b n)
              ; -_ = λ a → λ n → - (a n)
              ; 0′ = λ n → 0′
              ; +-is-associative = λ a b c → fun-ext λ n → +-is-associative (a n) (b n) (c n)
              ; +-is-unital = λ a → fun-ext (λ n → +-is-unital _)
              ; +-is-commutative = λ a b → fun-ext (λ _ → +-is-commutative _ _)
              ; +-has-inverses = λ a → fun-ext (λ _ → +-has-inverses _)
              ; _·_ = {!!}
              ; 1′ = {!!}
              ; ·-is-associative = {!!}
              ; ·-is-unital = {!!}
              ; ·-is-commutative = {!!}
              ; distributive = {!!}
              }
  

