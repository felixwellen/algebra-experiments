{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Basics where

data Empty : Set where

¬_ : Set → Set
¬ A = A → Empty

absurd : (A : Set) → Empty → A
absurd A ()

infixl 5 _and_
data _and_ (A B : Set) : Set where
  ⟨_and_⟩ : A → B → A and B

pr1 : {A B : Set}
      → A and B → A
pr1 ⟨ x and _ ⟩ = x      


hProp₀ = hProp ℓ-zero

_holds : ∀ {ℓ} → hProp ℓ → Type ℓ
(P , _) holds = P

holds-is-prop : (P : hProp₀) → isProp (P holds)
holds-is-prop (_ , is-prop) = is-prop

Σₛ : {A : Type₀} (P : A → hProp₀) → Type₀
Σₛ {A} P = Σ[ x ∈ A ] ((P x) holds)

ι : {A : Type₀} (P : A → hProp₀) 
    → (x : A) → P(x) holds → Σₛ P 
ι P x p = x , p
