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

subtypeEqual : {A : Type₀} {x y : A} {P : A → hProp₀} (p : x ≡ y)
               → (px : P(x) holds) (py : P(y) holds) 
               → ι P x px  ≡ ι P y py
subtypeEqual {x = x} {y = y} {P = P} p px py =
             (x , px)    ≡⟨ (λ i → x , (snd (P x) px px′ i)) ⟩
             (x , px′)   ≡⟨ p′ ⟩
             (y , py′)   ≡⟨ (λ i → y , (snd (P y) py′ py i)) ⟩ 
             (y , py)    ∎
  where
    px′ = subst (λ u → P u holds) (λ j → p (i0 ∧ j)) px
    py′ = subst (λ u → P u holds) (λ j → p (i1 ∧ j)) px
    p′ : (x , px′)  ≡ (y , py′)
    p′ i = (p i , subst (λ u → P u holds) (λ j → p (i ∧ j)) px) 

subtypeEqual′ : {A : Type₀} {P : A → hProp₀}
                → (x y : Σₛ P) (p : fst x ≡ fst y)
                → x ≡ y
subtypeEqual′ {_} {P} x y p = subtypeEqual {P = P} p (snd x) (snd y)
