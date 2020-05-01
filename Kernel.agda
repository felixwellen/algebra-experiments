{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties
open import Basics
open import Ring
open import QuotientRing

{- kernel of algebra homomorphism -}
module Kernel where
  
module _ (R : Type₀) ⦃ _ : ring-structure {R} ⦄ where
  open ring-structure ⦃...⦄

  module _ (A B : Type₀) (B-is-0-truncated : isOfHLevel 2 B)
      ⦃ _ : ring-structure {A} ⦄ ⦃ _ : algebra-structure R {A} ⦄
      ⦃ _ : ring-structure {B} ⦄ ⦃ _ : algebra-structure R {B} ⦄ where
    kernel : 
      (hom R A B) → (A → hProp₀)
    kernel (f , _) = λ a → (f(a) ≡ 0′) , B-is-0-truncated _ _

    isIdeal : (f : hom R A B) → ideal.is-ideal (kernel f)
    isIdeal (f , isHom)
            = let open algebra-homomorphism-structure isHom
              in record
                  { +-closed = λ {x} {y} x∈I y∈I →
                                             f(x + y)     ≡⟨ +-homomorphic _ _ ⟩
                                             f(x) + f(y)  ≡⟨ cong (λ u → f(x) + u) y∈I ⟩
                                             f(x) + 0′    ≡⟨ cong (λ u → u + 0′) x∈I ⟩
                                             0′ + 0′      ≡⟨ +-is-unital 0′ ⟩
                                             0′ ∎ ;
                  -closed = λ {x} x∈I → f(- x)   ≡⟨ sym (inversion-homomorphic x) ⟩
                                        - f(x)   ≡⟨ cong (λ u → - u) x∈I ⟩
                                        - 0′     ≡⟨ 0-selfinverse ⟩
                                        0′       ∎  ;
                  0′-closed = sym 0-unital ;
                  ·-closed = λ {x} r x∈I → f(r · x)     ≡⟨ ·-homomorphic _ _ ⟩
                                           f(r) · f(x)  ≡⟨ cong (λ u → f(r) · u) x∈I ⟩
                                           f(r) · 0′    ≡⟨ sym (0-nullifies _) ⟩
                                           0′ ∎ }
