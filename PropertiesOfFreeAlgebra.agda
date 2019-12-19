{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Ring
import FreeAlgebra

module PropertiesOfFreeAlgebra (R : Type₀) ⦃ ring-structure-on-R : ring-structure {R} ⦄
                               (I : Type₀) where

module _ (A : Type₀) (A-is-0-truncated : isOfHLevel 2 A) ⦃ _ : ring-structure {A} ⦄
                   ⦃ _ : algebra-structure R {A} ⦄ where
  open FreeAlgebra R
       hiding ()
       using (R[_])
  open FreeAlgebra.free-structures R I
  open algebra-structure ⦃...⦄
  open ring-structure ⦃...⦄

  evaluate-at : (I → A) → (R[ I ] → A)
  evaluate-at φ (R[_].var x) = φ x
  evaluate-at φ (R[_].const r) = r ⋆ 1′
  evaluate-at φ (P R[_].+ P′) = evaluate-at φ P + evaluate-at φ P′
  evaluate-at φ (R[_].- P) = - (evaluate-at φ P)
  evaluate-at φ R[_].0′ = 0′
  evaluate-at φ (R[_].+-is-associative P P₁ P₂ i) =
    +-is-associative (evaluate-at φ P) (evaluate-at φ P₁) (evaluate-at φ P₂) i
  evaluate-at φ (R[_].+-is-unital P i) = +-is-unital (evaluate-at φ P) i
  evaluate-at φ (R[_].+-is-commutative P P₁ i) =
    +-is-commutative (evaluate-at φ P) (evaluate-at φ P₁) i
  evaluate-at φ (R[_].+-has-inverses P i) = +-has-inverses (evaluate-at φ P) i
  evaluate-at φ (P R[_].· P₁) = evaluate-at φ P · evaluate-at φ P₁
  evaluate-at φ R[_].1′ = 1′
  evaluate-at φ (R[_].·-is-associative P P₁ P₂ i) =
    ·-is-associative (evaluate-at φ P) (evaluate-at φ P₁) (evaluate-at φ P₂) i
  evaluate-at φ (R[_].·-is-unital P i) = ·-is-unital (evaluate-at φ P) i
  evaluate-at φ (R[_].·-is-commutative P P₁ i) =
    ·-is-commutative (evaluate-at φ P) (evaluate-at φ P₁) i
  evaluate-at φ (R[_].distributive P P₁ P₂ i) =
    distributive (evaluate-at φ P) (evaluate-at φ P₁) (evaluate-at φ P₂) i
  evaluate-at φ (r R[_].⋆ P) = r ⋆ evaluate-at φ P
  evaluate-at φ (R[_].⋆-associates-with-· s t P i) =
    ⋆-associates-with-· s t (evaluate-at φ P) i
  evaluate-at φ (R[_].⋆-distributes-with-+ s t P i) =
    ⋆-distributes-with-+ s t (evaluate-at φ P) i
  evaluate-at φ (R[_].1-acts-trivial P i) =
    1-acts-trivial (evaluate-at φ P) i
  evaluate-at φ (R[_].is-0-truncated P P₁ p q i j) =
    A-is-0-truncated (evaluate-at φ P) (evaluate-at φ P₁) (cong _ p) (cong _ q) i j
