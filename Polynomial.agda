{-# OPTIONS --cubical --safe #-}
{-
  The goal is to compare multiple definitions of the ring of 
  polynomials in one variable over a given commutative unital ring.
-}
open import Cubical.Foundations.Prelude
open import Point
open import Ring
import FreeAlgebra
import HornerPolynomial renaming (R[X] to R[X]ₕ)
import PropertiesOfFreeAlgebra

module Polynomial (R : Type₀) ⦃ _ : ring-structure {R} ⦄ where

open FreeAlgebra R
open PropertiesOfFreeAlgebra R OnePointType
  renaming (evaluate-at to free-evaluate-at)
open HornerPolynomial R
  renaming (evaluate-at to horner-evaluate-at)
open ring-structure ⦃...⦄

R[X] : Type₀
R[X] = R[ OnePointType ] 
open free-structures OnePointType

X-free : R[X]
X-free = var point

horner-to-free : R[X]ₕ → R[X]
horner-to-free = horner-evaluate-at
                   R[X]
                   (λ x y → λ p q → R[_].is-0-truncated _ _ _ _) X-free

