{-# OPTIONS --cubical --safe #-}
{-
  The goal is to compare multiple definitions of the ring of 
  polynomials in one variable over a given commutative unital ring.
-}
open import Cubical.Foundations.Prelude
open import Point
open import Ring
import FreeAlgebra
import HornerPolynomial

module Polynomial (R : Type₀) ⦃ _ : ring-structure {R} ⦄ where

open FreeAlgebra R
open HornerPolynomial R
open ring-structure ⦃...⦄

as-free-algebra : Type₀
as-free-algebra = R[ OnePointType ] 
open free-structures OnePointType

X-free : as-free-algebra
X-free = var point

as-horner-forms : Type₀
as-horner-forms = R[X]

horner-to-free : R[X] → as-free-algebra
horner-to-free = evaluate-at as-free-algebra (λ x y → λ p q → R[_].is-0-truncated _ _ _ _) X-free

