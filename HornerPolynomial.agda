{-# OPTIONS --cubical --safe #-}

{-
Following this talk:
https://www.youtube.com/watch?v=VNp-f_9MnVk
of David Jaz Myers
 -}

open import Cubical.Foundations.Prelude
open import Ring

module HornerPolynomial (R : Set) {{ _ : ring-structure {R} }} where
  open ring-structure {{...}}

  infix 10 _·X+_

  data R[X] : Type₀ where
    const : R → R[X]
    _·X+_ : R[X] → R → R[X]
    const0-nullifies : (r : R) → const 0′ ·X+ r ≡ const r
    is-0-truncated : (x y : R[X]) (p q : x ≡ y) → p ≡ q
    
  _∘_ : R[X] → R[X] → R[X]
  const r ∘ g = const r
  (h ·X+ r) ∘ g = (h ∘ g) ·X+ r
  const0-nullifies r i ∘ g = const0-nullifies r i
  is-0-truncated f f′ p q i j ∘ g =
    is-0-truncated (f ∘ g) (f′ ∘ g) (cong (_∘ g) p) (cong (_∘ g) q) i j
