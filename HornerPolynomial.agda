{-# OPTIONS --cubical --safe #-}

{-
Following this talk:
https://www.youtube.com/watch?v=VNp-f_9MnVk
of David Jaz Myers
 -}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
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

  private
    X = ((const 1′) ·X+ 0′)

  X-horner-form = X

  module _ (A : Type₀) (A-is-0-truncated : isOfHLevel 2 A) {{ _ : ring-structure {A} }}
                   {{ _ : algebra-structure R {A} }} where
    open algebra-structure {{...}}               
    evaluate-at : A → (R[X] → A)
    evaluate-at a (const r) = r ⋆ 1′
    evaluate-at a (f ·X+ r) = (evaluate-at a f) · a + r ⋆ 1′
    evaluate-at a (const0-nullifies r i) =
         let equality-to-construct =
               (0′ ⋆ 1′) · a + r ⋆ 1′ ≡⟨ cong (λ u → u · a + r ⋆ 1′) (sym (0-acts-nullifying 1′)) ⟩
               0′ · a + r ⋆ 1′        ≡⟨ cong (λ u → u + r ⋆ 1′) (0-nullifies′ a) ⟩
               0′ + r ⋆ 1′            ≡⟨ +-is-unital′ _ ⟩
               r ⋆ 1′                 ∎ 
         in equality-to-construct i
    evaluate-at a (is-0-truncated f f′ p q i j) =
      A-is-0-truncated
        (evaluate-at a f) (evaluate-at a f′) (cong (evaluate-at a) p) (cong (evaluate-at a) q) i j

    image-of-X : (R[X] → A) → A
    image-of-X f = f X
