{-# OPTIONS --cubical --safe #-}

{-
Following this talk:
https://www.youtube.com/watch?v=VNp-f_9MnVk
of David Jaz Myers
 -}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat.Base renaming (_+_ to _+ℕ_)
open import Ring

module HornerPolynomial (R : Type₀) ⦃ _ : ring-structure {R} ⦄ where
  open ring-structure ⦃...⦄

  infix 10 _·X+_

  data R[X] : Type₀ where
    const : R → R[X]
    _·X+_ : R[X] → R → R[X]
    const0-nullifies : (r : R) → const 0′ ·X+ r ≡ const r
    is-0-truncated : (x y : R[X]) (p q : x ≡ y) → p ≡ q


  _⋆ₕ_ : R → R[X] → R[X]
  r ⋆ₕ const s = const (r · s)
  r ⋆ₕ (P ·X+ s) = (r ⋆ₕ P) ·X+ (r · s)
  r ⋆ₕ const0-nullifies s i =
    let equality-to-prove : r ⋆ₕ (const 0′ ·X+ s) ≡ r ⋆ₕ const s
        equality-to-prove = const (r · 0′) ·X+ (r · s)      ≡⟨ cong (λ u → const u ·X+ (r · s)) (·-is-commutative _ _) ⟩
                            const (0′ · r) ·X+ (r · s)      ≡⟨ cong (λ u → const u ·X+ (r · s)) (0-nullifies′ _) ⟩
                            const 0′ ·X+ (r · s)            ≡⟨ const0-nullifies _ ⟩
                            const (r · s)                   ∎
    in equality-to-prove i
  r ⋆ₕ is-0-truncated P Q p q i j = is-0-truncated (r ⋆ₕ P) (r ⋆ₕ Q) (cong _ p) (cong _ q) i j

  _·X : R[X] → R[X]
  P ·X = P ·X+ 0′

  _+const_ : R[X] → R → R[X]
  const x +const r = const (x + r) 
  (P ·X+ x) +const r = P ·X+ (x + r)
  const0-nullifies r i +const s =(const 0′ ·X+ (r + s) ≡⟨ const0-nullifies (r + s) ⟩
                                  const (r + s) ∎) i
  is-0-truncated P Q p q i j +const r = is-0-truncated (P +const r) (Q +const r) (cong _ p) (cong _ q) i j

  module _ (R-is-0-type : isOfHLevel 2 R) where 
    constant-coefficient : R[X] → R
    constant-coefficient (const r) = r
    constant-coefficient (P ·X+ r) = r
    constant-coefficient (const0-nullifies r i) = ( r ≡⟨ refl ⟩ r ∎) i
    constant-coefficient (is-0-truncated P Q p q i j) =
      R-is-0-type (constant-coefficient P) (constant-coefficient Q)
                  (cong _ p) (cong _ q) i j

    non-constant-part : R[X] → R[X]
    non-constant-part (const r) = const 0′
    non-constant-part (P ·X+ r) = P
    non-constant-part (const0-nullifies r i) = (const 0′ ≡⟨ refl ⟩ const 0′ ∎) i
    non-constant-part (is-0-truncated P Q p q i j) =
      is-0-truncated (non-constant-part P) (non-constant-part Q) (cong _ p) (cong _ q) i j

    coefficient : ℕ → R[X] → R
    coefficient zero P = constant-coefficient P
    coefficient (suc n) P = coefficient n (non-constant-part P)

  private
    X = ((const 1′) ·X+ 0′)

  X-horner-form = X

  module _ (A : Type₀) (A-is-0-truncated : isOfHLevel 2 A) ⦃ _ : ring-structure {A} ⦄
                   ⦃ _ : algebra-structure R {A} ⦄ where
    open algebra-structure ⦃...⦄               
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
