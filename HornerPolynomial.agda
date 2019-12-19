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


  lemma+const0 : ∀ P → P +const 0′ ≡ P
  lemma+const0 (const r) = cong const (+-is-unital _)
  lemma+const0 (Q ·X+ r) = cong (Q ·X+_) (+-is-unital _)
  lemma+const0 (const0-nullifies r i) = is-0-truncated _ _ {!!} {!!} i
  lemma+const0 (is-0-truncated P Q p q i j) = {!!}
{-  const r   +ₕ const s   = const (r + s)
  const r   +ₕ (P ·X+ s) = P ·X+ (r + s)
  (P ·X+ r) +ₕ const s   = P ·X+ (r + s)
  (P ·X+ r) +ₕ (Q ·X+ s) = (P +ₕ Q) ·X+ (r + s)
  const r +ₕ const0-nullifies s i   = (const 0′ ·X+ (r + s) ≡⟨ const0-nullifies (r + s) ⟩ const (r + s) ∎) i
  const0-nullifies r i +ₕ (const s) = (const 0′ ·X+ (r + s) ≡⟨ const0-nullifies _ ⟩ const (r + s) ∎) i
  const0-nullifies r i +ₕ (P ·X+ s) =
    let to-prove : (const 0′ ·X+ r) +ₕ (P ·X+ s) ≡ const r +ₕ (P ·X+ s) 
        to-prove = {!!}
    in to-prove i
  const0-nullifies r i +ₕ (const0-nullifies s j) =
    let to-prove : (const 0′ ·X+ r) +ₕ (const0-nullifies s j) ≡ const r +ₕ (const0-nullifies s j)
        to-prove = {!!}
    in to-prove i
  const0-nullifies r i +ₕ (is-0-truncated Q S p q j k) =
    let to-prove : (const 0′ ·X+ r) +ₕ (is-0-truncated Q S p q j k) ≡ const r +ₕ (is-0-truncated Q S p q j k)
        to-prove = {!!}
    in to-prove i
  ((const t) ·X+ r) +ₕ const0-nullifies s i =
    let to-prove : (const (t + 0′)) ·X+ (r + s) ≡ (const t ·X+ (r + s))
        to-prove = cong (λ u → const u ·X+ (r + s)) (+-is-unital _)
    in to-prove i
  ((P ·X+ t) ·X+ r) +ₕ const0-nullifies s i =
    let to-prove : (P ·X+ (t + 0′)) ·X+ (r + s) ≡ (P ·X+ t) ·X+ (r + s)
        to-prove = cong (λ u → (P ·X+ u) ·X+ (r + s)) (+-is-unital _)
    in to-prove i
  ((const0-nullifies t j) ·X+ r) +ₕ const0-nullifies s i =
    let to-prove : (_ +ₕ const 0′) ·X+ (r + s) ≡ (_ ·X+ (r + s))
        to-prove = {!!}
    in to-prove i
  ((is-0-truncated P Q p q j k) ·X+ r) +ₕ const0-nullifies s i =
    let to-prove : (P +ₕ const 0′) ·X+ (r + s) ≡ (P ·X+ (r + s))
        to-prove = {!!}
    in to-prove i
  const r +ₕ is-0-truncated Q S p q i j = is-0-truncated (const r +ₕ Q) (const r +ₕ S) (cong _ p) (cong _ q) i j
  (P ·X+ r) +ₕ is-0-truncated Q S p q i j = {!!}
  is-0-truncated P P₁ p q i i₁ +ₕ Q = {!!}

  _·ₕ_ : R[X] → R[X] → R[X]
  const r ·ₕ const s = const (r · s)
  const r ·ₕ (Q ·X+ s) = const r ·ₕ Q ·X+ r · s
  (P ·X+ r) ·ₕ const s = P ·ₕ const s ·X+ r · s
  (P ·X+ r) ·ₕ (Q ·X+ s) = {!P ·ₕ Q ·X+ !}
  (P ·X+ r) ·ₕ const0-nullifies r₁ i = {!!}
  (P ·X+ r) ·ₕ is-0-truncated Q Q₁ p q i i₁ = {!!}
  const r ·ₕ const0-nullifies s i = {!!}
  const r ·ₕ is-0-truncated Q Q₁ p q i i₁ = {!!}
  const0-nullifies r i ·ₕ Q = {!!}
  is-0-truncated P P₁ p q i i₁ ·ₕ Q = {!!}

  {- WRONG DEFINITION - this is not composition of polynomials -}
  _∘_ : R[X] → R[X] → R[X]
  const r ∘ g = const r
  (h ·X+ r) ∘ g = ((h ∘ g) ·ₕ g) +ₕ const r
  const0-nullifies r i ∘ g = {!!} -- const0-nullifies r i
  is-0-truncated f f′ p q i j ∘ g =
    is-0-truncated (f ∘ g) (f′ ∘ g) (cong (_∘ g) p) (cong (_∘ g) q) i j
-}




{-
-}

{-
  module _ (R-is-0-type : isOfHLevel 2 R) where 
    -- P = ∑ aᵢ X^i  => coefficient i P = aᵢ
    coefficient : ℕ → R[X] → R
    coefficient zero (const r) = r
    coefficient (suc n) (const r) = 0′
    coefficient zero (P ·X+ r) = r
    coefficient (suc n) (P ·X+ r) = coefficient n P
    coefficient 0 (const0-nullifies r i) = let eq-to-prove : coefficient 0 (const 0′ ·X+ r) ≡ coefficient 0 (const r)
                                               eq-to-prove = coefficient 0 (const 0′ ·X+ r) ≡⟨ refl ⟩ 
                                                             coefficient 0 (const r) ∎
                                           in eq-to-prove i
    coefficient (suc n) (const0-nullifies r i) = let compute-const-0 : (k : ℕ) → coefficient k (const 0′) ≡ 0′
                                                     compute-const-0 = (λ { zero → refl ; (suc k′) → refl })
{-                                                   eq-to-prove : _ ≡ _ -- coefficient (suc n) (const 0′ ·X+ r) ≡ coefficient (suc n) (const r)
                                                     eq-to-prove = coefficient (suc n) (const 0′ ·X+ r)   ≡⟨ {!!} ⟩
                                                                   coefficient n (const 0′)               ≡⟨ {!!} ⟩ 
                                                                   0′                                     ≡⟨ {!!} ⟩ 
                                                                   coefficient (suc n) (const r) ∎ -}
                                                 in compute-const-0 n i
    coefficient n (is-0-truncated P Q p q i j) = R-is-0-type (coefficient n P) (coefficient n Q) (cong _ p) (cong _ q) i j
-}

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
