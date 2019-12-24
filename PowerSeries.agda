{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Prod
open import Cubical.Data.List.Base
open import Ring
open import Optional

module PowerSeries (R : Type₀) ⦃ _ : ring-structure {R} ⦄ where
  open ring-structure ⦃...⦄

  seq = ℕ → R

  0ₚ : seq
  0ₚ n = 0′

  1ₚ : seq
  1ₚ zero = 1′
  1ₚ (suc n) = 0′

  _+ₚ_ : seq → seq → seq
  a +ₚ b = λ n → a n + b n

  -ₚ_ : seq → seq
  -ₚ a = λ n → - a n

  _⋆ₚ_ : R → seq → seq
  r ⋆ₚ a = λ n → r · (a n)

  [0,⋯,_] : ℕ → List ℕ
  [0,⋯, zero ] = [ zero ]
  [0,⋯, suc l ] =  [0,⋯, l ] ++ [ suc l ]

  zip : ∀ {A B : Type₀} → List A → List B → List (A × B)
  zip [] _ = []
  zip _ [] = []
  zip (x ∷ l) (y ∷ l′) = (x , y) ∷ zip l l′

  private
    indices-for-cauchy-product : ℕ → List (ℕ × ℕ)
    indices-for-cauchy-product n = zip [0,⋯, n ] (rev [0,⋯, n ])

  ∑ : List R → R
  ∑ [] = 0′
  ∑ (x ∷ []) = x
  ∑ (x ∷ l) = x + (∑ l)

  map : {A B : Type₀} → (A → B) → List A → List B
  map f [] = []
  map f (x ∷ l) = f x ∷ map f l

  private
    cauchy-numbers : seq → seq → ℕ → List R
    cauchy-numbers a b n = map (λ {(k , l) → a k · b l}) (indices-for-cauchy-product n)

    tail : {A : Type₀} → List A → Optional (List A)
    tail [] = None
    tail (x ∷ l) = Some l

    zero-list : ℕ → List R
    zero-list zero = []
    zero-list (suc n) = 0′ ∷ zero-list n

{-
    for-1ₚ : (a : seq) (k : ℕ) → cauchy-numbers a 1ₚ k ≡ a k ∷ zero-list k
    for-1ₚ a zero    = a 0 · 1′ ∷ [] ≡⟨ cong (λ u → u ∷ []) (·-is-unital′ _) ⟩  a 0 ∷ [] ∎
    for-1ₚ a (suc k) = {!!}
-}

  _·ₚ_ : seq → seq → seq
  a ·ₚ b = λ n → ∑ (cauchy-numbers a b n)

{-
  ·ₚ-unital : (a : seq) (k : ℕ) → (a ·ₚ 1ₚ) k ≡ a k
  ·ₚ-unital a zero = a 0 · 1′ ≡⟨ ·-is-unital′ _ ⟩  a 0 ∎
  ·ₚ-unital a (suc k) = (a ·ₚ 1ₚ) (suc k)         ≡⟨ {!!} ⟩
                        (a (suc k) · 1′) + ∑ l    ≡⟨ {!!} ⟩
                        (a (suc k) · 1′) + 0′     ≡⟨ {!!} ⟩
                        (a (suc k) · 1′)          ≡⟨ {!!} ⟩
                        a (suc k)                 ∎
                      where
                        l = {!cauchy-numbers a ·ₚ 1ₚ!}

  is-ring : ring-structure {seq}
  is-ring = record
              { _+_ = _+ₚ_
              ; -_ = λ a → λ n → - (a n)
              ; 0′ = 0ₚ
              ; +-is-associative = λ a b c → funExt λ n → +-is-associative (a n) (b n) (c n)
              ; +-is-unital = λ a → funExt (λ n → +-is-unital _)
              ; +-is-commutative = λ a b → funExt (λ _ → +-is-commutative _ _)
              ; +-has-inverses = λ a → funExt (λ _ → +-has-inverses _)
              ; _·_ = _·ₚ_
              ; 1′ = 1ₚ
              ; ·-is-associative = {!!}
              ; ·-is-unital = {!!}
              ; ·-is-commutative = {!!}
              ; distributive = {!!}
              }
-}
  

