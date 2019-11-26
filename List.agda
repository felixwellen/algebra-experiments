{-# OPTIONS --without-K --safe #-}

open import Basics
open import Naturals

module List where

data list (A : Set) : Set where
  [] : list A
  _∷_ : A → list A → list A     -- \::

infixr 25 _∷_

infixl 30 _⊕_ -- \o+
_⊕_ : {A : Set} → list A → list A → list A
[] ⊕ l′ = l′
(x ∷ l) ⊕ l′ = x ∷ (l ⊕ l′)

length : {A : Set} → list A → ℕ
length [] = zero
length (x ∷ l) = succ (length l)

⊕-is-unital : {A : Set} (l : list A) → l ⊕ [] ≈ l and l ≈ [] ⊕ l
⊕-is-unital [] = ⟨ refl and refl ⟩
⊕-is-unital (x ∷ l) = ⟨ ap (λ l′ → x ∷ l′) (pr1 (⊕-is-unital l)) and refl ⟩

⊕-is-associative : {A : Set} (l l′ l″ : list A)
                   → (l ⊕ l′) ⊕ l″ ≈ l ⊕ (l′ ⊕ l″)
⊕-is-associative [] l′ l″ = refl
⊕-is-associative (x ∷ l) l′ l″ = ap (λ l → x ∷ l) (⊕-is-associative l l′ l″)
