{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Basics

module Naturals where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+ℕ_ : ℕ → ℕ → ℕ
zero +ℕ b = b
succ a +ℕ b = succ (a +ℕ b)

data ℕ⁺ : Set where
  positiv : (k : ℕ) → ¬ (k ≡ zero) → ℕ⁺

pred : (k : ℕ) → ¬ (k ≡ zero) → ℕ
pred zero k-non-zero = absurd ℕ (k-non-zero refl)
pred (succ k) _ = k

pred′ : ℕ⁺ → ℕ
pred′ (positiv k x) = pred k x

inclusion : ℕ⁺ → ℕ
inclusion (positiv k x) = k

{- 
  From defining + we have '(succ a) + b = succ (a + b)',
  now we establish 'the other way' of pushing 'succ' out... 
-}
succ-commutes-with-+ : (a b : ℕ) → succ (a +ℕ b) ≡ (a +ℕ succ b)
succ-commutes-with-+ zero b = refl
succ-commutes-with-+ (succ a) b = cong succ (succ-commutes-with-+ a b)

+ℕ-is-associative : (a b c : ℕ) → ((a +ℕ b) +ℕ c) ≡ (a +ℕ (b +ℕ c))
+ℕ-is-associative zero b c = refl
+ℕ-is-associative (succ a) b c = cong succ (+ℕ-is-associative a b c)


+ℕ-is-unital : (a : ℕ) → ((a +ℕ zero) ≡ a) and (a ≡ (zero +ℕ a))
+ℕ-is-unital zero = ⟨ refl and refl ⟩
+ℕ-is-unital (succ a) = ⟨ cong succ (pr1 (+ℕ-is-unital a)) and refl ⟩
