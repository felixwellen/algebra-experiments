{-# OPTIONS --without-K --safe #-}

open import Basics

module Naturals where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+ℕ_ : ℕ → ℕ → ℕ
zero +ℕ b = b
succ a +ℕ b = succ (a +ℕ b)

data ℕ⁺ : Set where
  positiv : (k : ℕ) → ¬ (k ≈ zero) → ℕ⁺

succ-something-is-non-zero : (k : ℕ) → ¬ (succ k ≈ zero)
succ-something-is-non-zero k = λ ()

succ′ : ℕ → ℕ⁺
succ′ k = positiv (succ k) λ ()

pred : (k : ℕ) → ¬ (k ≈ zero) → ℕ
pred zero k-non-zero = absurd ℕ (k-non-zero refl)
pred (succ k) _ = k

pred′ : ℕ⁺ → ℕ
pred′ (positiv k x) = pred k x

inclusion : ℕ⁺ → ℕ
inclusion (positiv k x) = k

collapse : ℕ → ℕ⁺
collapse zero = positiv (succ zero) λ ()
collapse (succ n) = succ′ n

compute-pred∘succ : (k : ℕ) → (pred (succ k) λ ()) ≈ k
compute-pred∘succ k = refl

succ-is-injective : (a b : ℕ) → succ a ≈ succ b → a ≈ b
succ-is-injective zero zero _ = refl
succ-is-injective (succ a) (succ b) p = ap (λ x → pred′ (collapse x)) p

{- 
  From defining + we have '(succ a) + b = succ (a + b)',
  now we establish 'the other way' of pushing 'succ' out... 
-}
succ-commutes-with-+ : (a b : ℕ) → succ (a +ℕ b) ≈ (a +ℕ succ b)
succ-commutes-with-+ zero b = refl
succ-commutes-with-+ (succ a) b = ap succ (succ-commutes-with-+ a b)

+ℕ-is-associative : (a b c : ℕ) → ((a +ℕ b) +ℕ c) ≈ (a +ℕ (b +ℕ c))
+ℕ-is-associative zero b c = refl
+ℕ-is-associative (succ a) b c = ap succ (+ℕ-is-associative a b c)


+ℕ-is-unital : (a : ℕ) → (a +ℕ zero) ≈ a and a ≈ (zero +ℕ a)
+ℕ-is-unital zero = ⟨ refl and refl ⟩
+ℕ-is-unital (succ a) = ⟨ ap succ (pr1 (+ℕ-is-unital a)) and refl ⟩
