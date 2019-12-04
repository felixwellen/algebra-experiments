{-# OPTIONS --cubical --safe #-}
{-
  copied from here:
  https://github.com/DavidJaz/Cohesion/blob/master/UpperNaturals.agda
  adapting...
-}
open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import Cubical.Foundations.HLevels
open import Basics hiding (¬)

module UpperNaturals where

hProp₀ = hProp {ℓ-zero}

_holds : ∀ {ℓ} → hProp {ℓ} → Type ℓ
(P , _) holds = P

holds-is-prop : (P : hProp₀) → isProp (P holds)
holds-is-prop (_ , is-prop) = is-prop

-- A propositional version of _≤_
_≤p_ : ℕ → ℕ → hProp₀
n ≤p m = (n ≤ m) , m≤n-isProp

_is-upward-closed : (N : ℕ → hProp₀) → Type₀
N is-upward-closed = (n m : ℕ) → n ≤ m → (N n) holds → (N m) holds

upward-closed-is-a-prop : (N : ℕ → hProp₀) → isProp (N is-upward-closed) 
upward-closed-is-a-prop N =
  propPi (λ _ → propPi (λ m → propPi (λ _ → propPi λ _ → holds-is-prop (N m))))

ℕ→Prop₀-is-a-set : isSet (ℕ → hProp₀) 
ℕ→Prop₀-is-a-set = hLevelPi 2 λ _ → isSetHProp

{- The Upper Naturals
   An upper natural is an upward closed proposition concerning natural numbers.
   The interpretation is that an upper natural is a natural ``defined by its upper bounds'', in the
   sense that for the proposition N holding of a natural n means that n is an upper bound of N.

   The important bit about upper naturals is that they satisfy the well-ordering principle, 
   constructively.
-}
ℕ↑ : Type₁
ℕ↑ = Σ[ s ∈ (ℕ → hProp₀)] s is-upward-closed

ℕ↑-is-a-set : isSet ℕ↑
ℕ↑-is-a-set = isOfHLevelΣ 2 ℕ→Prop₀-is-a-set (λ s  → hLevelSuc 1 _ (upward-closed-is-a-prop s))


_is-an-upper-bound-of_ : ℕ → ℕ↑ → hProp₀
n is-an-upper-bound-of M = (fst M) n

_≤:↑_ : ℕ↑ → ℕ → hProp₀
M ≤:↑ n = n is-an-upper-bound-of M

≤p-is-upward-closed : {n : ℕ} → (n ≤p_) is-upward-closed
≤p-is-upward-closed = λ n m z z₁ → ≤-trans z₁ z

_^↑ : ℕ → ℕ↑
n ^↑ = (n ≤p_) , ≤p-is-upward-closed


-- 0 is bounded above by every number.
O↑ : ℕ↑
O↑ = 0 ^↑

