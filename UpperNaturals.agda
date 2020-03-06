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
open import Basics hiding (¬_)

module UpperNaturals where

hProp₀ = hProp ℓ-zero

_holds : ∀ {ℓ} → hProp ℓ → Type ℓ
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

false : hProp₀
false = Empty , λ {()}

Empty-is-hProp : isOfHLevel 1 Empty
Empty-is-hProp = λ {()}

¬ : ∀ {ℓ} → hProp ℓ → hProp ℓ
¬ (P , isProp-P) = (P → Empty) , propPi (λ _ → Empty-is-hProp)

-- Infinity is defined to be the number with no upper bounds.
∞↑ : ℕ↑
∞↑ = (λ _ → false) , proof
  where proof : (λ _ → false) is-upward-closed
        proof = λ n m _ z → z

∞↑-has-no-upper-bounds : (n : ℕ) → ¬ (∞↑ ≤:↑ n) holds
∞↑-has-no-upper-bounds n = λ x → x

≤:↑-refl : {n : ℕ} → (n is-an-upper-bound-of (n ^↑)) holds
≤:↑-refl = ≤-refl


-- The ordering on the upper naturals is defined by saying that
-- N is at most M if every upper bound of M is an upper bound of N.
_≤↑_ : ℕ↑ → ℕ↑ → Type _
N ≤↑ M = (n : ℕ) → (M ≤:↑ n) holds → (N ≤:↑ n) holds

≤↑-is-a-prop : {N M : ℕ↑} → isProp (N ≤↑ M) 
≤↑-is-a-prop {N} {M} = propPi (λ n → propPi λ x → snd (N ≤:↑ n))

≤↑-refl : {N : ℕ↑} → N ≤↑ N
≤↑-refl = λ n z → z

≤↑-trans : {N M P : ℕ↑} → N ≤↑ M → M ≤↑ P → N ≤↑ P
≤↑-trans = λ z z₁ n z₂ → z n (z₁ n z₂)

^↑-is-monotone : {n m : ℕ} → n ≤ m → (n ^↑) ≤↑ (m ^↑)
^↑-is-monotone = λ x k x₁ → ≤-trans x x₁

^↑-yoneda : {n : ℕ} {M : ℕ↑} → M ≤↑ (n ^↑) → (M ≤:↑ n) holds
^↑-yoneda {n} {M} = λ x → x n ≤:↑-refl

{-
^↑-is-full : {n m : ℕ} → (n ^↑) ≤↑ (m ^↑) → n ≤ m
^↑-is-full {n} {m} = λ z → z m {!!}
-}
{-
≤-antisym in cubical
≤-antisymmetry : {n m : ℕ} (_ : n ≤ m) (_ : m ≤ n) → n ≡ m
≤-antisymmetry {_} {_} (inl p) _ = p
≤-antisymmetry {_} {_} _ (inl p) = ! p
≤-antisymmetry {_} {_} (inr p) q = quodlibet (<-to-≱ p q)

ℕ↑-prop : SubtypeProp (ℕ → Prop₀) _
ℕ↑-prop = _is-upward-closed , upward-closed-is-a-prop



^↑-yoneda : {n : ℕ} {M : ℕ↑} → M ≤↑ (n ^↑) → M ≤:↑ n
^↑-yoneda {n} {M} = λ x → x n ≤:↑-refl

^↑-is-full : {n m : ℕ} → (n ^↑) ≤↑ (m ^↑) → n ≤ m
^↑-is-full {n} {m} = λ z → z m (inl idp)





^↑-is-ff : {n m : ℕ} → (n ≤ m) ≃ ((n ^↑) ≤↑ (m ^↑))
^↑-is-ff {n} {m} = equiv ^↑-is-monotone ^↑-is-full
  (λ b → prop-path (≤↑-is-a-prop {(n ^↑)} {(m ^↑)}) (λ _ → ≤-trans (b m (inl idp))) b)
  (λ a → prop-path ≤-is-prop (≤-trans a (inl idp)) a)

=-to-≤↑ : {N M : ℕ↑} → N == M → N ≤↑ M
=-to-≤↑ idp = λ n z → z

^↑-is-injective : {n m : ℕ} → (n ^↑) == (m ^↑) → n == m
^↑-is-injective {n} {m}  =
  λ x → ≤-antisymmetry (^↑-is-full (=-to-≤↑ x)) (^↑-is-full ((=-to-≤↑ (! x))))

O↑≤↑ : (N : ℕ↑) → O↑ ≤↑ N
O↑≤↑ N = λ n x → ^↑-is-monotone (O≤ n) n ≤:↑-refl

_≤↑∞↑ : (N : ℕ↑) → N ≤↑ ∞↑
N ≤↑∞↑ = λ n x → quodlibet (∞↑-has-no-upper-bounds n x)


minℕ : (P : ℕ → Type₀) → ℕ↑
minℕ P =
  (λ n → min-pred n) ,
    (λ n m x → Trunc-rec (implication n m x))
  where
    min-pred : (n : ℕ) → Prop₀
    min-pred n = ∃ (λ k → (P k) And (k ≤ n))

    implication : (n m : ℕ) (x : n ≤ m)
                  → Σ ℕ (λ k → (P k) And (k ≤ n))
                  → min-pred m holds
    implication n m x = λ {(k , p) → [ k , fst p , ≤-trans (snd p) x ] }

{- Probably requires propositional resizing
minℕ↑ : (P : ℕ↑ → Type₀) → ℕ↑
minℕ↑ P =
  (λ n → min-pred n) ,
    (λ n m x → Trunc-rec (implication n m x))
  where
    min-pred : (n : ℕ) → Prop₀
    min-pred n = ∃ (λ K → (P K) And (K ≤:↑ n))
    implication : (n m : ℕ) (x : n ≤ m)
                  → Σ ℕ↑ (λ K → (P K) And (K ≤:↑ n))
                  → min-pred m holds
    implication n m x = λ {(k , p) → [ k , fst p , ≤-trans (snd p) x ] }
-}
-}
