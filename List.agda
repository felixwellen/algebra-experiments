{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Basics
open import Naturals

module List where

data list (A : Set) : Set where
  [] : list A
  _∷_ : A → list A → list A     -- \::

pattern [_] z = z ∷ []

infixr 25 _∷_

module _ {A : Set} where

  infixl 30 _⊕_ -- \o+
  _⊕_ : list A → list A → list A
  [] ⊕ l′ = l′
  (x ∷ l) ⊕ l′ = x ∷ (l ⊕ l′)

  length : list A → ℕ
  length [] = zero
  length (x ∷ l) = succ (length l)

  ⊕-is-unital : (l : list A) → (l ⊕ [] ≡ l) and (l ≡ [] ⊕ l)
  ⊕-is-unital [] = ⟨ refl and refl ⟩
  ⊕-is-unital (x ∷ l) = ⟨ cong (λ l′ → x ∷ l′) (pr1 (⊕-is-unital l)) and refl ⟩

  ⊕-is-associative : (l l′ l″ : list A)
                     → (l ⊕ l′) ⊕ l″ ≡ l ⊕ (l′ ⊕ l″)
  ⊕-is-associative [] l′ l″ = refl
  ⊕-is-associative (x ∷ l) l′ l″ = cong (λ l → x ∷ l) (⊕-is-associative l l′ l″)

  reverse : list A → list A
  reverse [] = []
  reverse (x ∷ l) = append-at-end (reverse l) x
    where
      append-at-end : list A → A → list A
      append-at-end [] x = [ x ]
      append-at-end (y ∷ l) x = y ∷ (append-at-end l x)

map : {A B : Set} → (A → B) → list A → list B
map f [] = []
map f (x ∷ l) = f x ∷ map f l

-- list comprehension syntax
syntax map (λ x → Expr) l = [ Expr ∣ x ∈ l ]

pattern [_∣_] y z = y ∷ z ∷ []
pattern [_∣_∣_] x y z = x ∷ y ∷ z ∷ []
pattern [_∣_∣_∣_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_∣_∣_∣_∣_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_∣_∣_∣_∣_∣_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []
