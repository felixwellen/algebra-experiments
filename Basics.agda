{-# OPTIONS --without-K --safe #-}

module Basics where

data Empty : Set where

data Point : Set where
  0″ : Point
  
¬_ : Set → Set
¬ A = A → Empty

absurd : (A : Set) → Empty → A
absurd A ()

infixl 5 _and_
data _and_ (A B : Set) : Set where
  ⟨_and_⟩ : A → B → A and B

pr1 : {A B : Set}
      → A and B → A
pr1 ⟨ x and _ ⟩ = x      

infix 6 _≈_
data _≈_ {A : Set} (a : A) : A → Set where
  refl : a ≈ a

ap : {A B : Set} {a a′ : A} (f : A → B) → (a ≈ a′) → f a ≈ f a′
ap f refl = refl

≈-is-transitive : {A : Set} {x y z : A} → x ≈ y → y ≈ z → x ≈ z
≈-is-transitive refl p = p

≈-is-symmetric : {A : Set} {x y : A} → x ≈ y → y ≈ x
≈-is-symmetric refl = refl

_≈∎ : {A : Set} (x : A) → x ≈ x
_≈∎ x = refl {a = x}

infixr 5 _≈⟨_⟩_
infix 6 _≈∎

_≈⟨_⟩_ : {A : Set} {y z : A} (x : A) (p : x ≈ y) (q : y ≈ z) → x ≈ z
x ≈⟨ p ⟩ q = ≈-is-transitive p q

