{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude

module Basics where

data Empty : Set where

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

