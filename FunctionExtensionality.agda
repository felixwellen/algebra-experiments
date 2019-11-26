{-# OPTIONS --without-K #-}

open import Basics

module FunctionExtensionality where

postulate
  function-extensionality : (A : Set) (P : A → Set)
                            → (f g : (a : A) → P a)
                            → ((a : A) → f(a) ≈ g(a)) → f ≈ g

fun-ext : {A : Set} {P : A → Set}
            → {f g : (a : A) → P a}
            → ((a : A) → f(a) ≈ g(a)) → f ≈ g
fun-ext = function-extensionality _ _ _ _
