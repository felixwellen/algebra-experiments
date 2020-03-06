{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude

module AbelianGroup where

  record abelian-group-structure {A : Type₀} : Type₀ where
    field
      _+_ : A → A → A
      -_ : A → A
      0′ : A                    -- 0\'

      +-is-associative : (x y z : A) → x + (y + z) ≡ (x + y) + z
      +-is-unital : (x : A) → x + 0′ ≡ x
      +-is-commutative : (x y : A) → x + y ≡ y + x
      +-has-inverses : (x : A) → x + (- x) ≡ 0′


