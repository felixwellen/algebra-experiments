{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Ring

module FreeAlgebra (R : Type₀) {{ ring-structure-on-R : ring-structure {R} }} where
infixl 15 _·_
infixl 10 _+_

open ring-structure ring-structure-on-R
  using ()
  renaming (_·_ to _·s_; _+_ to _+s_; -_ to -s_; 0′ to 0s; 1′ to 1s)

data R[_] (I : Type₀) : Type₀ where
  var : I → R[ I ]
  const : R → R[ I ]
  _+_ : R[ I ] → R[ I ] → R[ I ]
  -_ : R[ I ] → R[ I ]
  0′ : R[ I ]

  +-is-associative : (x y z : R[ I ]) → x + (y + z) ≡ (x + y) + z
  +-is-unital : (x : R[ I ]) → x + 0′ ≡ x
  +-is-commutative : (x y : R[ I ]) → x + y ≡ y + x
  +-has-inverses : (x : R[ I ]) → x + (- x) ≡ 0′

  _·_ : R[ I ] → R[ I ] → R[ I ]            -- \cdot
  1′ : R[ I ]
  ·-is-associative : (x y z : R[ I ]) → x · (y · z) ≡ (x · y) · z
  ·-is-unital : (x : R[ I ]) → 1′ · x ≡ x
  ·-is-commutative : (x y : R[ I ]) → x · y ≡ y · x

  distributive : (x y z : R[ I ]) → (x + y) · z ≡ x · z + y · z
  
  _⋆_ : R → R[ I ] → R[ I ]        -- \*
  ⋆-associates-with-· : (s t : R) (x : R[ I ]) → s ⋆ (t ⋆ x) ≡ (s ·s t) ⋆ x
  ⋆-distributes-with-+ : (s t : R) (x : R[ I ]) → (s +s t) ⋆ x ≡ s ⋆ x + t ⋆ x
  1-acts-trivial : (x : R[ I ]) → 1s ⋆ x ≡ x

  is-0-truncated : (x y : R[ I ]) (p q : x ≡ y) → p ≡ q

module _ (I : Type₀) where
  instance 
    is-ring : ring-structure {R[ I ]}
    is-ring = record
              { _+_ = _+_
              ; -_ = -_
              ; 0′ = 0′
              ; +-is-associative = +-is-associative
              ; +-is-unital = +-is-unital
              ; +-is-commutative = +-is-commutative
              ; +-has-inverses = +-has-inverses
              ; _·_ = _·_
              ; 1′ = 1′
              ; ·-is-associative = ·-is-associative
              ; ·-is-unital = ·-is-unital
              ; ·-is-commutative = ·-is-commutative
              ; distributive = distributive
              }

  is-algebra : algebra-structure R {R[ I ]}
  is-algebra = record
               { _⋆_ = _⋆_
               ; ⋆-associates-with-· = ⋆-associates-with-·
               ; ⋆-distributes-with-+ = ⋆-distributes-with-+
               ; 1-acts-trivial = 1-acts-trivial
               }

module free-structures (I : Type₀) where
  instance
    free-ring : ring-structure {R[ I ]}
    free-ring = is-ring I

  instance
    free-algebra : algebra-structure R {R[ I ]}
    free-algebra = is-algebra I 
