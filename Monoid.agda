{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Basics
open import Naturals
open import List

module Monoid where

record monoid-struct {A : Set} : Set where
  infix 7 _*_ 
  field
    _*_ : A → A → A
    unit : A
    associative : (a b c : A) → ((a * b) * c) ≡ (a * (b * c))
    unital : (a : A) → ((a * unit) ≡ a) and (a ≡ (unit * a))


instance
  monoid-struct-on-ℕ : monoid-struct
  monoid-struct-on-ℕ =
    record {
         _*_ = _+ℕ_ ;
         unit = zero ;
         associative =  +ℕ-is-associative ;
         unital = +ℕ-is-unital
         }
  
instance
  monoid-struct-on-lists : {A : Set} → monoid-struct
  monoid-struct-on-lists {A} =
    record {
      _*_ = _⊕_ ;
      unit = [] ;
      associative = ⊕-is-associative {A} ;
      unital = ⊕-is-unital
    }

record monoid-morphism-struct
       {A B : Set}
       {{A-is-monoid : monoid-struct {A}}}
       {{B-is-monoid : monoid-struct {B}}}
       (f : A → B) : Set where
  open monoid-struct A-is-monoid renaming (unit to unit-A; _*_ to _*A_)
  open monoid-struct B-is-monoid renaming (unit to unit-B; _*_ to _*B_)
  field
    unital : f unit-A ≡ unit-B
    homomorphic : (x y : A) → f (x *A y) ≡ f x *B f y


length-homomorphic :  {A : Set} (l l′ : list A)
  → length (l ⊕ l′) ≡ length l +ℕ length l′
length-homomorphic [] l′ = refl
length-homomorphic (x ∷ l) l′ = cong succ (length-homomorphic l l′)


lists-ℕ : {A : Set} → monoid-morphism-struct length
lists-ℕ {A} =
  record {
    unital = refl ;
    homomorphic = length-homomorphic {A}
  }

[_] : {A : Set} → A → list A
[ a ] = a ∷ []

record []-monoid-struct {A : Set} : Set where
  field
    _*_ : A → A → A
    *[] : list A → A
    is-left-inverse : (a : A) → *[] [ a ] ≡ a
    *[]-homomorphic : (l l′ : list A) → *[] (l ⊕ l′) ≡ (*[] l) * (*[] l′)

  unit : A
  unit = *[] []

  *[_] : A → A
  *[ x ] = *[] [ x ]

  *-is-associative : (x y z : A) →  x * (y * z) ≡ (x * y) * z
  *-is-associative x y z =
                         (x * (y * z))                 ≡⟨ cong (λ u → x * (y * u)) (sym (is-left-inverse z)) ⟩
                         (x * (y * *[ z ]))            ≡⟨ cong (λ u → x * (u * *[ z ])) (sym (is-left-inverse y)) ⟩
                         (x * (*[ y ] * *[ z ]))       ≡⟨ cong (λ u → x * u) (sym (*[]-homomorphic [ y ] [ z ])) ⟩
                         (x * *[] (y ∷ [ z ]))         ≡⟨ cong (λ u → u * *[] (y ∷ [ z ])) (sym (is-left-inverse x)) ⟩
                         (*[ x ] * *[] (y ∷ [ z ]))    ≡⟨ sym (*[]-homomorphic [ x ] (y ∷ [ z ])) ⟩
                         *[] (x ∷ y ∷ [ z ])           ≡⟨ *[]-homomorphic (x ∷ [ y ]) [ z ] ⟩
                         (*[] (x ∷ [ y ]) * *[ z ])    ≡⟨ cong (λ u → (*[] (x ∷ [ y ]) * u)) (is-left-inverse z) ⟩ 
                         (*[] (x ∷ [ y ]) * z)         ≡⟨ cong (λ u → u * z) (*[]-homomorphic [ x ] [ y ]) ⟩ 
                         ((*[ x ] * *[ y ]) * z)       ≡⟨ cong (λ u → (u * *[ y ]) * z) (is-left-inverse x) ⟩ 
                         ((x * *[ y ]) * z)            ≡⟨ cong (λ u → (x * u) * z) (is-left-inverse y) ⟩ 
                         ((x * y) * z)                 ∎ 

