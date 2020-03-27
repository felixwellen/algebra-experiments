{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties
open import Basics
open import AbelianGroup
open import Ring

module QuotientRing where

module ideal {R : Type₀}  ⦃ _ : ring-structure {R} ⦄ where
  open ring-structure ⦃...⦄
  record is-ideal (I : R → hProp₀) : Type₀ where
    field
      +-closed : {x y : R} (_ : I(x) holds) (_ : I(y) holds) → I(x + y) holds
      -closed : {x : R} (_ : I(x) holds) → I(- x) holds
      0′-closed : I(0′) holds
      ·-closed : {r x : R} (_ : I(x) holds) → I(r · x) holds

    I′ : Type₀
    I′ = Σₛ I

    _+′_ : I′ → I′ → I′
    (x , p) +′ (y , q) = (x + y , +-closed p q)

    +-is-associative-I : (x y z : I′) → x +′ (y +′ z) ≡ (x +′ y) +′ z
    +-is-associative-I (x , p) (y , q) (z , r) =
                      subtypeEqual′ {P = I}
                        ((x , p) +′ ((y , q) +′ (z , r)))
                        (((x , p) +′ (y , q)) +′ (z , r))
                        (+-is-associative x y z)

    is-abelian-group : abelian-group-structure {I′}
    is-abelian-group = record
                         { _+_ = _+′_
                         ; -_ = λ {(x , p) → (- x) , -closed p}
                         ; 0′ = 0′ , 0′-closed
                         ; +-is-associative = +-is-associative-I
                         ; +-is-unital = λ {(x , _) → subtypeEqual′ {P = I} _ _ (+-is-unital x)}
                         ; +-is-commutative = λ {(x , _) (y , _)
                                                → subtypeEqual′ {P = I} _ _ (+-is-commutative x y)}
                         ; +-has-inverses = λ {(x , _)
                                            →  subtypeEqual′ {P = I} _ _ (+-has-inverses x) }
                         }


  mod-syntax : ∀ {ℓ ℓ'} {A : Type ℓ} (R : A → A → Type ℓ') (x y : A / R) → Type (ℓ-max ℓ ℓ') 
  mod-syntax {A = A} R = PathP (λ i → A / R)

  syntax mod-syntax R x y = x ≡ y mod R
  
  module _ (I : R → hProp₀) (isIdeal : is-ideal I) where
    differenceIsInIdeal : R → R → Type₀
    differenceIsInIdeal x y = I(x - y) holds


    Q : Type₀
    Q = R / differenceIsInIdeal

    homogenity : (x a b : R) (_ : differenceIsInIdeal a b)
                 → differenceIsInIdeal (x + a) (x + b)
    homogenity x a b p = subst (λ u → I(u) holds) calculation p
      where calculation = a - b               ≡⟨ {!!} ⟩
                          ((x + a) - (x + b)) ∎
      
    translate : R → Q → Q
    translate x = elim (λ r → squash/)
                       (λ y → [ x + y ])
                       λ y y' diffrenceInIdeal → eq/ (x + y) (x + y') (homogenity x y y' diffrenceInIdeal)

    homogenity' : (x x' : R) (_ : differenceIsInIdeal x x')
                  → translate x ≡ translate x'
    homogenity' x x' differenceInIdeal =
      λ i y → elim
                (λ z → {!!})
                (λ y' → eq y' i)
                {!!}
                {!!}
      where zz : (y : R) → (x + y) - (x' + y) ≡ x - x'
            zz y = (x + y) - (x' + y)  ≡⟨ {!!} ⟩
                   x - x'              ∎
            eq : (y : R)
                 → [ x + y ] ≡ [ x' + y ] mod differenceIsInIdeal
            eq y = eq/ (x + y) (x' + y)
                       (subst (λ u → I(u) holds) (sym (zz y)) differenceInIdeal)
            
    _+/_ : Q → Q → Q
    _+/_ = elim
             (λ r → isOfHLevelPi 2 λ _ → squash/)
             translate
             homogenity'

