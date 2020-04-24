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

  infix 5 _∈_
  _∈_ : {X : Type₀} → (x : X) → (P : X → hProp₀) → Type₀
  x ∈ P = P(x) holds

  record is-ideal (I : R → hProp₀) : Type₀ where
    field
      +-closed : {x y : R} → x ∈ I → y ∈ I → x + y ∈ I
      -closed : {x : R} → x ∈ I → - x ∈ I
      0′-closed : 0′ ∈ I
      ·-closed : {r x : R} → x ∈ I → r · x ∈ I
  
  module _ (I : R → hProp₀) (isIdeal : is-ideal I) where
    R/I : Type₀
    R/I = R / (λ x y → x - y ∈ I)

    homogenity : ∀ (x a b : R)
                 → (a - b ∈ I)
                 → (x + a) - (x + b) ∈ I
    homogenity x a b p = subst (λ u → I(u) holds) calculation p
      where calculation =
              a - b                       ≡⟨ cong (λ u → a + u)
                                                  (sym (+-is-unital′ _)) ⟩
              (a + (0′ + (- b)))          ≡⟨ cong (λ u → a + (u + (- b)))
                                                  (sym (+-has-inverses _)) ⟩
              (a + ((x + (- x)) + (- b))) ≡⟨ cong (λ u → a + u)
                                                  (+-is-associative′ _ _ _) ⟩
              (a + (x + ((- x) + (- b)))) ≡⟨ sym (+-is-associative′ _ _ _) ⟩
              ((a + x) + ((- x) + (- b))) ≡⟨ cong (λ u → u + ((- x) + (- b)))
                                                  (+-is-commutative _ _) ⟩
              ((x + a) + ((- x) + (- b))) ≡⟨ cong (λ u → (x + a) + u)
                                                  (-isDistributive _ _) ⟩
              ((x + a) - (x + b)) ∎
      
    translate : R → R/I → R/I
    translate x = elim
                    (λ r → squash/)
                    (λ y → [ x + y ])
                    λ y y' diffrenceInIdeal → eq/ (x + y) (x + y') (homogenity x y y' diffrenceInIdeal)

{-
    isSetR/I : isSet R/I
    isSetR/I = squash/

    homogenity' : (x y : R) → (x - y ∈ I) 
                  → translate x ≡ translate y
    homogenity' x y x-y∈I i r = pointwise-equal r i
      where
        pointwise-equal : ∀ (u : R/I)
                          → translate x u ≡ translate y u
        pointwise-equal = elim (λ u p q → {!isSetR/I !}) {!!} {!!} {!!}
        
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
-}
