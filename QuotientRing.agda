{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties
open import Basics
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

    differenceIsTranslationInvariant : ∀ (x a b : R)
                                       → a - b ≡ (x + a) - (x + b)
    differenceIsTranslationInvariant x a b =
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

    homogenity : ∀ (x a b : R)
                 → (a - b ∈ I)
                 → (x + a) - (x + b) ∈ I
    homogenity x a b p = subst (λ u → u ∈ I) (differenceIsTranslationInvariant x a b) p
      where 
      
    translate : R → R/I → R/I
    translate x = elim
                    (λ r → squash/)
                    (λ y → [ x + y ])
                    λ y y' diffrenceInIdeal → eq/ (x + y) (x + y') (homogenity x y y' diffrenceInIdeal)

    isSetR/I : isSet R/I
    isSetR/I = squash/
    [_]/I : (a : R) → R/I
    [ a ]/I = [ a ]

    lemma : (x y a : R)
            → x - y ∈ I
            → [ x + a ]/I ≡ [ y + a ]/I
    lemma x y a x-y∈I = eq/ (x + a) (y + a) (subst (λ u → I u holds) calculate x-y∈I)
      where calculate : x - y ≡ (x + a) - (y + a)
            calculate =
                      x - y                 ≡⟨ differenceIsTranslationInvariant a x y ⟩
                      ((a + x) - (a + y))   ≡⟨ cong (λ u → u - (a + y)) (+-is-commutative _ _) ⟩ 
                      ((x + a) - (a + y))   ≡⟨ cong (λ u → (x + a) - u) (+-is-commutative _ _) ⟩ 
                      ((x + a) - (y + a))   ∎
    
    homogenity' : (x y : R) → (x - y ∈ I) 
                  → translate x ≡ translate y
    homogenity' x y x-y∈I i r = pointwise-equal r i
      where
        pointwise-equal : ∀ (u : R/I)
                          → translate x u ≡ translate y u
        pointwise-equal = elimProp (λ u → isSetR/I (translate x u) (translate y u))
                                   (λ a → lemma x y a x-y∈I)

    _+/I_ : R/I → R/I → R/I
    x +/I y = (elim R/I→R/I-isSet translate homogenity' x) y
      where
        R/I→R/I-isSet = (λ r →  isOfHLevelΠ 2 (λ _ → squash/))
