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
      ·-closed : {x : R} → (r : R) → x ∈ I → r · x ∈ I
  
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
    lemma x y a x-y∈I = eq/ (x + a) (y + a) (subst (λ u → u ∈ I) calculate x-y∈I)
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

    +/I-is-commutative : (x y : R/I) → x +/I y ≡ y +/I x
    +/I-is-commutative = elimProp (λ x → isOfHLevelΠ 1 λ y → squash/ (x +/I y) (y +/I x))
                                      (λ x' → elimProp (λ _ → squash/ _ _)
                                                       λ y' → eq x' y') 
                                                       
       where eq : (x y : R) → [ x ] +/I [ y ] ≡ [ y ] +/I [ x ]
             eq x y i =  [ +-is-commutative x y i ]

    +/I-is-associative : (x y z : R/I) → x +/I (y +/I z) ≡ (x +/I y) +/I z
    +/I-is-associative = elimProp
                           (λ x → isOfHLevelΠ 1 λ y → isOfHLevelΠ 1 λ z → squash/ _ _)
                           (λ x' → elimProp
                                     (λ y → isOfHLevelΠ 1 λ z → squash/ _ _)
                                     λ y' → elimProp (λ z → squash/ _ _)
                                                     (λ z' → eq x' y' z'))
                                                     
      where eq : (x y z : R) → [ x ] +/I ([ y ] +/I [ z ]) ≡ ([ x ] +/I [ y ]) +/I [ z ]
            eq x y z i =  [ +-is-associative x y z i ]

    0/I : R/I
    0/I = [ 0′ ]

    1/I : R/I
    1/I = [ 1′ ]

    -/I : R/I → R/I
    -/I = elim (λ _ → squash/) (λ x' → [ - x' ]) eq
      where
        eq : (x y : R) → (x - y ∈ I) → [ - x ] ≡ [ - y ]
        eq x y x-y∈I = eq/ (- x) (- y) (subst (λ u → u ∈ I) eq' (is-ideal.-closed isIdeal x-y∈I))
          where
            eq' = - (x + (- y))       ≡⟨ sym (-isDistributive _ _) ⟩
                  (- x) - (- y)       ∎

    +/I-has-inverses : (x : R/I) → x +/I (-/I x) ≡ 0/I
    +/I-has-inverses = elimProp (λ x → squash/ _ _) eq
      where
        eq : (x : R) → [ x ] +/I (-/I [ x ]) ≡ 0/I
        eq x i = [ +-has-inverses x i ]

    
    +/I-is-unital : (x : R/I) → x +/I 0/I ≡ x
    +/I-is-unital = elimProp (λ x → squash/ _ _) eq
      where
        eq : (x : R) → [ x ] +/I 0/I ≡ [ x ]
        eq x i = [ +-is-unital x i ]

    _·/I_ : R/I → R/I → R/I
    _·/I_ =
      elim (λ x → isOfHLevelΠ 2 (λ y → squash/))
               (λ x → left· x)
               eq'
      where
        eq : (x y y' : R) → (y - y' ∈ I) → [ x · y ] ≡ [ x · y' ]
        eq x y y' y-y'∈I = eq/ _ _ (subst (λ u → u ∈ I)
                                          (x · (y - y')            ≡⟨ right-distributive _ _ _ ⟩
                                          ((x · y) + x · (- y'))   ≡⟨ cong (λ u → (x · y) + u) (-commutes-with-· x y')  ⟩
                                          (x · y) - (x · y')       ∎)
                                          (is-ideal.·-closed isIdeal x y-y'∈I))
        left· : (x : R) → R/I → R/I
        left· x = elim (λ y → squash/)
                     (λ y → [ x · y ])
                     (eq x)
        eq' : (x x' : R) → (x - x' ∈ I) → left· x ≡ left· x' 
        eq' x x' x-x'∈I i y = elimProp (λ y → squash/ (left· x y) (left· x' y))
                                       (λ y → eq′ y)
                                       y i
                              where
                                eq′ : (y : R) → left· x [ y ] ≡ left· x' [ y ]
                                eq′ y = eq/ (x · y) (x' · y)
                                            (subst (λ u → u ∈ I)
                                                   (y · (x - x')            ≡⟨ right-distributive _ _ _ ⟩
                                                   (y · x) + (y · (- x'))   ≡⟨ cong (λ u → (y · x) + u) (-commutes-with-· y x') ⟩
                                                   (y · x) - (y · x')       ≡⟨ cong (λ u → u - (y · x')) (·-is-commutative y x) ⟩
                                                   (x · y) - (y · x')       ≡⟨ cong (λ u → (x · y) - u) (·-is-commutative y x') ⟩
                                                   x · y - (x' · y)         ∎)
                                                   (is-ideal.·-closed isIdeal y x-x'∈I))

    -- copy paste from '+/I' - this is preliminary anyway
    ·/I-is-commutative : (x y : R/I) → x ·/I y ≡ y ·/I x
    ·/I-is-commutative = elimProp (λ x → isOfHLevelΠ 1 λ y → squash/ (x ·/I y) (y ·/I x))
                                      (λ x' → elimProp (λ _ → squash/ _ _)
                                                       λ y' → eq x' y') 
       where eq : (x y : R) → [ x ] ·/I [ y ] ≡ [ y ] ·/I [ x ]
             eq x y i =  [ ·-is-commutative x y i ]

    ·/I-is-associative : (x y z : R/I) → x ·/I (y ·/I z) ≡ (x ·/I y) ·/I z
    ·/I-is-associative = elimProp
                           (λ x → isOfHLevelΠ 1 λ y → isOfHLevelΠ 1 λ z → squash/ _ _)
                           (λ x' → elimProp
                                     (λ y → isOfHLevelΠ 1 λ z → squash/ _ _)
                                     λ y' → elimProp (λ z → squash/ _ _)
                                                     (λ z' → eq x' y' z'))
                                                     
      where eq : (x y z : R) → [ x ] ·/I ([ y ] ·/I [ z ]) ≡ ([ x ] ·/I [ y ]) ·/I [ z ]
            eq x y z i =  [ ·-is-associative x y z i ]

    ·/I-is-unital : (x : R/I) → 1/I ·/I x ≡ x
    ·/I-is-unital = elimProp (λ x → squash/ _ _) eq
      where
        eq : (x : R) → 1/I ·/I [ x ] ≡ [ x ]
        eq x i = [ ·-is-unital x i ]


    /I-distributive : (x y z : R/I) → (x +/I y) ·/I z ≡ (x ·/I z) +/I (y ·/I z)
    /I-distributive = elimProp (λ x → isOfHLevelΠ 1 λ y → isOfHLevelΠ 1 λ z → squash/ _ _)
                               (λ x → elimProp (λ y → isOfHLevelΠ 1 λ z → squash/ _ _)
                                               (λ y → elimProp (λ z → squash/ _ _)
                                                               {!λ z → eq x y z!}))
      where
        eq : (x y z : R) → ([ x ] +/I [ y ]) ·/I [ z ] ≡ ([ x ] ·/I [ z ]) +/I ([ y ] ·/I [ z ])
        eq x y z i = [ distributive x y z i ]


    has-ring-structure : ring-structure {R/I} 
    has-ring-structure = record
                           { _+_ = _+/I_
                           ; -_ = -/I
                           ; 0′ = 0/I
                           ; +-is-associative = +/I-is-associative
                           ; +-is-unital = +/I-is-unital
                           ; +-is-commutative = +/I-is-commutative
                           ; +-has-inverses = +/I-has-inverses
                           ; _·_ = _·/I_
                           ; 1′ = 1/I
                           ; ·-is-associative = ·/I-is-associative
                           ; ·-is-unital = ·/I-is-unital
                           ; ·-is-commutative = ·/I-is-commutative
                           ; distributive = /I-distributive
                           }
