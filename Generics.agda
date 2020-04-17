{-# OPTIONS --cubical --safe #-}
module Generics where

open import Cubical.Foundations.Everything

Constant : {ℓ : Level} -> Type ℓ -> Type ℓ
Constant A = A

UnOp : {ℓ : Level} -> Type ℓ -> Type ℓ
UnOp A = A → A

BinOp : {ℓ : Level} -> Type ℓ -> Type ℓ
BinOp A = A → A → A

ActLeft : {ℓ : Level} -> Type ℓ -> Type ℓ -> Type ℓ
ActLeft A B = A → B → B

ActRight : {ℓ : Level} -> Type ℓ -> Type ℓ -> Type ℓ
ActRight A B = B -> A -> B

_associates-with-left_ : {ℓ : Level} -> {A B : Type ℓ} -> BinOp A -> ActLeft A B -> Type ℓ
_associates-with-left_ {A = A} {B = B} _**_ _&&_ = (a b : A) (c : B) -> (a ** b) && c ≡ a && (b && c)

_associates-with-right_ : {ℓ : Level} -> {A B : Type ℓ} -> BinOp A -> ActRight A B -> Type ℓ
_associates-with-right_ {A = A} {B = B} _**_ _&&_ = (a : B) (b c : A) -> (a && b) && c ≡ a && (b ** c)

_is-associative : {ℓ : Level} -> {A : Type ℓ} -> BinOp A -> Type ℓ
_is-associative {A = A} _**_ = (a b c : A) -> (a ** b) ** c ≡ a ** (b ** c) 

_is-commutative : {ℓ : Level} -> {A : Type ℓ} -> BinOp A -> Type ℓ
_is-commutative {A = A} _**_ = (a b : A) -> a ** b ≡ b ** a

_distributes-over-left_ : {ℓ : Level} -> {A B : Type ℓ} -> (_**_ : ActLeft A B) -> (_++_ : BinOp B) -> Type ℓ
_distributes-over-left_ {A = A} {B = B} _**_ _++_ = (a : A) (b c : B) -> a ** (b ++ c) ≡ (a ** b) ++ (a ** c)

_distributes-over-right_ : {ℓ : Level} -> {A B : Type ℓ} -> (_**_ : ActRight A B) -> (_++_ : BinOp B) -> Type ℓ
_distributes-over-right_ {A = A} {B = B} _**_ _++_ =  (a b : B) (c : A) -> (a ++ b) ** c ≡ (a ** c) ++ (b ** c) 

_is-left-unit-for_ : {ℓ : Level} -> {A B : Type ℓ} -> Constant A -> ActLeft A B -> Type ℓ
_is-left-unit-for_ {A = A} {B = B} 1' _**_ = (b : B) -> 1' ** b ≡ b

_is-right-unit-for_ : {ℓ : Level} -> {A B : Type ℓ} -> Constant A -> ActRight A B -> Type ℓ
_is-right-unit-for_ {A = A} {B = B} 1' _**_ = (b : B) -> b ** 1' ≡ b

_annihilates_on-left-to_ : {ℓ : Level} -> {A B : Type ℓ} -> Constant A -> ActLeft A B -> Constant B -> Type ℓ
_annihilates_on-left-to_ {A = A} {B = B} 0' _**_ 0'' = (b : B) -> 0' ** b ≡ 0''

_annihilates_on-right-to_ : {ℓ : Level} -> {A B : Type ℓ} -> Constant A -> ActRight A B -> Constant B -> Type ℓ
_annihilates_on-right-to_ {A = A} {B = B} 0' _**_ 0'' = (b : B) -> b ** 0' ≡ 0''

