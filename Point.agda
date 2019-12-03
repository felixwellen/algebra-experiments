{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude

module Point where

data OnePointType : Type₀ where
  point : OnePointType
