{-# OPTIONS --cubical --safe #-}
module Cubical.Relation.Binary.Base where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.HITs.SetQuotients.Base

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

module BinaryRelation {ℓ ℓ' : Level} {A : Type ℓ} (R : A → A → Type ℓ') where
  isRefl : Type (ℓ-max ℓ ℓ')
  isRefl = (a : A) → R a a

  isSym : Type (ℓ-max ℓ ℓ')
  isSym = (a b : A) → R a b → R b a

  isTrans : Type (ℓ-max ℓ ℓ')
  isTrans = (a b c : A)  → R a b → R b c → R a c

  record isEquivRel : Type (ℓ-max ℓ ℓ') where
    constructor EquivRel
    field
      reflexive : isRefl
      symmetric : isSym
      transitive : isTrans

  isPropValued : Type (ℓ-max ℓ ℓ')
  isPropValued = (a b : A) → isProp (R a b)

  isEffective : Type (ℓ-max ℓ ℓ')
  isEffective = (a b : A) →
    let x : A / R
        x = [ a ]
        y : A / R
        y = [ b ]
    in (x ≡ y) ≃ R a b

_on_ : (B → B → C) → (A → B) → (A → A → C)
_*_ on f = λ x y → f x * f y
