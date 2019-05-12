{-# OPTIONS --cubical #-}

module Cubical.Data.Reals.LFT.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat hiding (_*_)
open import Cubical.Data.Int
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty
open import Cubical.Data.Reals.LFT.IntHelpers
  renaming (_≤_ to _≤Int_; _≤?_ to _≤Int?_)
open import Cubical.HITs.PropositionalTruncation
  renaming (∣_∣ to trunc)

data ℚ : Type₀ where
  _/1+_ : Int → ℕ → ℚ

_over-signed_ : Int → (m : Signed) → ℚ
n over-signed posSuc x = n /1+ x
n over-signed neut = pos 0 /1+ 0 -- ⊥-elim (¬m≡0 refl)
n over-signed negSuc x = n /1+ x

_over_by_ : Int → (n : Int) → ¬ n ≡ Int.pos 0 → ℚ
n over m by ¬m≡0 = n over-signed (Int→Signed m) where
  open Iso
  ¬sm≡neut : ¬ (Int→Signed m ≡ neut)
  ¬sm≡neut sm≡neut = ¬m≡0 (transport (λ i → Int≃Signed .leftInv m i ≡ pos 0) λ i → Signed→Int (sm≡neut i))

numerator : ℚ → Int
numerator (a /1+ b) = a

denominator : ℚ → ℕ
denominator (a /1+ b) = suc b

Int→ℚ : Int → ℚ
Int→ℚ n = n /1+ 0

1ℚ : ℚ
1ℚ = Int→ℚ (pos 1)

-1ℚ : ℚ
-1ℚ = Int→ℚ (negsuc 0)

_≤_ : (r : ℚ) (s : ℚ) → Type₀
r ≤ s = numerator r * pos (denominator s) ≤Int numerator s * pos (denominator r)

_≤?_ : ∀ r s → Dec (r ≤ s)
_ ≤? _ = _ ≤Int? _
