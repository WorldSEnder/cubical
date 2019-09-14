{-# OPTIONS --cubical #-}

module Cubical.Data.Reals.LFT.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
  renaming (_*_ to _*ℕ_; _+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
  using (<-wellfounded) renaming (_<_ to _<ℕ_)
open import Cubical.Data.Int
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Reals.LFT.IntHelpers
  using (inspect; _with≡_; ≤-transport; pos1*; *pos1)
  renaming (_≤_ to _≤Int_; _<_ to _<Int_;
            _≤?_ to _≤Int?_; ∣_∣ to ∣_∣ℤ;
            _*_ to _*ℤ_; mag to magInt;
            *-zeroˡ to *Int-zeroˡ)
open import Cubical.HITs.PropositionalTruncation
  renaming (∣_∣ to trunc)
open import Cubical.Induction.WellFounded
open import Cubical.Relation.Binary

data ℚ : Type₀ where
  _/1+_ : (m : Int) → (n : ℕ) → ℚ

private
  _over_ : Int → Int → ℚ
  n over pos zero = pos 0 /1+ 0
  n over pos (suc m) = n /1+ m
  n over negsuc m = (- n) /1+ m
  false-val : ∀ {a}{A : Type a}
            → Dec A → Type₀
  false-val (yes _) = ⊥
  false-val (no _) = Unit
  
_over_by_ : Int → (n : Int) → ¬ n ≡ Int.pos 0 → ℚ
n over m by ¬m≡0 = m over n

_over-const_ : Int → (m : Int) → {prf : false-val (discreteInt m (pos 0))} → ℚ
_over-const_ n m {prf} with inspect (discreteInt m (pos 0))
...                      | yes _ with≡ path = ⊥-elim (transport (λ i → false-val (path i)) prf)
...                      | no ¬m≡0 with≡ path = n over m by ¬m≡0

numerator : ℚ → Int
numerator (a /1+ b) = a

denominator : ℚ → ℕ
denominator (a /1+ b) = suc b

Int→ℚ : Int → ℚ
Int→ℚ n = n over-const (pos 1)

1ℚ : ℚ
1ℚ = (pos 1) over-const (pos 1)

0ℚ : ℚ
0ℚ = (pos 0) over-const (pos 1)

-1ℚ : ℚ
-1ℚ = (negsuc 0) over-const (pos 1)

∣_∣ : ℚ → ℚ
∣ m /1+ n ∣ = ∣ m ∣ℤ /1+ n
mag-numerator : ∀ q → numerator ∣ q ∣ ≡ ∣ numerator q ∣ℤ
mag-numerator (m /1+ n) = refl
mag-denominator : ∀ q → denominator ∣ q ∣ ≡ denominator q
mag-denominator (m /1+ n) = refl

_≤_ : (r : ℚ) (s : ℚ) → Type₀
r ≤ s = numerator r *ℤ pos (denominator s) ≤Int numerator s *ℤ pos (denominator r)

_<_ : (r : ℚ) (s : ℚ) → Type₀
r < s = numerator r *ℤ pos (denominator s) <Int numerator s *ℤ pos (denominator r)

0≤∣x∣ : ∀ x → 0ℚ ≤ ∣ x ∣
0≤∣x∣ x = magInt (numerator x) , reason where
  reason : pos 0 *ℤ pos (denominator ∣ x ∣) + pos (magInt (numerator x)) ≡ numerator ∣ x ∣ *ℤ pos 1
  reason =
    pos 0 *ℤ pos (denominator ∣ x ∣) + pos (magInt (numerator x)) ≡[ i ]⟨ *Int-zeroˡ (pos (denominator ∣ x ∣)) i + pos (magInt (numerator x)) ⟩
    pos 0 + pos (magInt (numerator x))                            ≡⟨ sym (pos0+ _) ⟩
    ∣ numerator x ∣ℤ                                              ≡⟨ sym (mag-numerator x) ⟩
    numerator ∣ x ∣                                               ≡⟨ sym (*pos1 _) ⟩
    numerator ∣ x ∣ *ℤ pos 1                                      ∎

_≤?_ : ∀ r s → Dec (r ≤ s)
_ ≤? _ = _ ≤Int? _

_*_ : ℚ → ℚ → ℚ
(r /1+ s) * (u /1+ v) = (r *ℤ u) /1+ (s +ℕ v +ℕ s *ℕ v)

module LogarithmicRecursion (C : ℚ) (c<1 : ∣ C ∣ < 1ℚ) where
  numC<denomC : ∣ numerator C ∣ℤ <Int pos (denominator C)
  numC<denomC = ≤-transport pathNumerator pathDenominator c<1 where
    pathNumerator : sucInt ∣ numerator C ∣ℤ ≡ sucInt (numerator ∣ C ∣ *ℤ pos (denominator 1ℚ))
    pathNumerator = cong sucInt (sym (mag-numerator C) ∙ sym (*pos1 _))
    pathDenominator : numerator 1ℚ *ℤ pos (denominator ∣ C ∣) ≡ pos (denominator C)
    pathDenominator = pos1* _ ∙ cong pos (mag-denominator C)

  min0 : Int → ℕ
  min0 (pos n) = n
  min0 (negsuc n) = 0

  discreteLog : ℚ → Int
  discreteLog = {!!}

  discreteLogSuc : ∀ q → discreteLog (q * C) ≡ sucInt (discreteLog q)
  discreteLogSuc = {!!}

  discreteLogBase : discreteLog 1ℚ ≡ pos 0
  discreteLogBase = {!!}

  discreteLogNat : ℚ → ℕ
  discreteLogNat q = min0 (discreteLog q)

  logOrder : ℚ → ℚ → Type₀
  logOrder = _<ℕ_ on discreteLogNat

  wellFoundedLogOrder : WellFounded logOrder
  wellFoundedLogOrder = InverseImage.wellFounded discreteLogNat <-wellfounded
