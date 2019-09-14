{-# OPTIONS --cubical #-}

module Cubical.Data.Reals.LFT.Matrix where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Reals.LFT.IntHelpers
open import Cubical.Data.Reals.LFT.Rationals
  renaming (_≤_ to _≤ℚ_; ∣_∣ to ∣_∣ℚ)
open import Cubical.HITs.SetQuotients
open import Cubical.Relation.Nullary

-- a 1-LFT is a linear fractional transformation, interpreted
-- as the function given by L(x) = (ax + c) / (bx + d)
-- note that this corresponds to the above interpretation
-- of interval semantics of digit streams.
-- we can / by a multiplicative factor shared between a b c d
-- as this would describe the same function.
-- L'(x) = a / (bx + d) - b(ax + c) / (bx + d)^2
--       = (ad - bc) / (bx + d)^2
record pre-LFT₁ : Type₀ where
  constructor LFT-Mat
  field
    a b c d : Int

_*pre-lft_ : pre-LFT₁ → pre-LFT₁ → pre-LFT₁
m *pre-lft n = LFT-Mat (m .a * n .a + m .c * n .b)
                       (m .b * n .a + m .d * n .b)
                       (m .a * n .c + m .c * n .d)
                       (m .b * n .c + m .d * n .d) where open pre-LFT₁

_*pre-lft-int_ : Int → pre-LFT₁ → pre-LFT₁
k *pre-lft-int m = LFT-Mat (k * m .a) (k * m .b) (k * m .c) (k * m .d) where open pre-LFT₁

_^-1-pre-lft : pre-LFT₁ → pre-LFT₁
m ^-1-pre-lft = LFT-Mat (m .d) (- m .b) (- m .c) (m .a) where open pre-LFT₁

module _ (lft : pre-LFT₁) where
  -- the following contains a few important variables that are unchanged for pre-LFT₁-eq
  -- related matrices:
  -- we can canonically calculate the "midpoint" and endpoints of a bounded LFT:
  --     L(0)         = c / d
  -- we can canonically calculate the (directed) length of a bounded LFT:
  --     L(1) - L(0)  = (c + a)/(d + b) - c / d
  --                  =  determinant / (d(d + b))
  --     L(-1) - L(0) = (c - a)/(d - b) - c / d
  --                  = -determinant / (d(d - b))
  --     L(1) - L(-1) = determinant * (1/(d(d + b)) + 1/(d(d - b)))
  --                  = determinant * ((d-b + d+b)/(d(d^2-b^2)))
  --                  = 2 * determinant / (d^2 - b^2)
  open pre-LFT₁ lft
  data pre-LFT₁-eq : pre-LFT₁ → Type₀ where
    pre-LFT₁-eq-con : ∀ k → ¬ (k ≡ Int.pos 0)
                    → (pre-LFT₁-eq (k *pre-lft-int lft))

  lft-eq-from-path : ∀ k → ¬ (k ≡ Int.pos 0) → ∀ lft₂ → k *pre-lft-int lft ≡ lft₂ → pre-LFT₁-eq lft₂
  lft-eq-from-path k ¬k≡0 _ eq = transport (cong pre-LFT₁-eq eq) (pre-LFT₁-eq-con k ¬k≡0)

  determinant : Int
  determinant = a * d - b * c
  isInvertible : Type₀
  isInvertible = ¬ (determinant ≡ Int.pos 0)
  signature : Int
  signature = d * d - b * b
  isMonotonic : Type₀
  isMonotonic = ¬ (signature ≡ Int.pos 0)

  -- a LFT₁ is bounded if the denominator can not be 0 on [-1, 1].
  -- note that this implies monotonicity
  record bounded₁-pre : Type₀ where
    field
      magb<magd : ∣ b ∣ < ∣ d ∣

    0<∣d∣-∣b∣ : Int.pos 0 < (∣ d ∣ - ∣ b ∣)
    0<∣d∣-∣b∣ = begin<
      Int.pos 0      ≤≡⟨ 0≡n-n ∣ b ∣ ⟩
      ∣ b ∣ - ∣ b ∣ <⟨ <-stepsʳ _ _ (- ∣ b ∣) magb<magd ⟩
      ∣ d ∣ - ∣ b ∣ ≤∎

    ¬d≡0 : ¬ (d ≡ Int.pos 0)
    ¬d≡0 = 0<∣x∣⇒¬x≡0 d (begin<
      Int.pos 0 ≤⟨ mag-positive b ⟩
      ∣ b ∣    <⟨ magb<magd ⟩
      ∣ d ∣    ≤∎)

    ¬d+b≡0 : ¬ (d + b ≡ Int.pos 0)
    ¬d+b≡0 = 0<∣x∣⇒¬x≡0 _ (begin<
      Int.pos 0      <⟨ 0<∣d∣-∣b∣ ⟩
      ∣ d ∣ - ∣ b ∣ ≤⟨ mag-triangle-inv d b ⟩
      ∣ d + b ∣     ≤∎)

    ¬d-b≡0 : ¬ (d - b ≡ Int.pos 0)
    ¬d-b≡0 = 0<∣x∣⇒¬x≡0 _ (begin<
      Int.pos 0        <⟨ 0<∣d∣-∣b∣ ⟩
      ∣ d ∣ - ∣ b ∣   ≤≡⟨ (λ i → ∣ d ∣ - mag-neg-absorb b (~ i)) ⟩
      ∣ d ∣ - ∣ - b ∣ ≤⟨ mag-triangle-inv d (- b) ⟩
      ∣ d - b ∣       ≤∎)

    monotonicity : isMonotonic
    monotonicity a2-b2≡0 = ¬a≡0∧¬b≡0⇒¬ab≡0 ¬d-b≡0 ¬d+b≡0 (binomial-formula d b ∙ a2-b2≡0)

    interval-length : ℚ
    interval-length = determinant over signature by monotonicity

    midpoint : ℚ
    midpoint = c over d by ¬d≡0

    endpoint1 : ℚ
    endpoint1 = (c + a) over (d + b) by ¬d+b≡0

    endpoint-1 : ℚ
    endpoint-1 = (c - a) over (d - b) by ¬d-b≡0

  -- a LFT₁ is refining if L([-1, 1]) ⊆ [-1, 1]
  -- since we can not give this axiomatically, as we will define the interpretation
  -- of L on I₀ only later, we derive this from the fact that L(x) is monotonic iff
  -- it is bounded and L(-1) ∈ [-1, 1] and L(1) ∈ [-1, 1]
  record refining₁-pre : Type₀ where
    field
      bounded : bounded₁-pre
    open bounded₁-pre bounded public
    field
      L[-1]≤1  : endpoint-1 ≤ℚ 1ℚ
      -1≤L[-1] : -1ℚ ≤ℚ endpoint-1
      L[+1]≤1  : endpoint1 ≤ℚ 1ℚ
      -1≤L[+1] : -1ℚ ≤ℚ endpoint-1

    -- a bounded interval is small (enough to be always admit a digit extraction)
    -- if its length is < 1/2
    isSmallEnough : Type₀
    isSmallEnough = ∣ interval-length ∣ℚ ≤ℚ (Int.pos 1 over-const Int.pos 2)

  open refining₁-pre using (isSmallEnough; bounded) public
  open bounded₁-pre using (monotonicity; interval-length; midpoint; endpoint1; endpoint-1) public

*pre-linear-left : ∀ k m n → (k *pre-lft-int m) *pre-lft n ≡ k *pre-lft-int (m *pre-lft n)
*pre-linear-left k m n i =
  LFT-Mat (*-distrib-assocˡ-+ k (m .a) (n .a) (m .c) (n .b) i)
          (*-distrib-assocˡ-+ k (m .b) (n .a) (m .d) (n .b) i)
          (*-distrib-assocˡ-+ k (m .a) (n .c) (m .c) (n .d) i)
          (*-distrib-assocˡ-+ k (m .b) (n .c) (m .d) (n .d) i) where
  open pre-LFT₁

*pre-linear-right : ∀ k m n → m *pre-lft (k *pre-lft-int n) ≡ k *pre-lft-int (m *pre-lft n)
*pre-linear-right k m n i =
  LFT-Mat (*-distrib-assocʳ-+ k (m .a) (n .a) (m .c) (n .b) i)
          (*-distrib-assocʳ-+ k (m .b) (n .a) (m .d) (n .b) i)
          (*-distrib-assocʳ-+ k (m .a) (n .c) (m .c) (n .d) i)
          (*-distrib-assocʳ-+ k (m .b) (n .c) (m .d) (n .d) i) where
  open pre-LFT₁

^-1-pre-linear : ∀ k m → (k *pre-lft-int m) ^-1-pre-lft ≡ k *pre-lft-int (m ^-1-pre-lft)
^-1-pre-linear k m i =
  LFT-Mat (k * m .d)
          (*neg k (m .b) i)
          (*neg k (m .c) i)
          (k * m .a) where
  open pre-LFT₁

LFT₁ : Type₀
LFT₁ = pre-LFT₁ / pre-LFT₁-eq

data Lifted (pre-lft-prop : pre-LFT₁ → Type₀) : LFT₁ → Type₀ where
  Lift-pre : (pre-lft : pre-LFT₁) → (hasProp : pre-lft-prop pre-lft) → Lifted pre-lft-prop [ pre-lft ]

invertible₁ = Lifted isInvertible
bounded₁ = Lifted bounded₁-pre
refining₁ = Lifted refining₁-pre

id-pre-lft : pre-LFT₁
id-pre-lft = LFT-Mat (Int.pos 1) (Int.pos 0) (Int.pos 0) (Int.pos 1)
id-lft : LFT₁
id-lft = [ id-pre-lft ]

_*lft_ : LFT₁ → LFT₁ → LFT₁
_*lft_ = elimSetQuotientOp₂ _*pre-lft_ leftPath rightPath where
  leftPath : (a b c : pre-LFT₁) → pre-LFT₁-eq a b → pre-LFT₁-eq (a *pre-lft c) (b *pre-lft c)
  leftPath a _ c (pre-LFT₁-eq-con k ¬k≡0) = lft-eq-from-path _ k ¬k≡0 _ (sym (*pre-linear-left k a c))
  rightPath : (c a b : pre-LFT₁) → pre-LFT₁-eq a b → pre-LFT₁-eq (c *pre-lft a) (c *pre-lft b)
  rightPath c a _ (pre-LFT₁-eq-con k ¬k≡0) = lft-eq-from-path _ k ¬k≡0 _ (sym (*pre-linear-right k c a))

*lft-id-r : ∀ m → m *lft id-lft ≡ m
*lft-id-r = elimSetQuotientsProp (λ _ → squash/ _ _) λ m →
    [ LFT-Mat (m .a * Int.pos 1 + m .c * Int.pos 0)
              (m .b * Int.pos 1 + m .d * Int.pos 0)
              (m .a * Int.pos 0 + m .c * Int.pos 1)
              (m .b * Int.pos 0 + m .d * Int.pos 1) ]
  ≡[ i ]⟨ [ LFT-Mat (*pos1 (m .a) i + *-zeroʳ (m .c) i)
                    (*pos1 (m .b) i + *-zeroʳ (m .d) i)
                    (*-zeroʳ (m .a) i + *pos1 (m .c) i)
                    (*-zeroʳ (m .b) i + *pos1 (m .d) i) ] ⟩
    [ LFT-Mat (m .a) (m .b)
              (Int.pos 0 + m .c) (Int.pos 0 + m .d) ]
  ≡[ i ]⟨ [ LFT-Mat (m .a) (m .b) (pos0+ (m .c) (~ i)) (pos0+ (m .d) (~ i)) ] ⟩
    [ m ]
  ∎ where
  open pre-LFT₁

*lft-id-l : ∀ m → id-lft *lft m ≡ m
*lft-id-l = elimSetQuotientsProp (λ _ → squash/ _ _) λ m →
    [ LFT-Mat (Int.pos 1 * m .a + Int.pos 0 * m .b)
              (Int.pos 0 * m .a + Int.pos 1 * m .b)
              (Int.pos 1 * m .c + Int.pos 0 * m .d)
              (Int.pos 0 * m .c + Int.pos 1 * m .d) ]
  ≡[ i ]⟨ [ LFT-Mat (pos1* (m .a) i + *-zeroˡ (m .b) i)
                    (*-zeroˡ (m .a) i + pos1* (m .b) i)
                    (pos1* (m .c) i + *-zeroˡ (m .d) i)
                    (*-zeroˡ (m .c) i + pos1* (m .d) i) ] ⟩
    [ LFT-Mat (m .a) (Int.pos 0 + m .b)
              (m .c) (Int.pos 0 + m .d) ]
  ≡[ i ]⟨ [ LFT-Mat (m .a) (pos0+ (m .b) (~ i)) (m .c) (pos0+ (m .d) (~ i)) ] ⟩
    [ m ]
  ∎ where
  open pre-LFT₁

_^-1 : LFT₁ → LFT₁
_^-1 = elimSetQuotientOp₁ _^-1-pre-lft path where
  path : (a b : pre-LFT₁) → pre-LFT₁-eq a b → pre-LFT₁-eq (a ^-1-pre-lft) (b ^-1-pre-lft)
  path a _ (pre-LFT₁-eq-con k ¬k≡0) = transport (sym (cong (pre-LFT₁-eq _) (^-1-pre-linear k a))) (pre-LFT₁-eq-con k ¬k≡0)

^-1-pre-inv : ∀ m → isInvertible m → pre-LFT₁-eq id-pre-lft (m *pre-lft (m ^-1-pre-lft))
^-1-pre-inv m ¬det≡0 = lft-eq-from-path id-pre-lft (determinant m) ¬det≡0 _ path where
  open pre-LFT₁ m
  eq-a : determinant m * Int.pos 1 ≡ a * d + c * (- b)
  eq-a = *pos1 (determinant m) ∙ cong (a * d +_) (neg* b c ∙ *-comm (- b) c)
  eq-b : determinant m * Int.pos 0 ≡ b * d + d * (- b)
  eq-b = *-zeroʳ (determinant m) ∙ sym (neg-refl (b * d)) ∙ cong (b * d +_) (neg* b d ∙ *-comm (- b) d)
  eq-c : determinant m * Int.pos 0 ≡ a * (- c) + c * a
  eq-c = *-zeroʳ (determinant m) ∙ sym (neg-refl (c * a)) ∙ +-comm (c * a) _ ∙ cong (_+ c * a) (neg* c a ∙ *-comm (- c) a)
  eq-d : determinant m * Int.pos 1 ≡ b * (- c) + d * a
  eq-d = *pos1 (determinant m) ∙ cong (a * d +_) (*neg b c) ∙ +-comm (a * d) (b * - c) ∙ cong (b * (- c) +_) (*-comm a d)
  path : (determinant m *pre-lft-int id-pre-lft) ≡ (m *pre-lft (m ^-1-pre-lft))
  path i = LFT-Mat (eq-a i) (eq-b i) (eq-c i) (eq-d i)

^-1-inv : ∀ m → invertible₁ m → id-lft ≡ m *lft (m ^-1)
^-1-inv _ (Lift-pre pre-lft hasProp) = eq/ _ _ (^-1-pre-inv pre-lft hasProp)
