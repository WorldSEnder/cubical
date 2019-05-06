{-# OPTIONS --cubical #-}

module Cubical.Data.Reals.LFT where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Reals.LFT.IntHelpers
open import Cubical.Data.Reals.LFT.Rationals
  renaming (_≤_ to _≤ℚ_)
open import Cubical.Codata.Stream
open import Cubical.HITs.SetQuotients
open import Cubical.Relation.Nullary
open import Cubical.Data.Prod

data Digit : Type₀ where
  +1 +0 −1 : Digit

-- initially, we start with the interval [-1, 1]
-- observing +1 corresponds to tightening the interval to the right:  [0  ,  1]
-- observing +0 corresponds to tightening the interval to the middle: [-.5, .5]
-- observing -1 corresponds to tightening the interval to the left:   [-1 ,  0]
-- as can be seen, +0 , +1 , x ≡ +1 , -1 , x
-- and             +0 , -1 , x ≡ -1 , +1 , x
I₀ : Type₀
I₀ = Stream Digit

-- a 1-LFT is a linear fractional transformation, interpreted
-- as the function given by L(x) = (ax + c) / (bx + d)
-- note that this corresponds to the above interpretation
-- of interval semantics of digit streams.
-- we could ‌// by a multiplicative factor share between a b c d
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
  --                  = determinant / (d^2 - b^2)
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
    0<∣d∣-∣b∣ = {!!}

    ¬d≡0 : ¬ (d ≡ Int.pos 0)
    ¬d≡0 d≡0 = 0<∣x∣⇒¬x≡0 d (≤<-trans (mag-positive _) magb<magd) (sym d≡0)

    ¬d+b≡0 : ¬ (d + b ≡ Int.pos 0)
    ¬d+b≡0 d+b≡0 = 0<∣x∣⇒¬x≡0 _ {!!} (sym d+b≡0)

    ¬d-b≡0 : ¬ (d - b ≡ Int.pos 0)
    ¬d-b≡0 d-b≡0 = <-not-eq (Int.pos 0) (d - b) {!!} (sym d-b≡0)

    monotonicity : isMonotonic
    monotonicity = {!!}

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
  {-
    field
      L[-1]≤1  : endpoint-1 ≤ℚ 1ℚ
      -1≤L[-1] : -1ℚ ≤ℚ endpoint-1
      L[+1]≤1  : endpoint1 ≤ℚ 1ℚ
      -1≤L[+1] : -1ℚ ≤ℚ endpoint-1
    -- a bounded interval is small (enough to be always admit a digit extraction)
    -- if its length is < 1/4
    isSmallEnough : Type₀
    isSmallEnough = (numerator interval-length * Int.pos 4) < Int.pos (denominator interval-length)
  -}

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
  Lift : (pre-lft : pre-LFT₁) → (hasProp : pre-lft-prop pre-lft) → Lifted pre-lft-prop [ pre-lft ]

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
    [ LFT-Mat (Int.pos 0 + m .a) (Int.pos 0 + m .b)
              (Int.pos 0 + (Int.pos 0 + m .c)) (Int.pos 0 + (Int.pos 0 + m .d)) ]
  ≡[ i ]⟨ [ LFT-Mat (pos0+ (m .a) (~ i)) (pos0+ (m .b) (~ i))
                    (pos0+ (pos0+ (m .c) (~ i)) (~ i)) (pos0+ (pos0+ (m .d) (~ i)) (~ i)) ] ⟩
    [ m ]
  ∎ where
  open pre-LFT₁
*lft-id-l : ∀ m → id-lft *lft m ≡ m
*lft-id-l = elimSetQuotientsProp (λ _ → squash/ _ _) λ m → 
    [ LFT-Mat (Int.pos 1 * m .a + Int.pos 0 * m .b)
              (Int.pos 0 * m .a + Int.pos 1 * m .b)
              (Int.pos 1 * m .c + Int.pos 0 * m .d)
              (Int.pos 0 * m .c + Int.pos 1 * m .d) ]
  ≡[ i ]⟨ [ LFT-Mat (pos1* (m .a) i + pos0* (m .b) (~ i))
                    (pos0* (m .a) (~ i) + pos1* (m .b) i)
                    (pos1* (m .c) i + pos0* (m .d) (~ i))
                    (pos0* (m .c) (~ i) + pos1* (m .d) i) ] ⟩
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
^-1-pre-inv m ¬det≡0 = lft-eq-from-path _ (determinant m) ¬det≡0 _ path where
  open pre-LFT₁ m
  eq-a : determinant m * Int.pos 1 ≡ a * d + c * (- b)
  eq-a = sym (pos0+ _) ∙ cong (a * d +_) (cong -_ (*-comm b c) ∙ *neg c b)
  eq-b : Int.pos 0 ≡ b * d + d * (- b)
  eq-b = sym (neg-refl (b * d)) ∙ cong (b * d +_) (cong -_ (*-comm b d) ∙ *neg d b)
  eq-c : Int.pos 0 ≡ a * (- c) + c * a
  eq-c = sym (neg-refl (c * a)) ∙ (cong (c * a +_) (cong -_ (*-comm c a) ∙ *neg a c) ∙ +-comm (c * a) _)
  eq-d : determinant m * Int.pos 1 ≡ b * (- c) + d * a
  eq-d = sym (pos0+ _) ∙ cong (a * d +_) (*neg b c) ∙ +-comm (a * d) _ ∙ cong (b * (- c) +_) (*-comm a d) 
  path : (determinant m *pre-lft-int id-pre-lft) ≡ (m *pre-lft (m ^-1-pre-lft))
  path i = LFT-Mat (eq-a i) (eq-b i) (eq-c i) (eq-d i)

^-1-inv : ∀ m → invertible₁ m → id-lft ≡ m *lft (m ^-1)
^-1-inv _ (Lift pre-lft hasProp) = eq/ _ _ (^-1-pre-inv pre-lft hasProp)

digit2prelft : Digit → pre-LFT₁
pre-LFT₁.a (digit2prelft digit) = Int.pos 1
pre-LFT₁.b (digit2prelft digit) = Int.pos 0
pre-LFT₁.c (digit2prelft +1) = Int.pos 1
pre-LFT₁.c (digit2prelft +0) = Int.pos 0
pre-LFT₁.c (digit2prelft −1) = Int.negsuc 0
pre-LFT₁.d (digit2prelft digit) = Int.pos 2

digit2lft : Digit → LFT₁
digit2lft d = [ digit2prelft d ]

digit-bounded : ∀ d → bounded₁ (digit2lft d)
digit-bounded +1 = Lift _ record { magb<magd = 1 , refl }
digit-bounded +0 = Lift _ record { magb<magd = 1 , refl }
digit-bounded −1 = Lift _ record { magb<magd = 1 , refl }

data DigitList : Type₀ where
  [] : DigitList
  _∷_ : Digit → DigitList → DigitList

sift : DigitList → LFT₁ → LFT₁
sift [] lft = lft
sift (d ∷ ds) lft = sift ds (lft *lft digit2lft d)

prepend : DigitList → Stream Digit → Stream Digit
prepend [] xs = xs
prepend (x ∷ ds) xs = x , prepend ds xs

record StreamPrefix (ds : Stream Digit) : Type₀ where
  field
    prefix : DigitList
    rest : Stream Digit
    isPrefix : prepend prefix rest ≡ ds

record splitting₁-rec (Rec : LFT₁ → Type₀) (m : LFT₁) : Type₀ where
  inductive
  field
    splitDigit : Digit
    leftover : LFT₁
    isSplit : m ≡ digit2lft splitDigit *lft leftover
    leftoverExtracts : Rec leftover

record extracting₁ (m : LFT₁) : Type₀ where
  coinductive
  field
    cont : (ds : Stream Digit)
         → Σ[ pref ∈ StreamPrefix ds ] splitting₁-rec extracting₁ (sift (pref .StreamPrefix.prefix) m)

module Unfold (A : LFT₁ → Type₀) where
  record extracting₁-BaseF (m : LFT₁) : Type₀ where
    inductive
    field
      cont : (ds : Stream Digit)
           → Σ[ pref ∈ StreamPrefix ds ] splitting₁-rec A (sift (pref .StreamPrefix.prefix) m)
  -- a kind of unfold of the coinductive extracting₁
  module _ (α : ∀ {m} → A m → extracting₁-BaseF m) where
    open extracting₁ renaming (cont to cont-ext)
    unfold-extracting : ∀ {m} → A m → extracting₁ m
    unfold-extracting refm .cont-ext ds = pref , record
      { splitDigit = x .splitDigit
      ; leftover = x .leftover
      ; isSplit = x .isSplit
      ; leftoverExtracts = unfold-extracting (x .leftoverExtracts)
      } where
        open splitting₁-rec
        ΣprefX = α refm .extracting₁-BaseF.cont ds
        pref = fst ΣprefX
        x = snd ΣprefX
open Unfold refining₁

fundamental-theorem : ∀ {m}
                    → refining₁ m
                    → extracting₁ m
fundamental-theorem = unfold-extracting fundamental-theorem-alg where
  fundamental-theorem-alg : ∀ {m} → refining₁ m → extracting₁-BaseF m
  fundamental-theorem-alg (Lift pre-lft isRefining) = record
    { cont = cont } where
    -- to extract a digit to the left, we multiply
    -- by the inverse of the digit's LFT matrix
    -- the result must be a refining matrix to
    -- continually invoke again the fundamental theorem
    -- etc...
    -- pulling the digit (+ k) we multiply on the right
    -- [a c] * [1 k] = [a (ka+2c)]
    -- [b d]   [0 2]   [b (kb+2d)]
    -- the new determinant = 2*old determinant
    -- but the lengths and L(0) are not at all "nicely"
    -- changed. We need a good bound for ((2d+kb)^2 - b^2)/(d^2 - b^2),
    -- which should be at least > 2.
    --     ((2d+kb)^2 - b^2)/(d^2 - b^2) ≥ 2 + C
    -- <=> (bounded₁)
    --     (2d+kb)^2 - b^2 ≥ 2 * (d^2 - b^2) + C * (d^2 - b^2)
    -- <=>
    --     2d^2 + 2kdb - C * (d^2 - b^2) + (k^2)b^2 + b^2 > 0
    -- <=>
    --     (k^2)b^2 + b^2 ≥ 0
    --  ∧  2d^2 + 2kdb - C * (d^2 - b^2)
    --          (v  this might have been - , 0 , or +, depending on k, minus gives the worst bound)
    --    ≥ 2d^2 - 2∣ db ∣ - C * (d^2 - b^2)
    --    ≥ 2∣ d ∣(∣ d ∣ - ∣ b ∣) - C * (∣ d ∣^2 - ∣ b ∣^2) ≥ 0
    -- choose C(b, d) = 2∣ d ∣(∣ d ∣ - ∣ b ∣) / (∣ d ∣^2 - ∣ b ∣^2)
    --                = 2∣ d ∣ / (∣ d ∣ + ∣ b ∣)
    --                = 2 - ∣ b ∣ / (∣ d ∣ + ∣ b ∣)
    -- note C > 0
    -- finally, note that ∣ kb + 2d ∣ > ∣ d ∣
    -- and C is monotonically growing with ∣ d ∣ and constant ∣ b ∣
    -- so the first bound is conservative, even after a constant amount of digits
    -- and the algorithm terminates in finite time.
    -- ∎
    -- notice though that this preserves bounded₁ and refining₁
    -- also the magnitude of d is strictly monotonically growing.
    -- this should be clear because we are doing LF function
    -- composition here.
    --
    -- to extract the digit (- k) we multiply with the inverse
    -- but on the left
    -- [2 k] * [a c] = [(2a+kb) (2c+kd)]
    -- [0 1]   [b d]   [b       d      ]   
    -- notice that this preserves b and d, hence also bounded₁.
    -- the new determinant = 2*old determinant, and the lengths
    -- are also all doubled evenly around the midpoint.
    -- I.e., emitting a 0 corresponds to blowing up the interval
    -- around 0 by doubling all values.
    -- Emitting a 1 corresponds to blowing up the interval around
    -- 1 by double every value's difference to 1.

    -- The following is a sufficient, but not a necessary condition
    -- to be able to emit at least 1 digit:
    -- If an interval has length ≤ 1/4 then at least one of these
    -- blowups safely keeps the interval after emission in [-1, 1]:
    -- Suppose the left endpoint is in [-1, -1/2], then the right
    -- endpoint is in [-1, 0] and we can safely emit -1.
    -- Suppose the left endpoint is in [-1/2, 0], then the right
    -- endpoint is in [-1/2, 1/2] and we can emit 0.
    -- Suppose the left endpoint is in [0, 1], then we can safely
    -- emit a 1.
    -- naturally overlaps are possible. If the interval is [.2, .4]
    -- then we can either emit a 0 with a new interval [.4, .8], then
    -- emit a 1 with new interval [-.2, .6]
    -- OR
    -- emit a 1 with a new interval of [-.6, -.2] then emit a -1
    -- with new interval [-.2, .6]. Again we see 0,1 ~~ 1,-1.
    cont : (ds : Stream Digit)
         → Σ[ pref ∈ StreamPrefix ds ] splitting₁-rec refining₁ (sift (pref .StreamPrefix.prefix) [ pre-lft ])
    cont ds = {!!} , record
      { splitDigit = {!!}
      ; leftover = {!!}
      ; isSplit = {!!}
      ; leftoverExtracts = {!!}
      }

record ExtractionMachine : Type₀ where
  coinductive
  field
    nextDigit : Digit
    {state} : LFT₁
    extractingState : extracting₁ state
    next : ExtractionMachine

projectDigits : ExtractionMachine → Stream Digit
Stream.head (projectDigits machine) = ExtractionMachine.nextDigit machine
Stream.tail (projectDigits machine) = projectDigits (ExtractionMachine.next machine)

fold-over : ∀ {m} → extracting₁ m → Stream Digit → ExtractionMachine
fold-over {m = m} fundamental stream = unfold where
  open extracting₁ fundamental
  prefixTail = cont stream
  prefix = fst prefixTail
  split = snd prefixTail
  tail = prefix .StreamPrefix.rest
  open splitting₁-rec split
  -- given all the above, we can give a resulting digit stream
  unfold : ExtractionMachine
  ExtractionMachine.nextDigit unfold = splitDigit
  ExtractionMachine.state unfold = leftover
  ExtractionMachine.extractingState unfold = leftoverExtracts
  ExtractionMachine.next unfold = fold-over leftoverExtracts tail

fold-over' : ∀ {m} → refining₁ m → Stream Digit → ExtractionMachine
fold-over' refining = fold-over (fundamental-theorem refining)
