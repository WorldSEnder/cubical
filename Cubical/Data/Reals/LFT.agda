{-# OPTIONS --cubical #-}

module Cubical.Data.Reals.LFT where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Reals.LFT.IntHelpers
open import Cubical.Data.Reals.LFT.Rationals
  renaming (_≤_ to _≤ℚ_)
open import Cubical.Data.Reals.LFT.Matrix
open import Cubical.Codata.Stream
open import Cubical.HITs.SetQuotients
open import Cubical.Relation.Nullary
open import Cubical.Data.Prod
open import Agda.Builtin.List
open import Cubical.Data.List
  hiding ([_])

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
digit-bounded +1 = Lift-pre _ record { magb<magd = 1 , refl }
digit-bounded +0 = Lift-pre _ record { magb<magd = 1 , refl }
digit-bounded −1 = Lift-pre _ record { magb<magd = 1 , refl }

DigitList : Type₀
DigitList = List Digit

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

record splitting₁-pre-rec (Rec : pre-LFT₁ → Type₀) (m : pre-LFT₁) : Type₀ where
  inductive
  field
    splitDigit : Digit
    leftover : pre-LFT₁
    isSplit : m ≡ digit2prelft splitDigit *pre-lft leftover
    leftoverExtracts : Rec leftover

smallEnough⇒splitting₁-pre : ∀ {lft}
                           → (ref : refining₁-pre lft)
                           → isSmallEnough ref
                           → splitting₁-pre-rec refining₁-pre lft
smallEnough⇒splitting₁-pre refining smallEnough = {!!}

module UnfoldDefs (A : LFT₁ → Type₀) where
  record splitting₁-rec (m : LFT₁) : Type₀ where
    field
      splitDigit : Digit
      leftover : LFT₁
      isSplit : m ≡ digit2lft splitDigit *lft leftover
      leftoverExtracts : A leftover

  record SplittingSolution (m : LFT₁) (ds : Stream Digit) : Type₀ where
    field
      prefix : StreamPrefix ds
      isSplitting : splitting₁-rec (sift (prefix .StreamPrefix.prefix) m)
    open splitting₁-rec isSplitting public

  record extracting₁-BaseF (m : LFT₁) : Type₀ where
    inductive
    field
      cont : (ds : Stream Digit) → SplittingSolution m ds

record extracting₁ (m : LFT₁) : Type₀ where
  coinductive
  field
    cont : (ds : Stream Digit)
         → UnfoldDefs.SplittingSolution extracting₁ m ds

module UnfoldCoalg (A : LFT₁ → Type₀) (open UnfoldDefs) (α : ∀ {m} → A m → extracting₁-BaseF A m) where
  unfold-extracting : ∀ {m} → A m → extracting₁ m
  unfold-extracting refm .extracting₁.cont ds = record
    { prefix = prefix
    ; isSplitting = record
      { splitDigit = splitDigit
      ; leftover = leftover
      ; isSplit = isSplit
      ; leftoverExtracts = unfold-extracting leftoverExtracts
    } } where
      solution = α refm .extracting₁-BaseF.cont ds
      open SplittingSolution solution

module _ where
  open UnfoldDefs refining₁
  open UnfoldCoalg refining₁

  fundamental-theorem-alg : ∀ {m} → refining₁ m → extracting₁-BaseF m
  fundamental-theorem-alg (Lift-pre pre-lft isRefining) = record { cont = solver } where
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
    solver : (ds : Stream Digit) → SplittingSolution [ pre-lft ] ds
    solver ds = {!!}

  fundamental-theorem : ∀ {m}
                      → refining₁ m
                      → extracting₁ m
  fundamental-theorem = unfold-extracting fundamental-theorem-alg

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
  prefix = prefixTail .UnfoldDefs.SplittingSolution.prefix
  tail = prefix .StreamPrefix.rest
  open UnfoldDefs.SplittingSolution prefixTail
  -- given all the above, we can give a resulting digit stream
  unfold : ExtractionMachine
  ExtractionMachine.nextDigit unfold = splitDigit
  ExtractionMachine.state unfold = leftover
  ExtractionMachine.extractingState unfold = leftoverExtracts
  ExtractionMachine.next unfold = fold-over leftoverExtracts tail

fold-over' : ∀ {m} → refining₁ m → Stream Digit → ExtractionMachine
fold-over' refining = fold-over (fundamental-theorem refining)
