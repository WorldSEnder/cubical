{-# OPTIONS --cubical #-}

module Cubical.Data.Reals.LFT where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Order
  using (_≤_)
open import Cubical.Data.Nat
  using (ℕ; zero; suc)
open import Cubical.Data.Int
  using (Int; _+_; _-_; -_)
open import Cubical.Codata.Stream
  using (Stream)
open import Cubical.HITs.SetQuotients
  using (_/_; [_]; eq/; squash/; elimSetQuotientsProp; elimSetQuotientOp₁; elimSetQuotientOp₂)
open import Cubical.Relation.Nullary
  using (¬_)

module IntHelpers where
  open Cubical.Data.Int

  data Sign : Type₀ where
    pos neut neg : Sign

  sign : Int → Sign
  sign (Int.pos zero) = neut
  sign (Int.pos (suc n)) = pos
  sign (Int.negsuc n) = neg

  ∣_∣ : Int → ℕ
  ∣ Int.pos n ∣ = n
  ∣ Int.negsuc n ∣ = suc n

  *pos : ℕ → Int → Int
  *pos zero _ = Int.pos zero
  *pos (suc n) x = *pos n x + x
  *negsuc : ℕ → Int → Int
  *negsuc zero x = Int.pos 0 - x
  *negsuc (suc n) x = *negsuc n x - x

  infixl 7  _*_
  _*_ : Int → Int → Int
  x * Int.pos n = *pos n x
  x * Int.negsuc n = *negsuc n x

  +-swap : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
  +-swap a b c d =
    a + b + (c + d)   ≡⟨ sym (+-assoc _ _ (c + d)) ⟩
    a + (b + (c + d)) ≡[ i ]⟨ a + +-assoc b c d i ⟩
    a + ((b + c) + d) ≡[ i ]⟨ a + (+-comm b c i + d) ⟩
    a + ((c + b) + d) ≡[ i ]⟨ a + +-assoc c b d (~ i) ⟩
    a + (c + (b + d)) ≡⟨ +-assoc _ _ (b + d) ⟩
    a + c + (b + d)   ∎
  neg-swap : ∀ a b c d → (a - b) + (c - d) ≡ (a + c) - (b + d)
  neg-swap a b c d =
    (a - b) + (c - d)   ≡⟨ +-swap a (- b) c (- d) ⟩
    (a + c) + (- b - d) ≡[ i ]⟨ (a + c) + neg-distrib-+ b d (~ i) ⟩
    (a + c) - (b + d)   ∎

  sucInt3⟶2 : ∀ a b c → a + b + sucInt c ≡ a + sucInt b + c
  sucInt3⟶2 a b c =
    a + b + sucInt c   ≡⟨ sym (+sucInt _ c) ⟩
    sucInt (a + b + c) ≡⟨ sucInt+ _ c ⟩
    sucInt (a + b) + c ≡⟨ cong (_+ c) (+sucInt _ b) ⟩
    a + sucInt b + c   ∎
  predInt3⟶2 : ∀ a b c → a + b + predInt c ≡ a + predInt b + c
  predInt3⟶2 a b c =
    a + b + predInt c   ≡⟨ sym (+predInt _ c) ⟩
    predInt (a + b + c) ≡⟨ predInt+ _ c ⟩
    predInt (a + b) + c ≡⟨ cong (_+ c) (+predInt _ b) ⟩
    a + predInt b + c   ∎
  +-swap3↔2 : ∀ a b c → a + b + c ≡ a + c + b
  +-swap3↔2 a b c =
    a + b + c   ≡⟨ sym (+-assoc a b c) ⟩
    a + (b + c) ≡⟨ cong (a +_) (+-comm b c) ⟩
    a + (c + b) ≡⟨ +-assoc a c b ⟩
    a + c + b   ∎

  sucInt* : ∀ a b → a * b + b ≡ sucInt a * b
  sucInt* a (pos zero) = refl
  sucInt* a (pos (suc n)) =
    a * pos n + a + sucInt (pos n) ≡⟨ sucInt3⟶2 _ a (pos n) ⟩
    a * pos n + sucInt a + pos n   ≡⟨ +-swap3↔2 _ (sucInt a) (pos n) ⟩
    a * pos n + pos n + sucInt a   ≡⟨ cong (_+ sucInt a) (sucInt* a (pos n)) ⟩
    sucInt a * pos n + sucInt a    ≡⟨ refl ⟩
    sucInt a * pos (suc n)         ∎
  sucInt* a (negsuc zero) =
    predInt (pos 0 - a)   ≡⟨ +predInt _ (- a) ⟩
    pos 0 + predInt (- a) ≡[ i ]⟨ pos 0 + neg-suc-pred a (~ i) ⟩
    pos 0 - sucInt a      ∎
  sucInt* a (negsuc (suc n)) =
    a * negsuc n - a + predInt (negsuc n)   ≡⟨ predInt3⟶2 _ (- a) (negsuc n) ⟩
    a * negsuc n + predInt (- a) + negsuc n ≡⟨ +-swap3↔2 _ (predInt (- a)) (negsuc n) ⟩
    a * negsuc n + negsuc n + predInt (- a) ≡⟨ cong (_+ predInt (- a)) (sucInt* a (negsuc n)) ⟩
    sucInt a * negsuc n + predInt (- a)     ≡[ i ]⟨ sucInt a * negsuc n + neg-suc-pred a (~ i) ⟩
    sucInt a * negsuc (suc n)               ∎

  predInt* : ∀ a b → a * b - b ≡ predInt a * b
  predInt* a (pos zero) = refl
  predInt* a (pos (suc n)) =
    a * pos n + a - sucInt (pos n)    ≡[ i ]⟨ a * pos n + a + neg-suc-pred (pos n) i ⟩
    a * pos n + a + predInt (- pos n) ≡⟨ predInt3⟶2 _ a (- pos n) ⟩
    a * pos n + predInt a - pos n     ≡⟨ +-swap3↔2 _ (predInt a) (- pos n) ⟩
    a * pos n - pos n + predInt a     ≡⟨ cong (_+ predInt a) (predInt* a (pos n)) ⟩
    predInt a * pos n + predInt a     ≡⟨ refl ⟩
    predInt a * pos (suc n)           ∎
  predInt* a (negsuc zero) = 
    sucInt (pos 0 - a)   ≡⟨ +sucInt _ (- a) ⟩
    pos 0 + sucInt (- a) ≡[ i ]⟨ pos 0 + neg-pred-suc a (~ i) ⟩
    pos 0 - predInt a    ∎
  predInt* a (negsuc (suc n)) = 
    a * negsuc n - a - predInt (negsuc n)    ≡[ i ]⟨ a * negsuc n - a + neg-pred-suc (negsuc n) i ⟩
    a * negsuc n - a + sucInt (- negsuc n)  ≡⟨ sucInt3⟶2 _ (- a) (- negsuc n) ⟩
    a * negsuc n + sucInt (- a) - negsuc n  ≡⟨ +-swap3↔2 _ (sucInt (- a)) (- negsuc n) ⟩
    a * negsuc n - negsuc n + sucInt (- a) ≡⟨ cong (_+ sucInt (- a)) (predInt* a (negsuc n)) ⟩
    predInt a * negsuc n + sucInt (- a)    ≡[ i ]⟨ predInt a * negsuc n + neg-pred-suc a (~ i) ⟩
    predInt a * negsuc n - predInt a        ≡⟨ refl ⟩
    predInt a * negsuc (suc n)              ∎

  pos0* : ∀ z → pos 0 ≡ pos 0 * z
  pos0* (pos zero) = refl
  pos0* (pos (suc n)) = pos0* (pos n)
  pos0* (negsuc zero) = refl
  pos0* (negsuc (suc n)) = pos0* (negsuc n)
  negsuc0* : ∀ z → pos 0 - z ≡ negsuc 0 * z
  negsuc0* (pos zero) = refl
  negsuc0* (pos (suc n)) =
    pos 0 + (- sucInt (pos n)) ≡[ i ]⟨ pos 0 + neg-suc-pred (pos n) i ⟩
    pos 0 + predInt (- pos n)  ≡⟨ sym (+predInt _ (- pos n)) ⟩
    predInt (pos 0 - pos n)    ≡⟨ cong predInt (negsuc0* (pos n)) ⟩
    predInt (negsuc 0 * pos n) ∎
  negsuc0* (negsuc zero) = refl
  negsuc0* (negsuc (suc n)) =
    pos 0 + (- predInt (negsuc n)) ≡[ i ]⟨ pos 0  + neg-pred-suc (negsuc n) i ⟩
    pos 0 + sucInt (- negsuc n)    ≡⟨ sym (+sucInt _ (- negsuc n)) ⟩
    sucInt (pos 0 - negsuc n)      ≡⟨ cong sucInt (negsuc0* (negsuc n)) ⟩
    sucInt (negsuc 0 * negsuc n)   ∎

  *-ind-base-pos : _
  *-ind-base-pos = record
    { _·_ = _*_ ; f = Int.pos ; fᵢ = λ _ → pos 1 ; _:>_ = _*_ ; _#_ = _+_ ; p = refl }
  *-ind-base-negsuc : _
  *-ind-base-negsuc = record
    { _·_ = _*_ ; f = Int.negsuc ; fᵢ = λ _ → negsuc 0 ; _:>_ = _*_ ; _#_ = _+_ ; p = refl }

  *-comm : ∀ a b → a * b ≡ b * a
  *-comm a (Int.pos b) = ind-comm record
    { ind-base = *-ind-base-pos
    ; g∙ = λ n b → cong (pos n * b +_) (sym (pos0+ b)) ∙ sucInt* (pos n) b
    ; ∙g = λ b n → cong (b * pos n +_) (sym (pos0+ b))
    ; base = pos0*
    } a b
  *-comm a (Int.negsuc b) = ind-comm record
    { ind-base = *-ind-base-negsuc
    ; g∙ = λ n b → cong (negsuc n * b +_) (sym (neg0Minus b)) ∙ predInt* (negsuc n) b
    ; ∙g = λ b n → cong (b * negsuc n +_) (sym (neg0Minus b))
    ; base = negsuc0*
    } a b

  *-distribʳ-+ : ∀ k m n → m * k + n * k ≡ (m + n) * k
  *-distribʳ-+ (Int.pos zero) m n = refl
  *-distribʳ-+ (Int.pos (suc k)) m n =
    m * Int.pos (suc k) + n * Int.pos (suc k) ≡⟨ refl ⟩
    (m * Int.pos k + m) + (n * Int.pos k + n) ≡⟨ +-swap _ m _ n ⟩
    (m * Int.pos k + n * Int.pos k) + (m + n) ≡[ i ]⟨ *-distribʳ-+ (Int.pos k) m n i + (m + n) ⟩
    (m + n) * Int.pos k + (m + n)             ≡⟨ refl ⟩
    (m + n) * Int.pos (suc k)                 ∎
  *-distribʳ-+ (Int.negsuc zero) m n = neg-swap _ m _ n
  *-distribʳ-+ (Int.negsuc (suc k)) m n =
    m * Int.negsuc (suc k) + n * Int.negsuc (suc k) ≡⟨ refl ⟩
    (m * Int.negsuc k - m) + (n * Int.negsuc k - n) ≡⟨ neg-swap _ m _ n ⟩
    (m * Int.negsuc k + n * Int.negsuc k) - (m + n) ≡[ i ]⟨ *-distribʳ-+ (Int.negsuc k) m n i - (m + n) ⟩
    (m + n) * Int.negsuc k - (m + n)                ≡⟨ refl ⟩
    (m + n) * Int.negsuc (suc k)                    ∎
  *-distribˡ-+ : ∀ k m n → k * m + k * n ≡ k * (m + n)
  *-distribˡ-+ k m n =
    k * m + k * n ≡[ i ]⟨ *-comm k m i + *-comm k n i ⟩
    m * k + n * k ≡⟨ *-distribʳ-+ k m n ⟩
    (m + n) * k   ≡⟨ *-comm (m + n) k ⟩
    k * (m + n)   ∎

  neg-inv : ∀ m → - - m ≡ m
  neg-inv (pos zero) = refl
  neg-inv (pos (suc n)) = refl
  neg-inv (negsuc zero) = refl
  neg-inv (negsuc (suc n)) = refl

  neg-refl : ∀ a → a - a ≡ pos 0
  neg-refl a =
    a - a         ≡[ i ]⟨ pos0+ a i - a ⟩
    pos 0 + a - a ≡⟨ plusMinus a (pos 0) ⟩
    pos 0         ∎

  *neg : ∀ m n → - (m * n) ≡ m * (- n)
  *neg m (pos zero) = refl
  *neg m (pos (suc zero)) = neg-distrib-+ _ m
  *neg m (pos (suc (suc n))) =
    - (m * pos (suc n) + m) ≡⟨ neg-distrib-+ _ m ⟩
    - (m * pos (suc n)) - m ≡[ i ]⟨ *neg m (pos (suc n)) i - m ⟩
    m * (- pos (suc n)) - m ≡⟨ refl ⟩
    m * negsuc (suc n)      ∎
  *neg m (negsuc zero) =
    - (pos 0 + (- m)) ≡⟨ neg-distrib-+ _ (- m) ⟩
    pos 0 - (- m)     ≡[ i ]⟨ pos 0 + neg-inv m i ⟩
    pos 0 + m         ∎
  *neg m (negsuc (suc n)) =
    - (m * negsuc n - m)     ≡⟨ neg-distrib-+ _ (- m) ⟩
    - (m * negsuc n) - (- m) ≡[ i ]⟨ *neg m (negsuc n) i + neg-inv m i ⟩
    m * (- negsuc n) + m     ≡⟨ refl ⟩
    m * pos (suc (suc n))    ∎

  *-assoc : ∀ a b c → a * (b * c) ≡ (a * b) * c
  *-assoc a b (pos n) = ind-assoc record
    { ind-base = *-ind-base-pos
    ; q = *-distribˡ-+
    ; z = λ i j _ → sym (*-distribˡ-+ i (pos 0) j)
    ; base = λ _ _ → refl
    } a b n
  *-assoc a b (negsuc n) = ind-assoc record
    { ind-base = *-ind-base-negsuc
    ; q = *-distribˡ-+
    ; z = λ i j _ → cong (i *_) (sym (pos0+ (- j))) ∙ sym (*neg i j) ∙ (pos0+ _)
    ; base = λ i j → sym (pos0+ _) ∙ *neg i j ∙ cong (i *_) (pos0+ (- j))
    } a b n

  *-distrib-assocˡ-+ : ∀ k m o n p → (k * m) * o + (k * n) * p ≡ k * (m * o + n * p)
  *-distrib-assocˡ-+ k m o n p =
    (k * m) * o + (k * n) * p ≡[ i ]⟨ *-assoc k m o (~ i) + *-assoc k n p (~ i) ⟩
    k * (m * o) + k * (n * p) ≡⟨ *-distribˡ-+ k (m * o) (n * p) ⟩
    k * (m * o + n * p)       ∎
  *-distrib-assocʳ-+ : ∀ k m o n p → m * (k * o) + n * (k * p) ≡ k * (m * o + n * p)
  *-distrib-assocʳ-+ k m o n p =
    m * (k * o) + n * (k * p) ≡[ i ]⟨ m * *-comm k o i + n * *-comm k p i ⟩
    m * (o * k) + n * (p * k) ≡[ i ]⟨ *-assoc m o k i + *-assoc n p k i ⟩
    (m * o) * k + (n * p) * k ≡⟨ *-distribʳ-+ k (m * o) (n * p) ∙ *-comm _ k ⟩
    k * (m * o + n * p)       ∎

  pos1* : ∀ z → pos 1 * z ≡ z
  pos1* z = pos 1 * z ≡⟨ *-comm (pos 1) z ⟩ z * pos 1 ≡⟨ sym (pos0+ z) ⟩ z ∎

open IntHelpers

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
  open pre-LFT₁ lft
  data pre-LFT₁-eq : pre-LFT₁ → Type₀ where
    pre-LFT₁-eq-con : ∀ k → ¬ (k ≡ Int.pos 0)
                    → (pre-LFT₁-eq (k *pre-lft-int lft))

  lft-eq-from-path : ∀ k → ¬ (k ≡ Int.pos 0) → ∀ lft₂ → k *pre-lft-int lft ≡ lft₂ → pre-LFT₁-eq lft₂
  lft-eq-from-path k ¬k≡0 _ eq = transport (cong pre-LFT₁-eq eq) (pre-LFT₁-eq-con k ¬k≡0)

  determinant-pre : Int
  determinant-pre = a * d - b * c
  invertible-pre : Type₀
  invertible-pre = ¬ (determinant-pre ≡ Int.pos 0)

  -- a LFT₁ is bounded if the denominator can not be 0 on [-1, 1].
  -- note that this implies monotonicity
  record bounded₁-pre : Type₀ where
    field
      sq-sign-pos : sign (d * d - b * b) ≡ pos

  -- a LFT₁ is refining if L([-1, 1]) ⊆ [-1, 1]
  -- since we can not give this axiomatically, as we will define the interpretation
  -- of L on I₀ only later, we derive this from the fact that L(x) is monotonic iff
  -- it is bounded and L(-1) ∈ [-1, 1] and L(1) ∈ [-1, 1]
  record refining₁-pre : Type₀ where
    field
      bounded : bounded₁-pre
      |L[-1]|≤1 : ∣ c - a ∣ ≤ ∣ d - b ∣
      |L[+1]|≤1 : ∣ c + a ∣ ≤ ∣ d + b ∣

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

invertible₁ = Lifted invertible-pre
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
  open Cubical.Data.Int
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
  open Cubical.Data.Int

_^-1 : LFT₁ → LFT₁
_^-1 = elimSetQuotientOp₁ _^-1-pre-lft path where
  path : (a b : pre-LFT₁) → pre-LFT₁-eq a b → pre-LFT₁-eq (a ^-1-pre-lft) (b ^-1-pre-lft)
  path a _ (pre-LFT₁-eq-con k ¬k≡0) = transport (sym (cong (pre-LFT₁-eq _) (^-1-pre-linear k a))) (pre-LFT₁-eq-con k ¬k≡0)

^-1-pre-inv : ∀ m → invertible-pre m → pre-LFT₁-eq id-pre-lft (m *pre-lft (m ^-1-pre-lft))
^-1-pre-inv m ¬det≡0 = lft-eq-from-path _ (determinant-pre m) ¬det≡0 _ path where
  open pre-LFT₁ m
  eq-a : determinant-pre m * Int.pos 1 ≡ a * d + c * (- b)
  eq-a = sym (Cubical.Data.Int.pos0+ _) ∙ cong (a * d +_) (cong -_ (*-comm b c) ∙ *neg c b)
  eq-b : Int.pos 0 ≡ b * d + d * (- b)
  eq-b = sym (neg-refl (b * d)) ∙ cong (b * d +_) (cong -_ (*-comm b d) ∙ *neg d b)
  eq-c : Int.pos 0 ≡ a * (- c) + c * a
  eq-c = sym (neg-refl (c * a)) ∙ (cong (c * a +_) (cong -_ (*-comm c a) ∙ *neg a c) ∙ Cubical.Data.Int.+-comm (c * a) _)
  eq-d : determinant-pre m * Int.pos 1 ≡ b * (- c) + d * a
  eq-d = sym (Cubical.Data.Int.pos0+ _) ∙ cong (a * d +_) (*neg b c) ∙ Cubical.Data.Int.+-comm (a * d) _ ∙ cong (b * (- c) +_) (*-comm a d) 
  path : (determinant-pre m *pre-lft-int id-pre-lft) ≡ (m *pre-lft (m ^-1-pre-lft))
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
digit-bounded +1 = Lift _ record { sq-sign-pos = refl }
digit-bounded +0 = Lift _ record { sq-sign-pos = refl }
digit-bounded −1 = Lift _ record { sq-sign-pos = refl }

data DigitList : ℕ → Type₀ where
  [] : DigitList 0
  _∷_ : ∀ {n} → Digit → DigitList n → DigitList (suc n)

sift : ∀ {n} → DigitList n → LFT₁ → LFT₁
sift [] lft = lft
sift (d ∷ ds) lft = sift ds (lft *lft digit2lft d)

open import Cubical.Data.Prod
record extracting₁ (m : LFT₁) : Type₀
record splitting₁ (m : LFT₁) : Type₀ where
  inductive
  field
    splitDigit : Digit
    leftover : LFT₁
    isSplit : m ≡ digit2lft splitDigit *lft leftover
    leftoverExtracts : extracting₁ leftover

record extracting₁ m where
  coinductive
  field
    n : ℕ
    cont : (ds : DigitList n)
         → splitting₁ (sift ds m)

fundamental-theorem : ∀ {m}
                    → refining₁ m
                    → extracting₁ m
fundamental-theorem (Lift pre-lft isRefining) = record
  { n = bound
  ; cont = cont } where
  bound : ℕ
  bound = {!!}
  cont : (ds : DigitList bound) → splitting₁ (sift ds [ pre-lft ])
  cont ds = record
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

private
  split-stream : (n : ℕ) → Stream Digit → DigitList n × Stream Digit
  split-stream zero ds = [] , ds
  split-stream (suc n) ds = (Stream.head ds ∷ head) , tail where
    inductive-split = split-stream n (Stream.tail ds)
    head = proj₁ inductive-split
    tail = proj₂ inductive-split

fold-over : ∀ {m} → extracting₁ m → Stream Digit → ExtractionMachine
fold-over {m = m} fundamental stream = unfold where
  open extracting₁ fundamental
  temp1 = split-stream n stream
  heads = proj₁ temp1
  tail = proj₂ temp1
  split = cont heads
  open splitting₁ split
  -- given all the above, we can give a resulting digit stream
  unfold : ExtractionMachine
  ExtractionMachine.nextDigit unfold = splitDigit
  ExtractionMachine.state unfold = leftover
  ExtractionMachine.extractingState unfold = leftoverExtracts
  ExtractionMachine.next unfold = fold-over leftoverExtracts tail

fold-over' : ∀ {m} → refining₁ m → Stream Digit → ExtractionMachine
fold-over' refining = fold-over (fundamental-theorem refining)
