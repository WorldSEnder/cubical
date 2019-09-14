{-# OPTIONS --cubical #-}

module Cubical.Data.Reals.LFT.IntHelpers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Core.Glue
open import Cubical.Data.Nat
  using (ℕ; zero; suc) public
open import Cubical.Data.Nat
  using ()
  renaming (_+_ to _+ℕ_; _*_ to _*ℕ_) public
open import Cubical.Data.Nat.Order
  using (¬-<-zero)
  renaming (_≤_ to _≤ℕ_)
open import Cubical.Data.Int
open Cubical.Data.Int
  using (Int; sucInt; _+_; _-_; -_; pos0+; +-comm) public
open import Cubical.Relation.Nullary
import Cubical.Data.Reals.LFT.NatHelpers as NatH
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Unit

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x
inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl

pos-distrib : ∀ m n → pos (m +ℕ n) ≡ pos m + pos n
pos-distrib zero n = pos0+ _
pos-distrib (suc m) n =
  sucInt (pos (m +ℕ n))  ≡⟨ cong sucInt (pos-distrib m n) ⟩
  sucInt (pos m + pos n) ≡⟨ sucInt+ (pos m) (pos n) ⟩
  pos (suc m) + pos n    ∎

negsuc-distrib : ∀ m n → negsuc (suc (m +ℕ n)) ≡ negsuc m + negsuc n
negsuc-distrib zero n = +-comm (negsuc n) (negsuc 0)
negsuc-distrib (suc m) n =
  predInt (negsuc (suc m +ℕ n)) ≡⟨ cong predInt (negsuc-distrib m n) ⟩
  predInt (negsuc m + negsuc n) ≡⟨ predInt+ (negsuc m) (negsuc n) ⟩
  negsuc (suc m) + negsuc n     ∎

negsuc-pos-distrib : ∀ m n → negsuc (m +ℕ n) ≡ negsuc m - pos n
negsuc-pos-distrib m zero = cong negsuc (NatH.+-zero m)
negsuc-pos-distrib m (suc n) = cong negsuc (NatH.+-suc m n) ∙ negsuc-distrib m n

0≡n-n : ∀ n → pos 0 ≡ n - n
0≡n-n n = sym (plusMinus n _) ∙ (cong (_- n) (sym (pos0+ n)))

neg-inv : ∀ m → - - m ≡ m
neg-inv (pos zero) = refl
neg-inv (pos (suc n)) = refl
neg-inv (negsuc zero) = refl
neg-inv (negsuc (suc n)) = refl

data Sign : Type₀ where pos neut neg : Sign

inv-sign : Sign → Sign
inv-sign Sign.pos = Sign.neg
inv-sign Sign.neut = Sign.neut
inv-sign Sign.neg = Sign.pos

_*sign_ : Sign → Sign → Sign
Sign.neut *sign Sign.neut = Sign.neut
Sign.neut *sign Sign.pos = Sign.neut
Sign.neut *sign Sign.neg = Sign.neut
Sign.pos *sign Sign.neut = Sign.neut
Sign.neg *sign Sign.neut = Sign.neut
Sign.pos *sign Sign.pos = Sign.pos
Sign.neg *sign Sign.pos = Sign.neg
Sign.pos *sign Sign.neg = Sign.neg
Sign.neg *sign Sign.neg = Sign.pos

sign-pos* : ∀ s → pos *sign s ≡ s
sign-pos* pos = refl
sign-pos* neut = refl
sign-pos* neg = refl
sign-*pos : ∀ s → s *sign pos ≡ s
sign-*pos pos = refl
sign-*pos neut = refl
sign-*pos neg = refl

sign-neut* : ∀ s → neut *sign s ≡ neut
sign-neut* pos = refl
sign-neut* neut = refl
sign-neut* neg = refl
sign-*neut : ∀ s → s *sign neut ≡ neut
sign-*neut pos = refl
sign-*neut neut = refl
sign-*neut neg = refl

sign-neg* : ∀ s → neg *sign s ≡ inv-sign s
sign-neg* pos = refl
sign-neg* neut = refl
sign-neg* neg = refl
sign-*neg : ∀ s → s *sign neg ≡ inv-sign s
sign-*neg pos = refl
sign-*neg neut = refl
sign-*neg neg = refl

inv-sign-involutive : ∀ s → inv-sign (inv-sign s) ≡ s
inv-sign-involutive pos = refl
inv-sign-involutive neut = refl
inv-sign-involutive neg = refl

inv-sign-distribʳ : ∀ s t → s *sign (inv-sign t) ≡ inv-sign (s *sign t)
inv-sign-distribʳ s pos = sign-*neg s ∙ cong inv-sign (sym (sign-*pos s))
inv-sign-distribʳ s neut = sign-*neut s ∙ cong inv-sign (sym (sign-*neut s))
inv-sign-distribʳ s neg = sign-*pos s ∙ sym (inv-sign-involutive s) ∙ cong inv-sign (sym (sign-*neg s))
inv-sign-distribˡ : ∀ s t → (inv-sign s) *sign t ≡ inv-sign (s *sign t)
inv-sign-distribˡ pos t = sign-neg* t ∙ cong inv-sign (sym (sign-pos* t))
inv-sign-distribˡ neut t = sign-neut* t ∙ cong inv-sign (sym (sign-neut* t))
inv-sign-distribˡ neg t = sign-pos* t ∙ sym (inv-sign-involutive t) ∙ cong inv-sign (sym (sign-neg* t))

*sign-comm : ∀ s t → s *sign t ≡ t *sign s
*sign-comm pos s = sign-pos* s ∙ sym (sign-*pos s)
*sign-comm neut s = sign-neut* s ∙ sym (sign-*neut s)
*sign-comm neg s = sign-neg* s ∙ sym (sign-*neg s)

*sign-assoc : ∀ s t u → s *sign (t *sign u) ≡ (s *sign t) *sign u
*sign-assoc s pos u = cong (s *sign_) (sign-pos* u) ∙ sym (cong (_*sign u) (sign-*pos s))
*sign-assoc s neut u = cong (s *sign_) (sign-neut* u) ∙ sign-*neut s ∙ sym (sign-neut* u) ∙ cong (_*sign u) (sym (sign-*neut s))
*sign-assoc s neg u = cong (s *sign_) (sign-neg* u) ∙ inv-sign-distribʳ s u ∙ sym (inv-sign-distribˡ s u) ∙ cong (_*sign u) (sym (sign-*neg s))

mag : Int → ℕ
mag (pos n) = n
mag (negsuc n) = (suc n)

sign : Int → Sign
sign (pos (suc n)) = Sign.pos
sign (pos zero) = Sign.neut
sign (negsuc n) = Sign.neg

_◃_ : Sign → ℕ → Int
Sign.pos ◃ n = pos n
Sign.neut ◃ n = pos zero
Sign.neg ◃ zero = pos zero
Sign.neg ◃ (suc m) = negsuc m

sign-mag-◃ : ∀ n → n ≡ sign n ◃ mag n
sign-mag-◃ (pos zero) = refl
sign-mag-◃ (pos (suc n)) = refl
sign-mag-◃ (negsuc n) = refl

◃-sign-zero : ∀ s → s ◃ 0 ≡ pos 0
◃-sign-zero pos = refl
◃-sign-zero neut = refl
◃-sign-zero neg = refl

◃-distrib-+ : ∀ s a b → s ◃ a + s ◃ b ≡ s ◃ (a +ℕ b)
◃-distrib-+ pos a b = sym (pos-distrib a b)
◃-distrib-+ neut a b = refl
◃-distrib-+ neg zero b = sym (pos0+ _)
◃-distrib-+ neg (suc a) zero = cong negsuc (sym (NatH.+-zero a))
◃-distrib-+ neg (suc a) (suc b) = sym (negsuc-distrib a b) ∙ cong negsuc (sym (NatH.+-suc a b))

neg-sign : ∀ b → sign (- b) ≡ inv-sign (sign b)
neg-sign (pos zero) = refl
neg-sign (pos (suc n)) = refl
neg-sign (negsuc n) = refl

neg-mag : ∀ b → mag (- b) ≡ mag b
neg-mag (pos zero) = refl
neg-mag (pos (suc n)) = refl
neg-mag (negsuc n) = refl

sign-neg-predInt : ∀ n → predInt (Sign.neg ◃ n) ≡ Sign.neg ◃ suc n
sign-neg-predInt zero = refl
sign-neg-predInt (suc n) = refl

inv-sign-neg : ∀ s n → s ◃ n ≡ - (inv-sign s ◃ n)
inv-sign-neg neut n = refl
inv-sign-neg pos zero = refl
inv-sign-neg pos (suc n) = refl
inv-sign-neg neg zero = refl
inv-sign-neg neg (suc n) = refl

neg-inv-sign : ∀ s n → - (s ◃ n) ≡ inv-sign s ◃ n
neg-inv-sign s n =
  - (s ◃ n)                     ≡[ i ]⟨ - (inv-sign-involutive s (~ i) ◃ n) ⟩
  - (inv-sign (inv-sign s) ◃ n) ≡⟨ sym (inv-sign-neg (inv-sign s) n) ⟩
  inv-sign s ◃ n                ∎

inv-sign-mag-◃ : ∀ b → inv-sign (sign b) ◃ mag b ≡ - b
inv-sign-mag-◃ b = sym (neg-inv _) ∙ cong (-_) (sym (inv-sign-neg _ _)∙ sym (sign-mag-◃ _))

∣_∣ : Int → Int
∣ n ∣ = pos (mag n)

infixl 7  _*_
_*_ : Int → Int → Int
n * m = (sign n *sign sign m) ◃ (mag n *ℕ mag m)

sign-*-*sign : ∀ a b → sign (a * b) ≡ sign a *sign sign b
sign-*-*sign (pos zero) (pos zero) = refl
sign-*-*sign (pos zero) (pos (suc m)) = refl
sign-*-*sign (pos (suc n)) (pos zero) = refl
sign-*-*sign (pos (suc n)) (pos (suc m)) = refl
sign-*-*sign (pos zero) (negsuc m) = refl
sign-*-*sign (pos (suc n)) (negsuc m) = refl
sign-*-*sign (negsuc n) (pos zero) = refl
sign-*-*sign (negsuc n) (pos (suc m)) = refl
sign-*-*sign (negsuc n) (negsuc m) = refl

mag-*-*-mag : ∀ a b → mag (a * b) ≡ mag a *ℕ mag b
mag-*-*-mag (pos zero) (pos zero) = refl
mag-*-*-mag (pos zero) (pos (suc m)) = refl
mag-*-*-mag (pos (suc n)) (pos zero) = NatH.0≡m*0 n
mag-*-*-mag (pos (suc n)) (pos (suc m)) = refl
mag-*-*-mag (pos zero) (negsuc m) = refl
mag-*-*-mag (pos (suc n)) (negsuc m) = refl
mag-*-*-mag (negsuc n) (pos zero) = NatH.0≡m*0 n
mag-*-*-mag (negsuc n) (pos (suc m)) = refl
mag-*-*-mag (negsuc n) (negsuc m) = refl

sign-assoc : ∀ a b c → sign (a * (b * c)) ≡ sign ((a * b) * c)
sign-assoc a b c =
  sign (a * (b * c))                 ≡⟨ sign-*-*sign a (b * c) ⟩
  sign a *sign sign (b * c)          ≡[ i ]⟨ sign a *sign sign-*-*sign b c i ⟩
  sign a *sign (sign b *sign sign c) ≡⟨ *sign-assoc _ _ _ ⟩
  (sign a *sign sign b) *sign sign c ≡[ i ]⟨ sign-*-*sign a b (~ i) *sign sign c ⟩
  sign (a * b) *sign sign c          ≡[ i ]⟨ sign-*-*sign (a * b) c (~ i) ⟩
  sign ((a * b) * c) ∎

mag-assoc : ∀ a b c → mag (a * (b * c)) ≡ mag ((a * b) * c)
mag-assoc a b c =
  mag (a * (b * c))         ≡⟨ mag-*-*-mag a (b * c) ⟩
  mag a *ℕ mag (b * c)      ≡[ i ]⟨ mag a *ℕ mag-*-*-mag b c i ⟩
  mag a *ℕ (mag b *ℕ mag c) ≡⟨ NatH.*-assoc (mag a) (mag b) (mag c) ⟩
  (mag a *ℕ mag b) *ℕ mag c ≡[ i ]⟨ mag-*-*-mag a b (~ i) *ℕ mag c ⟩
  mag (a * b) *ℕ mag c      ≡[ i ]⟨ mag-*-*-mag (a * b) c (~ i) ⟩
  mag ((a * b) * c) ∎

*-comm : ∀ a b → a * b ≡ b * a
*-comm a b i = *sign-comm (sign a) (sign b) i ◃ NatH.*-comm (mag a) (mag b) i

*-assoc : ∀ a b c → a * (b * c) ≡ (a * b) * c
*-assoc a b c =
  a * (b * c)                            ≡⟨ sign-mag-◃ _ ⟩
  sign (a * (b * c)) ◃ mag (a * (b * c)) ≡[ i ]⟨ (sign-assoc a b c i) ◃ (mag-assoc a b c i) ⟩
  sign ((a * b) * c) ◃ mag ((a * b) * c) ≡⟨ sym (sign-mag-◃ _) ⟩
  (a * b) * c                            ∎

*-zeroˡ : ∀ n → pos zero * n ≡ pos zero
*-zeroˡ (pos n) = ◃-sign-zero _
*-zeroˡ (negsuc n) = refl

*-zeroʳ : ∀ n → n * pos zero ≡ pos zero
*-zeroʳ (pos n) = cong ((sign (pos n) *sign Sign.neut) ◃_) (sym (NatH.0≡m*0 n)) ∙ ◃-sign-zero _
*-zeroʳ (negsuc n) = refl

*pos1 : ∀ b → b * pos 1 ≡ b
*pos1 z = (λ i → sign-*pos (sign z) i ◃ NatH.*-comm (mag z) 1 i) ∙ cong (sign z ◃_) (NatH.+-zero (mag z)) ∙ sym (sign-mag-◃ z)

pos1* : ∀ z → pos 1 * z ≡ z
pos1* z = (λ i → sign-pos* (sign z) i ◃ NatH.+-zero (mag z) i) ∙ sym (sign-mag-◃ z)

negsuc0* : ∀ b → negsuc zero * b ≡ - b
negsuc0* b =
  (neg *sign sign b) ◃ (mag b +ℕ 0) ≡[ i ]⟨ sign-neg* (sign b) i ◃ (NatH.+-zero (mag b) i) ⟩
  inv-sign (sign b) ◃ mag b         ≡[ i ]⟨ inv-sign-mag-◃ b i ⟩
  - b                               ∎

*negsuc0 : ∀ b → b * negsuc 0 ≡ - b
*negsuc0 b =
  (sign b *sign neg) ◃ (mag b *ℕ 1) ≡[ i ]⟨ sign-*neg (sign b) i ◃ (NatH.*pos1 (mag b) i) ⟩
  inv-sign (sign b) ◃ mag b         ≡[ i ]⟨ inv-sign-mag-◃ b i ⟩
  - b                               ∎

*pos-suc : ∀ n b → (pos n * b) + b ≡ pos (suc n) * b
*pos-suc zero b = cong (_+ b) (◃-sign-zero _) ∙ sym (pos0+ b) ∙ sym (pos1* b)
*pos-suc (suc n) b =
  ((pos *sign sign b) ◃ (mag b +ℕ n *ℕ mag b)) + b ≡[ i ]⟨ sign-pos* (sign b) i ◃ (mag b +ℕ n *ℕ mag b) + sign-mag-◃ b i ⟩
  sign b ◃ (mag b +ℕ n *ℕ mag b) + sign b ◃ mag b  ≡⟨ ◃-distrib-+ (sign b) _ (mag b) ⟩
  sign b ◃ ((mag b +ℕ n *ℕ mag b) +ℕ mag b)        ≡[ i ]⟨ sign-pos* (sign b) (~ i) ◃ NatH.+-comm (mag b +ℕ n *ℕ mag b) (mag b) i ⟩
  (pos *sign sign b) ◃ (mag b +ℕ (mag b +ℕ n *ℕ mag b)) ∎

*negsuc-suc : ∀ n b → negsuc (suc n) * b ≡ negsuc n * b - b
*negsuc-suc n b =
  negsuc (suc n) * b                         ≡[ i ]⟨ sign-neg* (sign b) i ◃ (mag b +ℕ suc n *ℕ mag b) ⟩
  inv-sign (sign b) ◃ (suc (suc n) *ℕ mag b) ≡[ i ]⟨ ◃-distrib-+ (inv-sign (sign b)) (mag b) (suc n *ℕ mag b) (~ i) ⟩
  inv-sign (sign b) ◃ mag b
    + inv-sign (sign b) ◃ (suc n *ℕ mag b)   ≡[ i ]⟨ inv-sign-mag-◃ b i + sign-neg* (sign b) (~ i) ◃ (suc n *ℕ mag b) ⟩
  - b + negsuc n * b                         ≡[ i ]⟨ +-comm (- b) (negsuc n * b) i ⟩
  negsuc n * b - b                           ∎

private
  *-distrib-stepsuc : ∀ k m n → pos (suc k) * (m + n) ≡ pos k * (m + n) + (m + n)
  *-distrib-stepsuc k m n = sym (*pos-suc k (m + n))
  *-distrib-stepnegsuc : ∀ k m n → negsuc (suc k) * (m + n) ≡ negsuc k * (m + n) - (m + n)
  *-distrib-stepnegsuc k m n = *negsuc-suc k (m + n)
  reassoc4 : ∀ m n o p → (m + n) + (o + p) ≡ (m + o) + (n + p)
  reassoc4 m n o p = +-assoc (m + n) o p ∙ cong (_+ p) (sym (+-assoc m n o))
                   ∙ cong (λ t → m + t + p) (+-comm n o)
                   ∙ cong (_+ p) (+-assoc m o n) ∙ sym (+-assoc (m + o) n p)

*-distribˡ-+ : ∀ k m n → k * (m + n) ≡ k * m + k * n
*-distribˡ-+ (pos zero) m n =
  pos 0 * (m + n)       ≡⟨ *-zeroˡ (m + n) ⟩
  pos 0 + pos 0         ≡[ i ]⟨ ◃-sign-zero (neut *sign sign m) (~ i) + ◃-sign-zero (neut *sign sign n) (~ i) ⟩
  pos 0 * m + pos 0 * n ∎
*-distribˡ-+ (pos (suc k)) m n =
  pos (suc k) * (m + n)             ≡⟨ *-distrib-stepsuc k m n ⟩
  pos k * (m + n) + (m + n)         ≡[ i ]⟨ *-distribˡ-+ (pos k) m n i + (m + n) ⟩
  (pos k * m + pos k * n) + (m + n) ≡⟨ reassoc4 (pos k * m) (pos k * n) m n ⟩
  (pos k * m + m) + (pos k * n + n) ≡[ i ]⟨ *pos-suc k m i + *pos-suc k n i ⟩
  pos (suc k) * m + pos (suc k) * n ∎
*-distribˡ-+ (negsuc zero) m n =
  negsuc 0 * (m + n)          ≡⟨ negsuc0* (m + n) ⟩
  - (m + n)                   ≡⟨ neg-distrib-+ m n ⟩
  - m - n                     ≡[ i ]⟨ negsuc0* m (~ i) + negsuc0* n (~ i) ⟩
  negsuc 0 * m + negsuc 0 * n ∎
*-distribˡ-+ (negsuc (suc k)) m n =
  negsuc (suc k) * (m + n)                  ≡⟨ *negsuc-suc k (m + n) ⟩
  negsuc k * (m + n) - (m + n)              ≡[ i ]⟨ *-distribˡ-+ (negsuc k) m n i + neg-distrib-+ m n i ⟩
  (negsuc k * m + negsuc k * n) + (- m - n) ≡⟨ reassoc4 (negsuc k * m) (negsuc k * n) (- m) (- n) ⟩
  (negsuc k * m - m) + (negsuc k * n - n)   ≡[ i ]⟨ *negsuc-suc k m (~ i) + *negsuc-suc k n (~ i) ⟩
  negsuc (suc k) * m + negsuc (suc k) * n   ∎

*-distribʳ-+ : ∀ k m n → (m + n) * k ≡ m * k + n * k
*-distribʳ-+ k m n =
  (m + n) * k   ≡⟨ *-comm (m + n) k ⟩
  k * (m + n)   ≡⟨ *-distribˡ-+ k m n ⟩
  k * m + k * n ≡[ i ]⟨ *-comm k m i + *-comm k n i ⟩
  m * k + n * k ∎

sucInt* : ∀ a b → sucInt a * b ≡ a * b + b
sucInt* a b = *-distribʳ-+ b a (pos 1) ∙ cong (a * b +_) (pos1* b)

*sucInt : ∀ a b → a * sucInt b ≡ a * b + a
*sucInt a b = *-distribˡ-+ a b (pos 1) ∙ cong (a * b +_) (*pos1 a)

predInt* : ∀ a b → predInt a * b ≡ a * b - b
predInt* a b = *-distribʳ-+ b a (negsuc 0) ∙ cong (a * b +_) (negsuc0* b)

*predInt : ∀ a b → a * predInt b ≡ a * b - a
*predInt a b = *-distribˡ-+ a b (negsuc 0) ∙ cong (a * b +_) (*negsuc0 a)

neg-refl : ∀ a → a - a ≡ pos 0
neg-refl a =
  a - a         ≡[ i ]⟨ pos0+ a i - a ⟩
  pos 0 + a - a ≡⟨ plusMinus a (pos 0) ⟩
  pos 0         ∎

*neg : ∀ m n → - (m * n) ≡ m * (- n)
*neg m n =
  - (m * n)                                         ≡⟨ neg-inv-sign _ _ ⟩
  inv-sign (sign m *sign sign n) ◃ (mag m *ℕ mag n) ≡[ i ]⟨ sign-path i ◃ mag-path i ⟩
  m * (- n)                                         ∎ where
  sign-path : inv-sign (sign m *sign sign n) ≡ sign m *sign sign (- n)
  sign-path = sym (sign-*neg _) ∙ sym (*sign-assoc _ _ _) ∙ cong (sign m *sign_) (sign-*neg (sign n) ∙ sym (neg-sign n))
  mag-path : mag m *ℕ mag n ≡ mag m *ℕ mag (- n)
  mag-path i = mag m *ℕ (neg-mag n (~ i))

neg* : ∀ m n → - (m * n) ≡ (- m) * n
neg* m n =
  - (m * n) ≡[ i ]⟨ - *-comm m n i ⟩
  - (n * m) ≡⟨ *neg n m ⟩
  n * (- m) ≡⟨ *-comm n (- m) ⟩
  (- m) * n ∎

*-distrib-assocˡ-+ : ∀ k m o n p → (k * m) * o + (k * n) * p ≡ k * (m * o + n * p)
*-distrib-assocˡ-+ k m o n p =
  (k * m) * o + (k * n) * p ≡[ i ]⟨ *-assoc k m o (~ i) + *-assoc k n p (~ i) ⟩
  k * (m * o) + k * (n * p) ≡⟨ sym (*-distribˡ-+ k (m * o) (n * p)) ⟩
  k * (m * o + n * p)       ∎
*-distrib-assocʳ-+ : ∀ k m o n p → m * (k * o) + n * (k * p) ≡ k * (m * o + n * p)
*-distrib-assocʳ-+ k m o n p =
  m * (k * o) + n * (k * p) ≡[ i ]⟨ m * *-comm k o i + n * *-comm k p i ⟩
  m * (o * k) + n * (p * k) ≡[ i ]⟨ *-assoc m o k i + *-assoc n p k i ⟩
  (m * o) * k + (n * p) * k ≡⟨ sym (*-distribʳ-+ k (m * o) (n * p)) ∙ *-comm _ k ⟩
  k * (m * o + n * p)       ∎

*negneg : ∀ m n → m * n ≡ (- m) * (- n)
*negneg m n =
  m * n         ≡⟨ sym (neg-inv _) ⟩
  - - (m * n)   ≡⟨ cong (-_) (neg* _ _) ⟩
  - ((- m) * n) ≡⟨ *neg _ _ ⟩
  (- m) * (- n) ∎

infix 4 _≤_ _<_

_≤_ : (m : Int) (n : Int) → Type₀
m ≤ n = Σ[ d ∈ ℕ ] m + Int.pos d ≡ n

_<_ : (m : Int) (n : Int) → Type₀
m < n = sucInt m ≤ n

pos-≤-pos : ∀ {m n} → m NatH.≤ n → pos m ≤ pos n
pos-≤-pos (d , mdn) = d , sym (pos-distrib _ d) ∙ cong Int.pos (NatH.+-comm _ d ∙ mdn)

unpos-≤-unpos : ∀ {m n} → pos m ≤ pos n → m NatH.≤ n
unpos-≤-unpos (d , mdn) = d , injPos (cong pos (sym (NatH.+-comm _ d)) ∙ pos-distrib _ d ∙ mdn)

negsuc-≤-negsuc : ∀ {m n} → n NatH.≤ m → negsuc m ≤ negsuc n
negsuc-≤-negsuc {m = m} {n} (d , ndm) = d , reason where
  reason : negsuc m + pos d ≡ negsuc n
  reason = negsuc m + pos d         ≡[ i ]⟨ negsuc (ndm (~ i)) + pos d ⟩
           negsuc (d +ℕ n) + pos d  ≡[ i ]⟨ negsuc (NatH.+-comm d n i) + pos d ⟩
           negsuc (n +ℕ d) + pos d  ≡[ i ]⟨ negsuc-pos-distrib n d i + pos d ⟩
           negsuc n - pos d + pos d ≡⟨ minusPlus (pos d) _ ⟩
           negsuc n                ∎

unnegsuc-≤-unnegsuc : ∀ {m n} → negsuc m ≤ negsuc n → n NatH.≤ m
unnegsuc-≤-unnegsuc {m = m} {n} (d , ndm) = d , injNegsuc reason where
  reason : negsuc (d +ℕ n) ≡ negsuc m
  reason = negsuc (d +ℕ n)          ≡[ i ]⟨ negsuc (NatH.+-comm d n i) ⟩
           negsuc (n +ℕ d)          ≡⟨ negsuc-pos-distrib n d ⟩
           negsuc n - pos d         ≡[ i ]⟨ sym ndm i - pos d ⟩
           negsuc m + pos d - pos d ≡⟨ plusMinus (pos d) _ ⟩
           negsuc m                 ∎

¬pos-≤-negsuc : ∀ m n → ¬ pos m ≤ negsuc n
¬pos-≤-negsuc m n (d , mdn) = posNotnegsuc (m +ℕ d) n (pos-distrib m d ∙ mdn)

negsuc-≤-pos : ∀ m n → negsuc m ≤ pos n
negsuc-≤-pos m n = suc m +ℕ n , reason where
  reason : negsuc m + pos (suc m +ℕ n) ≡ pos n
  reason = negsuc m + pos (suc m +ℕ n)      ≡[ i ]⟨ negsuc m + pos-distrib (suc m) n i ⟩
           negsuc m + (pos (suc m) + pos n) ≡⟨ +-assoc (negsuc m) _ (pos n) ⟩
           negsuc m - negsuc m + pos n      ≡[ i ]⟨ 0≡n-n (negsuc m) (~ i) + pos n ⟩
           pos 0 + pos n                    ≡⟨ sym (pos0+ _) ⟩
           pos n                            ∎

_≤?_ : ∀ m n → Dec (m ≤ n)
pos n ≤? pos m with n NatH.≤? m
...            | yes n≤m = yes (pos-≤-pos n≤m)
...            | no ¬n≤m = no (λ pn≤pm → ¬n≤m (unpos-≤-unpos pn≤pm))
pos n ≤? negsuc m = no (¬pos-≤-negsuc n m)
negsuc n ≤? pos m = yes (negsuc-≤-pos n m)
negsuc n ≤? negsuc m with m NatH.≤? n
...            | yes n≤m = yes (negsuc-≤-negsuc n≤m)
...            | no ¬n≤m = no λ pn≤pm → ¬n≤m (unnegsuc-≤-unnegsuc pn≤pm)

≤-suc : ∀ n → n ≤ sucInt n
≤-suc n = 1 , refl

zero-≤ : ∀ n → pos 0 ≤ pos n
zero-≤ n = n , sym (pos0+ _)

neg-flip-sub : ∀ m n → - (m - n) ≡ n - m
neg-flip-sub m n =
  - (m - n)   ≡⟨ neg-distrib-+ m (- n) ⟩
  - m - (- n) ≡[ i ]⟨ - m + neg-inv n i ⟩
  - m + n     ≡⟨ +-comm (- m) n ⟩
  n - m       ∎

n-m+p≡n : ∀ n m p → (n - m) + p ≡ n → p ≡ m
n-m+p≡n n m p n-m+p-eq =
  p                           ≡⟨ sym (plusMinus (n - m) p) ⟩
  (p + (n - m)) - (n - m)     ≡[ i ]⟨ +-comm (+-comm p (n - m) i) (- (n - m)) i ⟩
  (- (n - m)) + ((n - m) + p) ≡[ i ]⟨ neg-flip-sub n m i + ((n - m) + p) ⟩
  (m - n) + ((n - m) + p)     ≡[ i ]⟨ (m - n) + n-m+p-eq i ⟩
  (m - n) + n                 ≡⟨ minusPlus n m ⟩
  m                           ∎

<-not-refl : ∀ n → ¬ (n < n)
<-not-refl n (d , pth) = posNotnegsuc d 0 (n-m+p≡n n (negsuc 0) (pos d) pth)

<-not-eq : ∀ n m → n < m → ¬ (n ≡ m)
<-not-eq n m n<m n≡m = <-not-refl n (transport (λ i → n < n≡m (~ i)) n<m)

≤-refl : ∀ n → n ≤ n
≤-refl n = 0 , refl

≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans {a = x} {y} {z} (d , xdy) (e , yez) = d +ℕ e ,
  (x + Int.pos (d +ℕ e)       ≡[ i ]⟨ x + pos-distrib d e i ⟩
  x + (Int.pos d + Int.pos e) ≡⟨ +-assoc x (Int.pos d) (Int.pos e) ⟩
  (x + Int.pos d) + Int.pos e ≡[ i ]⟨ xdy i + Int.pos e ⟩
  y + Int.pos e               ≡⟨ yez ⟩
  z ∎)

≤-transport : ∀ {n m o p} → o ≡ n → m ≡ p → n ≤ m → o ≤ p
≤-transport o≡n m≡p (d , ndm) = d , cong (_+ pos d) o≡n ∙ ndm ∙ m≡p

≤-map : ∀ {n m}
      → (f g : Int → Int)
      → (∀ d → n + pos d ≡ m → f n + pos d ≡ g m)
      → n ≤ m → f n ≤ g m
≤-map f g f+d≡g (d , ndm) = d , f+d≡g d ndm

≤-stepsʳ : ∀ n m s → n ≤ m → n + s ≤ m + s
≤-stepsʳ n m s = ≤-map (_+ s) (_+ s) proof where
  proof : ∀ d → n + pos d ≡ m → (n + s) + pos d ≡ (m + s)
  proof d ndm =
    (n + s) + pos d ≡⟨ +-comm (n + s) (pos d) ⟩
    pos d + (n + s) ≡⟨ +-assoc (pos d) n s ⟩
    (pos d + n) + s ≡⟨ cong (_+ s) (+-comm (pos d) n ∙ ndm) ⟩
    m + s           ∎

≤-stepsˡ : ∀ n m s → n ≤ m → s + n ≤ s + m
≤-stepsˡ n m s n≤m = ≤-transport (+-comm s n) (+-comm m s) (≤-stepsʳ n m s n≤m)

≤-unstepsʳ : ∀ n m s → n + s ≤ m + s → n ≤ m
≤-unstepsʳ n m s ns≤ms = ≤-transport (sym (plusMinus s _)) (plusMinus s _) (≤-stepsʳ (n + s) (m + s) (- s) ns≤ms)

≤-unstepsˡ : ∀ n m s → s + n ≤ s + m → n ≤ m
≤-unstepsˡ n m s sn≤sm = ≤-unstepsʳ n m s (≤-transport (+-comm n s) (+-comm s m) sn≤sm)

<-stepsʳ : ∀ n m s → n < m → n + s < m + s
<-stepsʳ n m s n<m = ≤-transport (sucInt+ n s) refl (≤-stepsʳ _ _ s n<m)

<-stepsˡ : ∀ n m s → n < m → s + n < s + m
<-stepsˡ n m s n<m = ≤-transport (+sucInt s n) refl (≤-stepsˡ _ _ s n<m)

neg-op-≤ : ∀ n m → n ≤ m → (- m) ≤ (- n)
neg-op-≤ n m (d , ndm) = d , (
  - m + pos d           ≡[ i ]⟨ - ndm (~ i) + pos d ⟩
  - (n + pos d) + pos d ≡[ i ]⟨ neg-distrib-+ n (pos d) i + pos d ⟩
  (- n - pos d) + pos d ≡⟨ minusPlus (pos d) (- n) ⟩
  - n ∎)

neg-op-≤-inv : ∀ n m → (- m) ≤ (- n) → n ≤ m
neg-op-≤-inv n m m≤n = transport (λ i → neg-inv n i ≤ neg-inv m i) (neg-op-≤ _ _ m≤n)

infixl 7 _⊓_
infixl 6 _⊔_

_⊔_ : Int → Int → Int
pos n ⊔ pos m = pos (n NatH.⊔ m)
pos n ⊔ negsuc m = pos n
negsuc n ⊔ pos m = pos m
negsuc n ⊔ negsuc m = negsuc (n NatH.⊓ m)

⊔-comm : ∀ n m → n ⊔ m ≡ m ⊔ n
⊔-comm (pos n) (pos m) = cong pos (NatH.⊔-comm n m)
⊔-comm (pos n) (negsuc m) = refl
⊔-comm (negsuc n) (pos m) = refl
⊔-comm (negsuc n) (negsuc m) = cong negsuc (NatH.⊓-comm n m)

⊔-selective : ∀ n m → (n ⊔ m ≡ n) ⊎ (n ⊔ m ≡ m)
⊔-selective (pos n) (pos m) with NatH.⊔-select n m
...                         | inl path = inl (cong pos path)
...                         | inr path = inr (cong pos path)
⊔-selective (pos n) (negsuc m) = inl refl
⊔-selective (negsuc n) (pos m) = inr refl
⊔-selective (negsuc n) (negsuc m) with NatH.⊓-select n m
...                               | inl path = inl (cong negsuc path)
...                               | inr path = inr (cong negsuc path)

-- ⊔ is the poset sum
⊔-universal : ∀ n m z → n ≤ z → m ≤ z → n ⊔ m ≤ z
⊔-universal (pos n) (pos m) z (d , ndz) (e , mez) = helper (NatH.⊔-select n m) where
  helper : (n NatH.⊔ m ≡ n) ⊎ (n NatH.⊔ m ≡ m) → (pos n) ⊔ (pos m) ≤ z
  helper (inl path) = d , (λ i → pos (path i) + pos d) ∙ ndz
  helper (inr path) = e , (λ i → pos (path i) + pos e) ∙ mez
⊔-universal (pos n) (negsuc m) z (d , ndz) (e , mez) = d , ndz
⊔-universal (negsuc n) (pos m) z (d , ndz) (e , mez) = e , mez
⊔-universal (negsuc n) (negsuc m) z (d , ndz) (e , mez) = helper (NatH.⊓-select n m) where
  helper : (n NatH.⊓ m ≡ n) ⊎ (n NatH.⊓ m ≡ m) → (negsuc n) ⊔ (negsuc m) ≤ z
  helper (inl path) = d , (λ i → negsuc (path i) + pos d) ∙ ndz
  helper (inr path) = e , (λ i → negsuc (path i) + pos e) ∙ mez

left-≤-⊔ : ∀ n m → n ≤ n ⊔ m
left-≤-⊔ (pos n) (pos m) = pos-≤-pos (NatH.left-≤-⊔ n m)
left-≤-⊔ (pos n) (negsuc m) = ≤-refl _
left-≤-⊔ (negsuc n) (pos m) = m +ℕ (suc n) ,
  (negsuc n + pos (m +ℕ suc n)     ≡⟨ +-comm (negsuc n) _ ⟩
  (pos (m +ℕ suc n) +negsuc n)     ≡[ i ]⟨ pos-distrib m (suc n) i +negsuc n ⟩
  (pos m + pos (suc n)) + negsuc n ≡⟨ minusPlus (negsuc n) (pos m) ⟩
  pos m                            ∎)
left-≤-⊔ (negsuc n) (negsuc m) = negsuc-≤-negsuc (NatH.left-≤-⊓ n m)

right-≤-⊔ : ∀ n m → m ≤ n ⊔ m
right-≤-⊔ n m = let (d , mdn) = left-≤-⊔ m n in d , mdn ∙ ⊔-comm m n

_⊓_ : Int → Int → Int
m ⊓ n = - (- m ⊔ - n)

-- ⊓ is the poset product
⊓-universal : ∀ n m z → z ≤ n → z ≤ m → z ≤ n ⊓ m
⊓-universal n m z z≤n z≤m = neg-op-≤-inv _ _ (transport (λ i → neg-inv (- n ⊔ - m) (~ i) ≤ (- z))
                                                (⊔-universal _ _ _ (neg-op-≤ _ _ z≤n) (neg-op-≤ _ _ z≤m)))
left-≤-⊓ : ∀ n m → n ⊓ m ≤ n
left-≤-⊓ n m = neg-op-≤-inv _ _ (transport (λ i → (- n) ≤ neg-inv ((- n) ⊔ (- m)) (~ i)) (left-≤-⊔ _ _))

right-≤-⊓ : ∀ n m → n ⊓ m ≤ m
right-≤-⊓ n m = neg-op-≤-inv _ _ (transport (λ i → (- m) ≤ neg-inv ((- n) ⊔ (- m)) (~ i)) (right-≤-⊔ _ _))

infix -1 begin≤_ begin<_
infixr 2 _≤≡⟨_⟩_ _≤⟨_⟩_ _<⟨_⟩_
infix  3 _≤∎
data _Is-Related-To_ (x y : Int) : Type₀ where
  strict : x ≤ y → x Is-Related-To y
  non-strict : x < y → x Is-Related-To y

_≤≡⟨_⟩_ : ∀ x {y z} → x ≡ y → y Is-Related-To z → x Is-Related-To z
_ ≤≡⟨ x≡y ⟩ strict y≤z = strict (≤-transport x≡y refl y≤z)
_ ≤≡⟨ x≡y ⟩ non-strict y<z = non-strict (≤-transport (cong sucInt x≡y) refl y<z)

_≤⟨_⟩_ : ∀ x {y z} → (x≤y : x ≤ y) → y Is-Related-To z → x Is-Related-To z
_ ≤⟨ x≤y ⟩ strict y≤z = strict (≤-trans x≤y y≤z)
_ ≤⟨ x≤y ⟩ non-strict y<z = non-strict (≤-trans (≤-stepsʳ _ _ (pos 1) x≤y) y<z)

_<⟨_⟩_ : ∀ x {y z} → (x<y : x < y) → (y<z : y Is-Related-To z) → x Is-Related-To z
_ <⟨ x<y ⟩ strict y≤z = non-strict (≤-trans x<y y≤z)
_ <⟨ x<y ⟩ non-strict y<z = non-strict (≤-trans x<y (≤-trans (≤-suc _) y<z))

_≤∎ : ∀ x → x Is-Related-To x
x ≤∎ = strict (≤-refl x)

private
  isNonStrict : ∀ {x y} → x Is-Related-To y → Type₀
  isNonStrict (strict _) = ⊥
  isNonStrict (non-strict _) = Unit

begin≤_ : ∀ {x y} → (rel : x Is-Related-To y) → x ≤ y
begin≤ strict x~y = x~y
begin≤ non-strict x~y = ≤-trans (≤-suc _) x~y

begin<_ : ∀ {x y} → (rel : x Is-Related-To y) {ns : isNonStrict rel} → x < y
begin< non-strict x = x

mag-positive : ∀ n → Int.pos 0 ≤ ∣ n ∣
mag-positive (pos zero) = 0 , refl
mag-positive (pos (suc n)) = suc n , cong sucInt (sym (pos0+ (pos n)))
mag-positive (negsuc n) = suc n , cong sucInt (sym (pos0+ (pos n)))

max-≡-mag : ∀ n → (- n) ⊔ n ≡ ∣ n ∣
max-≡-mag (pos zero) = refl
max-≡-mag (pos (suc n)) = refl
max-≡-mag (negsuc n) = refl

0<∣x∣⇒¬x≡0 : ∀ z → pos 0 < ∣ z ∣ → ¬ (z ≡ pos 0)
0<∣x∣⇒¬x≡0 z 0<∣z∣ z≡0 = <-not-eq (pos 0) ∣ z ∣ 0<∣z∣ (cong ∣_∣ (sym z≡0))

mag-neg-absorb : ∀ a → ∣ - a ∣ ≡ ∣ a ∣
mag-neg-absorb (pos zero) = refl
mag-neg-absorb (pos (suc n)) = refl
mag-neg-absorb (negsuc n) = refl

mag-lower-bound-neg : ∀ x → - x ≤ ∣ x ∣
mag-lower-bound-neg x = begin≤
  - x       ≤⟨ left-≤-⊔ (- x) x ⟩
  (- x) ⊔ x ≤≡⟨ max-≡-mag x ⟩
  ∣ x ∣     ≤∎

mag-lower-bound : ∀ x → x ≤ ∣ x ∣
mag-lower-bound x = begin≤
  x         ≤≡⟨ sym (neg-inv x) ⟩
  - - x     ≤⟨ mag-lower-bound-neg (- x) ⟩
  ∣ - x ∣  ≤≡⟨ mag-neg-absorb x ⟩
  ∣ x ∣    ≤∎

mag-upper-bound : ∀ x → - ∣ x ∣ ≤ x
mag-upper-bound x = begin≤
  - ∣ x ∣       ≤≡⟨ cong (-_) (sym (max-≡-mag x)) ⟩
  - ((- x) ⊔ x) ≤≡⟨( λ i → - ((- x) ⊔ neg-inv x (~ i)) )⟩
  x ⊓ (- x)     ≤⟨ left-≤-⊓ x (- x) ⟩
  x             ≤∎

mag-upper-bound-neg : ∀ x → - ∣ x ∣ ≤ - x
mag-upper-bound-neg x = begin≤
  - ∣ x ∣   ≤≡⟨ cong (-_) (sym (mag-neg-absorb x)) ⟩
  - ∣ - x ∣ ≤⟨ mag-upper-bound (- x) ⟩
  - x       ≤∎

mag-triangle : (a b : Int) → ∣ a + b ∣ ≤ ∣ a ∣ + ∣ b ∣
mag-triangle a b = ≤-transport (sym (max-≡-mag (a + b))) refl (helper (⊔-selective _ _)) where
  pathinl : - (a + b) ≤ ∣ a ∣ + ∣ b ∣
  pathinl = begin≤
            (- (a + b))    ≤≡⟨ neg-distrib-+ a b ⟩
            - a - b        ≤⟨ ≤-stepsʳ _ _ (- b) (mag-lower-bound-neg a) ⟩
            ∣ a ∣ - b      ≤⟨ ≤-stepsˡ _ _ ∣ a ∣ (mag-lower-bound-neg b) ⟩
            ∣ a ∣ + ∣ b ∣ ≤∎
  pathinr : a + b ≤ ∣ a ∣ + ∣ b ∣
  pathinr = begin≤
            a + b          ≤⟨ ≤-stepsʳ _ _ b (mag-lower-bound a) ⟩
            ∣ a ∣ + b     ≤⟨ ≤-stepsˡ _ _ ∣ a ∣ (mag-lower-bound b) ⟩
            ∣ a ∣ + ∣ b ∣ ≤∎
  helper : (- (a + b) ⊔ (a + b) ≡ - (a + b)) ⊎ (- (a + b) ⊔ (a + b) ≡ a + b)
         → - (a + b) ⊔ (a + b) ≤ ∣ a ∣ + ∣ b ∣
  helper (inl path) = ≤-transport path refl pathinl
  helper (inr path) = ≤-transport path refl pathinr

mag-triangle-inv : (a b : Int) → ∣ a ∣ - ∣ b ∣ ≤ ∣ a + b ∣
mag-triangle-inv a b = ≤-unstepsʳ _ _ ∣ b ∣ (≤-transport (minusPlus ∣ b ∣ ∣ a ∣ ∙ cong ∣_∣ (sym (plusMinus b a)))
                                        (λ i → ∣ a + b ∣ + mag-neg-absorb b i) (mag-triangle (a + b) (- b)))

square-mag≡square : ∀ n → n * n ≡ ∣ n ∣ * ∣ n ∣
square-mag≡square (pos n) = refl
square-mag≡square (negsuc n) =
  negsuc n * negsuc n          ≡⟨ *negneg (negsuc n) (negsuc n) ⟩
  (- negsuc n) * (- negsuc n)  ≡⟨ refl ⟩
  ∣ negsuc n ∣ * ∣ negsuc n ∣ ∎

binomial-formula : ∀ a b → (a - b) * (a + b) ≡ a * a - b * b
binomial-formula a b =
  (a - b) * (a + b)                       ≡⟨ *-distribʳ-+ (a + b) a (- b) ⟩
  a * (a + b) + (- b) * (a + b)           ≡[ i ]⟨ *-distribˡ-+ a a b i + *-distribˡ-+ (- b) a b i ⟩
  (a * a + a * b) + (- b * a + - b * b)   ≡[ i ]⟨ (a * a + *-comm a b i) + (neg* b a (~ i) + neg* b b (~ i)) ⟩
  (a * a + b * a) + (- (b * a) - (b * b)) ≡[ i ]⟨ +-assoc (a * a + b * a) (- (b * a)) (- (b * b)) i ⟩
  (a * a + b * a) - b * a - b * b         ≡[ i ]⟨ +-assoc (a * a) (b * a) (- (b * a)) (~ i) - b * b ⟩
  a * a + (b * a - b * a) - b * b         ≡[ i ]⟨ a * a + 0≡n-n (b * a) (~ i) - b * b ⟩
  a * a - b * b ∎

ab≡0⇒a≡0∨b≡0 : ∀ a b → a * b ≡ pos 0 → (a ≡ pos 0) ⊎ (b ≡ pos 0)
ab≡0⇒a≡0∨b≡0 (pos zero) b _ = inl refl
ab≡0⇒a≡0∨b≡0 (pos (suc n)) (pos zero) _ = inr refl
ab≡0⇒a≡0∨b≡0 (pos (suc n)) (pos (suc m)) ab≡0 = ⊥-elim (NatH.snotz (injPos ab≡0))
ab≡0⇒a≡0∨b≡0 (pos (suc n)) (negsuc m) ab≡0 = ⊥-elim (negsucNotpos _ _ ab≡0)
ab≡0⇒a≡0∨b≡0 (negsuc n) (pos zero) _ = inr refl
ab≡0⇒a≡0∨b≡0 (negsuc n) (pos (suc m)) ab≡0 = ⊥-elim (negsucNotpos _ _ ab≡0)
ab≡0⇒a≡0∨b≡0 (negsuc n) (negsuc m) ab≡0 = ⊥-elim (NatH.snotz (injPos ab≡0))

¬a≡0∧¬b≡0⇒¬ab≡0 : ∀ {a b} → ¬ (a ≡ pos 0) → ¬ (b ≡ pos 0) → ¬ a * b ≡ pos 0
¬a≡0∧¬b≡0⇒¬ab≡0 {a = a} {b} ¬a≡0 ¬b≡0 ab≡0 with ab≡0⇒a≡0∨b≡0 a b ab≡0
...                             | inl a≡0 = ¬a≡0 a≡0
...                             | inr b≡0 = ¬b≡0 b≡0
