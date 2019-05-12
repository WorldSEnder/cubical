{-# OPTIONS --cubical #-}

module Cubical.Data.Reals.LFT.NatHelpers where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat public
open import Cubical.Data.Nat.Order public
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary

infixl 7 _⊓_
infixl 6 _⊔_

_≤?_ : ∀ n m → Dec (n ≤ m)
zero ≤? m = yes (m , +-zero m)
suc n ≤? zero = no ¬-<-zero
suc n ≤? suc m with n ≤? m
...            | yes n≤m = yes (suc-≤-suc n≤m)
...            | no ¬n≤m = no (λ sn≤sm → ¬n≤m (pred-≤-pred sn≤sm))

_⊔_ : ℕ → ℕ → ℕ
zero ⊔ y = y
suc x ⊔ zero = suc x
suc x ⊔ suc y = suc (x ⊔ y)

⊔-select : ∀ n m → (n ⊔ m ≡ n) ⊎ (n ⊔ m ≡ m)
⊔-select zero m = inr refl
⊔-select (suc n) zero = inl refl
⊔-select (suc n) (suc m) with ⊔-select n m
...                      | inl path = inl (cong suc path)
...                      | inr path = inr (cong suc path)

⊔-comm : ∀ n m → n ⊔ m ≡ m ⊔ n
⊔-comm zero zero = refl
⊔-comm zero (suc m) = refl
⊔-comm (suc n) zero = refl
⊔-comm (suc n) (suc m) = cong suc (⊔-comm n m)

left-≤-⊔ : ∀ n m → n ≤ n ⊔ m
left-≤-⊔ zero m = m , +-zero m
left-≤-⊔ (suc n) zero = zero , refl
left-≤-⊔ (suc n) (suc m) = let (d , ndm) = left-≤-⊔ n m in d , +-suc d n ∙ (cong suc ndm)

right-≤-⊔ : ∀ n m → m ≤ n ⊔ m
right-≤-⊔ n m = let (d , mdn) = left-≤-⊔ m n in d , mdn ∙ ⊔-comm m n

_⊓_ : ℕ → ℕ → ℕ
zero ⊓ y = zero
suc x ⊓ zero = zero
suc x ⊓ suc y = suc (x ⊓ y)

⊓-select : ∀ n m → (n ⊓ m ≡ n) ⊎ (n ⊓ m ≡ m)
⊓-select zero m = inl refl
⊓-select (suc n) zero = inr refl
⊓-select (suc n) (suc m) with ⊓-select n m
...                      | inl path = inl (cong suc path)
...                      | inr path = inr (cong suc path)

⊓-comm : ∀ n m → n ⊓ m ≡ m ⊓ n
⊓-comm zero zero = refl
⊓-comm zero (suc m) = refl
⊓-comm (suc n) zero = refl
⊓-comm (suc n) (suc m) = cong suc (⊓-comm n m)

left-≤-⊓ : ∀ n m → n ⊓ m ≤ n
left-≤-⊓ zero m = zero , refl
left-≤-⊓ (suc n) zero = suc n , cong suc (+-zero n)
left-≤-⊓ (suc n) (suc m) = let (d , ndm) = left-≤-⊓ n m in d , +-suc d (n ⊓ m) ∙ cong suc ndm

right-≤-⊓ : ∀ n m → n ⊓ m ≤ m
right-≤-⊓ n m = let (d , mdn) = left-≤-⊓ m n in d , (λ i → d + ⊓-comm n m i) ∙ mdn

*-distribʳ-+ : ∀ m n o → (n + o) * m ≡ n * m + o * m
*-distribʳ-+ m zero    o = refl
*-distribʳ-+ m (suc n) o =
  (suc n + o) * m     ≡⟨ refl ⟩
  m + (n + o) * m     ≡⟨ cong (m +_) (*-distribʳ-+ m n o) ⟩
  m + (n * m + o * m) ≡⟨ +-assoc m (n * m) (o * m) ⟩
  m + n * m + o * m   ≡⟨ refl ⟩
  suc n * m + o * m   ∎

*-assoc : ∀ m n o → m * (n * o) ≡ (m * n) * o
*-assoc zero b c = refl
*-assoc (suc m) n o =
  suc m * (n * o)     ≡⟨ refl ⟩
  n * o + m * (n * o) ≡⟨ cong (n * o +_) (*-assoc m n o) ⟩
  n * o + (m * n) * o ≡⟨ sym (*-distribʳ-+ o n (m * n)) ⟩
  (n + m * n) * o     ≡⟨ refl ⟩
  (suc m * n) * o     ∎
