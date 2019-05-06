{-# OPTIONS --cubical #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Cubical.Data.Reals.LFT.IntHelpers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Core.Glue
open import Cubical.Data.Nat
  using (ℕ; zero; suc) public
open import Cubical.Data.Nat
  using ()
  renaming (_+_ to _+ℕ_) public
open import Cubical.Data.Nat.Order
  using (¬-<-zero)
open import Cubical.Data.Int
open Cubical.Data.Int
  using (Int; _+_; _-_; -_; pos0+; +-comm) public
open import Cubical.Relation.Nullary

data Signed : Type₀ where
  posSuc : ℕ → Signed
  neut : Signed
  negSuc : ℕ → Signed

Int→Signed : Int → Signed
Int→Signed (pos zero) = neut
Int→Signed (pos (suc n)) = posSuc n
Int→Signed (negsuc n) = negSuc n

Signed→Int : Signed → Int
Signed→Int neut = pos zero
Signed→Int (posSuc n) = pos (suc n)
Signed→Int (negSuc n) = negsuc n

Int≃Signed : Iso Int Signed
Int≃Signed = iso Int→Signed Signed→Int intro→elim elim→intro where
  intro→elim : section Int→Signed Signed→Int
  intro→elim (posSuc x) = refl
  intro→elim neut = refl
  intro→elim (negSuc x) = refl
  elim→intro : retract Int→Signed Signed→Int
  elim→intro (pos zero) = refl
  elim→intro (pos (suc n)) = refl
  elim→intro (negsuc n) = refl

pos-distrib : ∀ m n → pos (m +ℕ n) ≡ pos m + pos n
pos-distrib zero n = pos0+ _
pos-distrib (suc m) n =
  pos (suc m +ℕ n)       ≡⟨ refl ⟩
  sucInt (pos (m +ℕ n))  ≡⟨ cong sucInt (pos-distrib m n) ⟩
  sucInt (pos m + pos n) ≡⟨ sucInt+ (pos m) (pos n) ⟩
  pos (suc m) + pos n    ∎

∣_∣ : Int → Int
∣ pos n ∣ = pos n
∣ negsuc n ∣ = pos (suc n)

unpos : Int → ℕ
unpos (Int.pos n) = n
unpos (Int.negsuc n) = zero

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

*negneg : ∀ m n → m * n ≡ (- m) * (- n)
*negneg m n =
  m * n         ≡⟨ sym (neg-inv _) ⟩
  - - (m * n)   ≡[ i ]⟨ - *neg m n i ⟩
  - (m * (- n)) ≡[ i ]⟨ - *-comm m (- n) i ⟩
  - ((- n) * m) ≡⟨ *neg (- n) m ⟩
  (- n) * (- m) ≡⟨ *-comm (- n) (- m) ⟩
  (- m) * (- n) ∎

infix 4 _≤_ _<_

_≤_ : (m : Int) (n : Int) → Type₀
m ≤ n = Σ[ d ∈ ℕ ] m + Int.pos d ≡ n

_<_ : (m : Int) (n : Int) → Type₀
m < n = sucInt m ≤ n

suc-≤ : ∀ n → n ≤ sucInt n
suc-≤ n = 1 , refl

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

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans {x = x} {y} {z} (d , xdy) (e , yez) = d +ℕ e ,
  (x + Int.pos (d +ℕ e) ≡[ i ]⟨ x + pos-distrib d e i ⟩
   x + (Int.pos d + Int.pos e) ≡⟨ +-assoc x (Int.pos d) (Int.pos e) ⟩
   (x + Int.pos d) + Int.pos e ≡[ i ]⟨ xdy i + Int.pos e ⟩
   y + Int.pos e ≡⟨ yez ⟩
   z ∎)

≤<-trans : ∀ {x y z} → x ≤ y → y < z → x < z
≤<-trans {x = x}{y} (d , xdy) y<z = ≤-trans sx≤sy y<z where
  sx≤sy : sucInt x ≤ sucInt y
  sx≤sy = d , sym (sucInt+ x (pos d)) ∙ cong sucInt xdy

<≤-trans : ∀ {x y z} → x < y → y ≤ z → x < z
<≤-trans x≤y y<z = ≤-trans x≤y y<z

<-trans : ∀ {x y z} → x < y → y < z → x < z
<-trans {y = y} x<y y<z = ≤-trans (≤-trans x<y (suc-≤ y)) y<z

_≤≤⟨_⟩_ : ∀ x {y z} → (x≤y : x ≤ y) → (y≤z : y ≤ z) → x ≤ z
_ ≤≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z

_≤<⟨_⟩_ : ∀ x {y z} → (x≤y : x ≤ y) → (y<z : y < z) → x < z
_ ≤<⟨ x≤y ⟩ y<z = ≤<-trans x≤y y<z

_<≤⟨_⟩_ : ∀ x {y z} → (x<y : x < y) → (y≤z : y ≤ z) → x < z
_ <≤⟨ x<y ⟩ y≤z = <≤-trans x<y y≤z

_<<⟨_⟩_ : ∀ x {y z} → (x<y : x < y) → (y<z : y < z) → x < z
_ <<⟨ x<y ⟩ y<z = <-trans x<y y<z

mag-positive : ∀ n → Int.pos 0 ≤ ∣ n ∣
mag-positive (pos zero) = 0 , refl
mag-positive (pos (suc n)) = suc n , sym (pos0+ _)
mag-positive (negsuc n) = suc n , sym (pos0+ _)

infixl 7 _⊓_ _⊓ℕ_
infixl 6 _⊔_ _⊔ℕ_

_⊔ℕ_ : ℕ → ℕ → ℕ
zero ⊔ℕ y = y
suc x ⊔ℕ zero = suc x
suc x ⊔ℕ suc y = suc (x ⊔ℕ y)

_⊓ℕ_ : ℕ → ℕ → ℕ
zero ⊓ℕ y = zero
suc x ⊓ℕ zero = zero
suc x ⊓ℕ suc y = suc (x ⊓ℕ y)

_⊔_ : Int → Int → Int
pos n ⊔ pos m = pos (n ⊔ℕ m)
pos n ⊔ negsuc m = pos n
negsuc n ⊔ pos m = pos m
negsuc n ⊔ negsuc m = negsuc (n ⊓ℕ m)

⊔-universal : ∀ n m z → n ≤ z → m ≤ z → n ⊔ m ≤ z
⊔-universal n m z n≤z m≤z = {!!}

left-≤-⊔ : ∀ n m → n ≤ n ⊔ m
left-≤-⊔ n m = {!!}

right-≤-⊔ : ∀ n m → n ≤ n ⊔ m
right-≤-⊔ n m = {!!}

_⊓_ : Int → Int → Int
pos n ⊓ pos m = pos (n ⊓ℕ m)
pos n ⊓ negsuc m = negsuc m
negsuc n ⊓ pos m = negsuc n
negsuc n ⊓ negsuc m = negsuc (n ⊔ℕ m)

⊓-universal : ∀ n m z → z ≤ n → z ≤ m → z ≤ n ⊓ m
⊓-universal n m z z≤n z≤m = {!!}

max-≡-mag : ∀ n → (- n) ⊔ n ≡ ∣ n ∣
max-≡-mag (pos zero) = refl
max-≡-mag (pos (suc n)) = refl
max-≡-mag (negsuc n) = refl

0<∣x∣⇒¬x≡0 : ∀ z → pos 0 < ∣ z ∣ → ¬ (pos 0 ≡ z)
0<∣x∣⇒¬x≡0 z 0<∣z∣ 0≡z = <-not-eq (pos 0) ∣ z ∣ 0<∣z∣ (cong ∣_∣ 0≡z)

∣-a∣ : ∀ a → ∣ - a ∣ ≡ ∣ a ∣
∣-a∣ (pos zero) = refl
∣-a∣ (pos (suc n)) = refl
∣-a∣ (negsuc n) = refl

∣-∣-triangle : (a b : Int) → (∣ a ∣ - ∣ b ∣) ≤ ∣ a - b ∣
∣-∣-triangle a b = {!!}

∣+∣-triangle : (a b : Int) → (∣ b ∣ - ∣ a ∣) ≤ ∣ a + b ∣
∣+∣-triangle a b = substition (∣-∣-triangle b (- a)) where
  lemma : b - (- a) ≡ a + b
  lemma = λ i → +-comm b (neg-inv a i) i
  substition : (∣ b ∣ - ∣ - a ∣) ≤ ∣ b - (- a) ∣
             → (∣ b ∣ - ∣ a ∣) ≤ ∣ a + b ∣
  substition = transport λ i → (∣ b ∣ - (∣-a∣ a i)) ≤ ∣ lemma i ∣

square-mag≡square : ∀ n → n * n ≡ ∣ n ∣ * ∣ n ∣
square-mag≡square (pos n) = refl
square-mag≡square (negsuc n) =
  negsuc n * negsuc n          ≡⟨ *negneg (negsuc n) (negsuc n) ⟩
  (- negsuc n) * (- negsuc n)  ≡⟨ refl ⟩
  ∣ negsuc n ∣ * ∣ negsuc n ∣ ∎
