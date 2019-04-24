{-# OPTIONS --cubical --safe #-}

{-

This file defines

sucPred : ∀ (i : Int) → sucInt (predInt i) ≡ i
predSuc : ∀ (i : Int) → predInt (sucInt i) ≡ i

discreteInt : discrete Int
isSetInt : isSet Int

addition of Int is defined _+_ : Int → Int → Int

as well as its commutativity and associativity
+-comm : ∀ (m n : Int) → m + n ≡ n + m
+-assoc : ∀ (m n o : Int) → m + (n + o) ≡ (m + n) + o

An alternate definition of _+_ is defined via ua,
namely _+'_, which helps us to easily prove

isEquivAddInt : (m : Int) → isEquiv (λ n → n + m)

-}

module Cubical.Data.Int.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty
open import Cubical.Data.Nat hiding (_+_ ; +-assoc ; +-comm)
open import Cubical.Data.Sum
open import Cubical.Data.Int.Base

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

sucPred : ∀ i → sucInt (predInt i) ≡ i
sucPred (pos zero)       = refl
sucPred (pos (suc n))    = refl
sucPred (negsuc zero)    = refl
sucPred (negsuc (suc n)) = refl

predSuc : ∀ i → predInt (sucInt i) ≡ i
predSuc (pos zero)       = refl
predSuc (pos (suc n))    = refl
predSuc (negsuc zero)    = refl
predSuc (negsuc (suc n)) = refl

-- TODO: define multiplication

injPos : ∀ {a b : ℕ} → pos a ≡ pos b → a ≡ b
injPos {a} h = subst T h refl
  where
  T : Int → Type₀
  T (pos x)    = a ≡ x
  T (negsuc _) = ⊥

injNegsuc : ∀ {a b : ℕ} → negsuc a ≡ negsuc b → a ≡ b
injNegsuc {a} h = subst T h refl
  where
  T : Int → Type₀
  T (pos _) = ⊥
  T (negsuc x) = a ≡ x

posNotnegsuc : ∀ (a b : ℕ) → ¬ (pos a ≡ negsuc b)
posNotnegsuc a b h = subst T h 0
  where
  T : Int → Type₀
  T (pos _)    = ℕ
  T (negsuc _) = ⊥

negsucNotpos : ∀ (a b : ℕ) → ¬ (negsuc a ≡ pos b)
negsucNotpos a b h = subst T h 0
  where
  T : Int → Type₀
  T (pos _)    = ⊥
  T (negsuc _) = ℕ

discreteInt : Discrete Int
discreteInt (pos n) (pos m) with discreteℕ n m
... | yes p = yes (cong pos p)
... | no p  = no (λ x → p (injPos x))
discreteInt (pos n) (negsuc m) = no (posNotnegsuc n m)
discreteInt (negsuc n) (pos m) = no (negsucNotpos n m)
discreteInt (negsuc n) (negsuc m) with discreteℕ n m
... | yes p = yes (cong negsuc p)
... | no p  = no (λ x → p (injNegsuc x))

isSetInt : isSet Int
isSetInt = Discrete→isSet discreteInt

_+pos_ : Int → ℕ  → Int
z +pos 0 = z
z +pos (suc n) = sucInt (z +pos n)

_+negsuc_ : Int → ℕ → Int
z +negsuc 0 = predInt z
z +negsuc (suc n) = predInt (z +negsuc n)

infixl 6 _+_ _-_

_+_ : Int → Int → Int
m + pos n = m +pos n
m + negsuc n = m +negsuc n

-_ : Int → Int
- pos zero = pos zero
- pos (suc n) = negsuc n
- negsuc n = pos (suc n)

_-_ : Int → Int → Int
m - n = m + (- n)

sucInt+pos : ∀ n m → sucInt (m +pos n) ≡ (sucInt m) +pos n
sucInt+pos zero m = refl
sucInt+pos (suc n) m = cong sucInt (sucInt+pos n m)

predInt+negsuc : ∀ n m → predInt (m +negsuc n) ≡ (predInt m) +negsuc n
predInt+negsuc zero m = refl
predInt+negsuc (suc n) m = cong predInt (predInt+negsuc n m)

sucInt+negsuc : ∀ n m → sucInt (m +negsuc n) ≡ (sucInt m) +negsuc n
sucInt+negsuc zero m = (sucPred _) ∙ (sym (predSuc _))
sucInt+negsuc (suc n) m =      _ ≡⟨ sucPred _ ⟩
  m +negsuc n                    ≡[ i ]⟨ predSuc m (~ i) +negsuc n ⟩
  (predInt (sucInt m)) +negsuc n ≡⟨ sym (predInt+negsuc n (sucInt m)) ⟩
  predInt (sucInt m +negsuc n) ∎

predInt+pos : ∀ n m → predInt (m +pos n) ≡ (predInt m) +pos n
predInt+pos zero m = refl
predInt+pos (suc n) m =     _ ≡⟨ predSuc _ ⟩
  m +pos n                    ≡[ i ]⟨ sucPred m (~ i) + pos n ⟩
  (sucInt (predInt m)) +pos n ≡⟨ sym (sucInt+pos n (predInt m))⟩
  (predInt m) +pos (suc n)    ∎

predInt+ : ∀ m n → predInt (m + n) ≡ (predInt m) + n
predInt+ m (pos n) = predInt+pos n m
predInt+ m (negsuc n) = predInt+negsuc n m

+predInt : ∀ m n → predInt (m + n) ≡ m + (predInt n)
+predInt m (pos zero) = refl
+predInt m (pos (suc n)) = (predSuc (m + pos n)) ∙ (cong (_+_ m) (sym (predSuc (pos n))))
+predInt m (negsuc n) = refl

sucInt+ : ∀ m n → sucInt (m + n) ≡ (sucInt m) + n
sucInt+ m (pos n) = sucInt+pos n m
sucInt+ m (negsuc n) = sucInt+negsuc n m

+sucInt : ∀ m n → sucInt (m + n) ≡  m + (sucInt n)
+sucInt m (pos n) = refl
+sucInt m (negsuc zero) = sucPred _
+sucInt m (negsuc (suc n)) = (sucPred (m +negsuc n)) ∙ (cong (_+_ m) (sym (sucPred (negsuc n))))

pos0+ : ∀ z → z ≡ pos 0 + z
pos0+ (pos zero) = refl
pos0+ (pos (suc n)) = cong sucInt (pos0+ (pos n))
pos0+ (negsuc zero) = refl
pos0+ (negsuc (suc n)) = cong predInt (pos0+ (negsuc n))

negsuc0+ : ∀ z → predInt z ≡ negsuc 0 + z
negsuc0+ (pos zero) = refl
negsuc0+ (pos (suc n)) = (sym (sucPred (pos n))) ∙ (cong sucInt (negsuc0+ _))
negsuc0+ (negsuc zero) = refl
negsuc0+ (negsuc (suc n)) = cong predInt (negsuc0+ (negsuc n))

private
  record IndStructure : Type₁
  record IndAssocStructure : Type₁
  record IndCommStructure : Type₁

record IndStructure where
  infix 15 _·_
  infixr 14 _:>_
  infix 13 _#_
  field
    {A Ix} : Type₀
    _·_ : A → A → A
    f : ℕ → A
    fᵢ : ℕ → Ix
    _:>_ : A → Ix → Ix
    _#_ : A → Ix → A
    p : ∀ {n} → f (suc n) ≡ f n # fᵢ n

record IndCommStructure where
  field
    ind-base : IndStructure
  open IndStructure ind-base public
  field
    g∙ : ∀ n b → (f n · b) # (b :> fᵢ n) ≡ (f n # fᵢ n) · b
    ∙g : ∀ a n → (a · f n) # (a :> fᵢ n) ≡ a · (f n # fᵢ n)
    base : ∀ z → z · f 0 ≡ f 0 · z

  ind-comm : ∀ z n → z · f n ≡ f n · z
  ind-comm z 0 = base z
  ind-comm z (suc n) =
    z · f (suc n)         ≡[ i ]⟨ z · p {n} i ⟩
    z · (f n # ix)        ≡⟨ sym (∙g z n) ⟩
    (z · f n) # (z :> ix) ≡⟨ cong (_# (z :> ix)) IH ⟩
    (f n · z) # (z :> ix) ≡⟨ g∙ n z ⟩
    (f n # ix) · z        ≡[ i ]⟨ p {n} (~ i) · z ⟩
    f (suc n) · z         ∎
    where
    ix = fᵢ n
    IH = ind-comm z n
open IndCommStructure using (ind-comm) public

record IndAssocStructure where
  field
    ind-base : IndStructure
  open IndStructure ind-base public
  field
    q : ∀ a b i → a · b # a :> i ≡ a · (b # i)
    z : ∀ i j n → i :> j :> fᵢ n ≡ i · j :> fᵢ n
    base : ∀ m n → (m · n) · f 0 ≡ m · (n · f 0)

  ind-assoc : ∀ m n o → m · (n · f o) ≡ (m · n) · f o
  ind-assoc m n 0 = sym (base m n)
  ind-assoc m n (suc o) =
    m · (n · f (suc o))          ≡[ i ]⟨ m · (n · p {o} i) ⟩
    m · (n · (f o # ix))         ≡[ i ]⟨ m · (q n (f o) ix (~ i)) ⟩
    m · (n · f o # n :> ix)      ≡⟨ sym (q m (n · f o) _) ⟩
    m · (n · f o) # m :> n :> ix ≡⟨ cong ((m · (n · f o)) #_) (z m n o) ⟩
    m · (n · f o) # m · n :> ix  ≡⟨ cong (_# ((m · n) :> ix)) IH ⟩
    (m · n) · f o # m · n :> ix  ≡⟨ q (m · n) (f o) _ ⟩
    (m · n) · (f o # ix)         ≡[ i ]⟨ (m · n) · p {o} (~ i) ⟩
    (m · n) · (f (suc o))        ∎
    where
    ix = fᵢ o
    IH = ind-assoc m n o
open IndAssocStructure using (ind-assoc) public

private
  record Unit : Set where constructor tt
  +-ind-base-pos : IndStructure
  +-ind-base-pos = record
    { _·_ = _+_ ; f = pos ; fᵢ = λ _ → tt ; _:>_ = λ _ i → i
    ; _#_ = λ n _ → sucInt n ; p = refl }
  +-ind-base-negsuc : IndStructure
  +-ind-base-negsuc = record
    { _·_ = _+_ ; f = negsuc ; fᵢ = λ _ → tt ; _:>_ = λ _ i → i
    ; _#_ = λ n _ → predInt n ; p = refl }

+-comm : ∀ m n → m + n ≡ n + m
+-comm m (pos n) = ind-comm record { ind-base = +-ind-base-pos
                                   ; g∙ = λ n b → sucInt+ (pos n) b
                                   ; ∙g = λ a n → +sucInt a (pos n)
                                   ; base = pos0+ } m n
+-comm m (negsuc n) = ind-comm record { ind-base = +-ind-base-negsuc
                                      ; g∙ = λ n b → predInt+ (negsuc n) b
                                      ; ∙g = λ a n → +predInt a (negsuc n)
                                      ; base = negsuc0+ } m n

+-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
+-assoc m n (pos o) = ind-assoc record { ind-base = +-ind-base-pos
                                       ; q = λ a b _ → +sucInt a b
                                       ; z = λ _ _ _ → refl
                                       ; base = λ _ _ → refl } m n o
+-assoc m n (negsuc o) = ind-assoc record { ind-base = +-ind-base-negsuc
                                          ; q = λ a b _ → +predInt a b
                                          ; z = λ _ _ _ → refl
                                          ; base = +predInt } m n o

-- Compose sucPathInt with itself n times. Transporting along this
-- will be addition, transporting with it backwards will be subtraction.
-- Use this to define _+'_ for which is easier to prove
-- isEquiv (λ n → n +' m) since _+'_ is defined by transport

sucPathInt : Int ≡ Int
sucPathInt = ua (sucInt , isoToIsEquiv (iso sucInt predInt sucPred predSuc))

addEq : ℕ → Int ≡ Int
addEq zero = refl
addEq (suc n) = (addEq n) ∙ sucPathInt

predPathInt : Int ≡ Int
predPathInt = ua (predInt , isoToIsEquiv (iso predInt sucInt predSuc sucPred))

subEq : ℕ → Int ≡ Int
subEq zero = refl
subEq (suc n) = (subEq n) ∙ predPathInt

_+'_ : Int → Int → Int
m +' pos n    = transport (addEq n) m
m +' negsuc n = transport (subEq (suc n)) m

+'≡+ : _+'_ ≡ _+_
+'≡+ i m (pos zero) = m
+'≡+ i m (pos (suc n)) = sucInt (+'≡+ i m (pos n))
+'≡+ i m (negsuc zero) = predInt m
+'≡+ i m (negsuc (suc n)) = predInt (+'≡+ i m (negsuc n)) --
  -- compPath (λ i → (+'≡+ i (predInt m) (negsuc n))) (sym (predInt+negsuc n m)) i

isEquivAddInt' : (m : Int) → isEquiv (λ n → n +' m)
isEquivAddInt' (pos n)    = isEquivTransport (addEq n)
isEquivAddInt' (negsuc n) = isEquivTransport (subEq (suc n))

isEquivAddInt : (m : Int) → isEquiv (λ n → n + m)
isEquivAddInt = subst (λ add → (m : Int) → isEquiv (λ n → add n m)) +'≡+ isEquivAddInt'

-- below is an alternate proof of isEquivAddInt for comparison
-- We also have two useful lemma here.

minusPlus : ∀ m n → (n - m) + m ≡ n
minusPlus (pos zero) n = refl
minusPlus (pos 1) = sucPred
minusPlus (pos (suc (suc m))) n =
  sucInt ((n +negsuc (suc m)) +pos (suc m)) ≡⟨ sucInt+pos (suc m) _ ⟩
  sucInt (n +negsuc (suc m)) +pos (suc m)   ≡[ i ]⟨ sucPred (n +negsuc m) i +pos (suc m) ⟩
  (n - pos (suc m)) +pos (suc m)            ≡⟨ minusPlus (pos (suc m)) n ⟩
  n ∎
minusPlus (negsuc zero) = predSuc
minusPlus (negsuc (suc m)) n =
  predInt (sucInt (sucInt (n +pos m)) +negsuc m) ≡⟨ predInt+negsuc m _ ⟩
  predInt (sucInt (sucInt (n +pos m))) +negsuc m ≡[ i ]⟨ predSuc (sucInt (n +pos m)) i +negsuc m ⟩
  sucInt (n +pos m) +negsuc m                    ≡⟨ minusPlus (negsuc m) n ⟩
  n ∎

plusMinus : ∀ m n → (n + m) - m ≡ n
plusMinus (pos zero) n = refl
plusMinus (pos (suc m)) = minusPlus (negsuc m)
plusMinus (negsuc m) = minusPlus (pos (suc m))

private
  alternateProof : (m : Int) → isEquiv (λ n → n + m)
  alternateProof m = isoToIsEquiv (iso (λ n → n + m)
                                       (λ n → n - m)
                                       (minusPlus m)
                                       (plusMinus m))

minusPlusNeg : ∀ m n → m - n ≡ m + (- n)
minusPlusNeg m n = refl

neg0Minus : ∀ n → (- n) ≡ pos 0 - n
neg0Minus (pos zero) = refl
neg0Minus (pos (suc n)) = pos0+ _
neg0Minus (negsuc n) =
  pos (suc n)            ≡⟨ pos0+ _ ⟩
  pos 0 + sucInt (pos n) ≡⟨ sym (+sucInt (pos 0) (pos n)) ⟩
  sucInt (pos 0 + pos n) ∎

neg-suc-pred : ∀ n → - (sucInt n) ≡ predInt (- n)
neg-suc-pred (pos 0) = refl
neg-suc-pred (pos (suc n)) = refl
neg-suc-pred (negsuc zero) = refl
neg-suc-pred (negsuc (suc n)) = refl

neg-pred-suc : ∀ n → - (predInt n) ≡ sucInt (- n)
neg-pred-suc n =
  - (predInt n)                   ≡⟨ sym (sucPred _) ⟩
  sucInt (predInt (- predInt n))  ≡⟨ cong sucInt (sym (neg-suc-pred _)) ⟩
  sucInt (- (sucInt (predInt n))) ≡[ i ]⟨ sucInt (- sucPred n i) ⟩
  sucInt (- n)                    ∎

neg-distrib-+ : ∀ m n → - (m + n) ≡ - m - n
neg-distrib-+ m (pos zero) = refl
neg-distrib-+ m (pos (suc n)) =
  - (sucInt (m + pos n))  ≡⟨ neg-suc-pred _ ⟩
  predInt (- (m + pos n)) ≡⟨ cong predInt (neg-distrib-+ m (pos n)) ⟩
  predInt (- m - pos n)   ≡⟨ +predInt (- m) (- pos n) ⟩
  - m + predInt (- pos n) ≡[ i ]⟨ - m + neg-suc-pred (pos n) (~ i) ⟩
  - m - pos (suc n)       ∎
neg-distrib-+ m (negsuc zero) = neg-pred-suc _
neg-distrib-+ m (negsuc (suc n)) =
  - predInt (m + negsuc n)  ≡⟨ neg-pred-suc _ ⟩
  sucInt (- (m + negsuc n)) ≡⟨ cong sucInt (neg-distrib-+ m (negsuc n)) ⟩
  sucInt (- m - negsuc n)   ≡⟨ +sucInt (- m) (- negsuc n) ⟩
  - m + sucInt (- negsuc n) ≡[ i ]⟨ - m + neg-pred-suc (negsuc n) (~ i) ⟩
  - m - negsuc (suc n)      ∎
