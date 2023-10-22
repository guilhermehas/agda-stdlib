------------------------------------------------------------------------
-- The Agda standard library
--
-- ℤ module n
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Mod where

open import Level using (Level)
open import Function using (id; _$_; _∘_; _∋_; const)
open import Data.Bool using (true; false)
open import Data.Product
open import Data.Nat.Base as ℕ using (ℕ; z≤n; s≤s)
open import Data.Nat.Properties as ℕ
  using (m≤n⇒m≤1+n; 1+n≰n; module ≤-Reasoning)
open import Data.Fin.Base as F hiding (suc; pred; _+_; _-_)
open import Data.Fin.Properties
open import Data.Fin.Patterns
open import Data.Fin.Induction using (<-weakInduction)
open import Data.Fin.Relation.Unary.Top
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; module ≡-Reasoning)
import Algebra.Definitions as ADef
open import Relation.Unary using (Pred)

private variable
  ℓ : Level
  A : Set ℓ
  m n : ℕ
  i : Fin n

open module AD {n} = ADef {A = Fin n} _≡_
open ≡-Reasoning

infixl 6 _+_ _+′_ _-_

suc : Fin n → Fin n
suc i with view i
... | ‵fromℕ = zero
... | ‵inj₁ i = F.suc ⟦ i ⟧

pred : Fin n → Fin n
pred zero = fromℕ _
pred (F.suc i) = inject₁ i

elimination : A → (A → A) → Fin n → A
elimination {n = ℕ.suc n} z f = fold′ _ (const f) z

_+_ : Fin m → Fin n → Fin n
i + j = elimination j suc i

_+′_ : Fin n → Fin n → Fin n
_+′_ = _+_

_-_ : Fin n → Fin n → Fin n
i - j  = i + opposite j

suc-inj≡fsuc : (i : Fin n) → suc (inject₁ i) ≡ F.suc i
suc-inj≡fsuc i rewrite view-inject₁ i = cong F.suc (view-complete (view i))

sucFromℕ≡0 : ∀ n → suc (fromℕ n) ≡ zero
sucFromℕ≡0 n rewrite view-fromℕ n = refl

induction : (P : Pred (Fin (ℕ.suc n)) ℓ)
  → P zero
  → (∀ {i} → P i → P (suc i))
  → ∀ i → P i
induction P P₀ Pᵢ⇒Pᵢ₊₁ = <-weakInduction P P₀ Pᵢ⇒Pᵢ₊₁′
  where

  PInj : ∀ {i} → P (suc (inject₁ i)) → P (F.suc i)
  PInj {i} rewrite suc-inj≡fsuc i = id

  Pᵢ⇒Pᵢ₊₁′ : ∀ i → P (inject₁ i) → P (F.suc i)
  Pᵢ⇒Pᵢ₊₁′ _ Pi = PInj (Pᵢ⇒Pᵢ₊₁ Pi)

pred-fsuc≡inj : (i : Fin n) → pred (F.suc i) ≡ inject₁ i
pred-fsuc≡inj _ = refl

suc-pred≡id : (i : Fin n) → suc (pred i) ≡ i
suc-pred≡id zero = sucFromℕ≡0 _
suc-pred≡id (F.suc i) = suc-inj≡fsuc i

pred-suc≡id : (i : Fin n) → pred (suc i) ≡ i
pred-suc≡id i with view i
... | ‵fromℕ = refl
... | ‵inj₁ p = cong inject₁ (view-complete p)

+-identityˡ : LeftIdentity {ℕ.suc n} zero _+_
+-identityˡ _ = refl

+-fsuc : ∀ (i : Fin m) (j : Fin n) → F.suc i + j ≡ suc (i + j)
+-fsuc {ℕ.suc m} i j = refl

+-fsuc′ : ∀ (i : Fin n) j → F.suc i +′ j ≡ suc (inject₁ i +′ j)
+-fsuc′ {ℕ.suc m} i j = begin
  suc (i + j) ≡⟨ cong suc {!!} ⟩
  -- {!!} ≡⟨ {!!} ⟩
  suc (inject₁ i +′ j) ∎

1+≡suc : (i : Fin $ ℕ.suc n) → suc zero +′ i ≡ suc i
1+≡suc {ℕ.zero} zero = refl
1+≡suc {ℕ.suc ℕ.zero} _ = refl
1+≡suc {ℕ.suc (ℕ.suc _)} = induction _ refl (cong suc)

suc-propagates : (i j : Fin n) → suc (i +′ j) ≡ suc i +′ j
suc-propagates n′@{ℕ.suc n} i j with view i
... | ‵fromℕ = begin
  suc (i + j) ≡⟨ {!!} ⟩
  -- {!!} ≡⟨ {!!} ⟩
  j ≡˘⟨ +-identityˡ j ⟩
  zero {n} + j ∎
... | ‵inj₁ {i = k} i′ = begin
  suc (inject₁ k +′ j) ≡⟨ cong suc {!!} ⟩
  suc (⟦ i′ ⟧ + j) ≡˘⟨ +-fsuc ⟦ i′ ⟧ j ⟩
  Fin.suc ⟦ i′ ⟧ +′ j ∎


-- suc-propagates : (i j : Fin n) → suc (i + j) ≡ suc i + j
-- suc-propagates n′@{ℕ.suc n} i j = induction P P0 (λ {i = i} → Pᵢ⇒Pᵢ₊₁ {i = i}) i
--   where
--   P = λ i → suc (i + j) ≡ suc i + j

--   P0 : P zero
--   P0 = begin
--     suc (zero {n} + j) ≡⟨ cong suc (+-identityˡ _) ⟩
--     suc j             ≡˘⟨ 1+≡suc j ⟩
--     suc (zero {n}) + j ∎

--   Pᵢ⇒Pᵢ₊₁ : ∀ {i : Fin n′} → P i → P (suc i)
--   Pᵢ⇒Pᵢ₊₁ {i = i} Pi = begin
--     suc (suc i + j) ≡˘⟨ cong suc Pi ⟩
--     suc (suc (i + j)) ≡⟨ {!!} ⟩
--     -- {!!} ≡⟨ {!!} ⟩
--     {!!} ≡⟨⟩
--     suc (suc i) + j ∎


+-identityʳ : RightIdentity {ℕ.suc n} zero _+_
+-identityʳ = induction _ refl Pᵢ⇒Pᵢ₊₁
  where
  Pᵢ⇒Pᵢ₊₁ : i + zero ≡ i → suc i + zero ≡ suc i
  Pᵢ⇒Pᵢ₊₁ {i = i} i+0≡i = sym $ begin
    suc i         ≡˘⟨ cong suc i+0≡i ⟩
    suc (i + zero) ≡⟨ suc-propagates i zero ⟩
    suc i + zero ∎



_ℕ+_ : ℕ → Fin n → Fin n
ℕ.zero ℕ+ i = i
ℕ.suc n ℕ+ i = suc (n ℕ+ i)

+ℕ-identityʳ-toℕ : m ℕ.≤ n → toℕ (m ℕ+ zero {n}) ≡ m
+ℕ-identityʳ-toℕ {ℕ.zero} m≤n = refl
+ℕ-identityʳ-toℕ {ℕ.suc m} (s≤s m≤n) = begin
  toℕ (suc (m ℕ+ zero))                  ≡⟨ cong (toℕ ∘ suc) (toℕ-injective toℕm≡fromℕ<) ⟩
  toℕ (suc (inject₁ (fromℕ< (s≤s m≤n)))) ≡⟨ cong toℕ (suc-inj≡fsuc _) ⟩
  ℕ.suc (toℕ (fromℕ< (s≤s m≤n)))         ≡⟨ cong ℕ.suc (toℕ-fromℕ< _) ⟩
  ℕ.suc m ∎
  where

  toℕm≡fromℕ< = begin
    toℕ (m ℕ+ zero)        ≡⟨ +ℕ-identityʳ-toℕ (m≤n⇒m≤1+n m≤n) ⟩
    m                      ≡˘⟨ toℕ-fromℕ< _ ⟩
    toℕ (fromℕ< (s≤s m≤n)) ≡˘⟨ toℕ-inject₁ _ ⟩
    toℕ (inject₁ (fromℕ< (s≤s m≤n))) ∎

+ℕ-identityʳ : (m≤n : m ℕ.≤ n) → m ℕ+ zero ≡ fromℕ< (s≤s m≤n)
+ℕ-identityʳ {m} m≤n = toℕ-injective (begin
  toℕ (m ℕ+ zero) ≡⟨ +ℕ-identityʳ-toℕ m≤n ⟩
  m                 ≡˘⟨ toℕ-fromℕ< _ ⟩
  toℕ (fromℕ< (s≤s m≤n)) ∎)
