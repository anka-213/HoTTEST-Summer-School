-- {-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}
{-# OPTIONS --rewriting --without-K --allow-unsolved-metas --postfix-projections #-}

open import new-prelude

open import Lecture6-notes
open import Lecture5-notes
open import Lecture4-notes
open import HoTT-WS9 hiding (is-emb ; _∔_)
open import HoTT-WS10 hiding (_↔_ ; is-decidable)
open import RandomLemmas
open import AlternativeEquivalence
open import StuffFromBook

module UnivalenceLecture where

private
  variable
    ℓ l1 l2 l3 : Level
    A B C D P Q : Type ℓ
    AA BB : Type ℓ

data _∔_ (A B : Type ℓ) : Type ℓ where
 inl+ : A → A ∔ B
 inr+ : B → A ∔ B

infixr 1 _∔_

module _ {l1 l2 : Level} {A : Type l1} {B : Type l2} where
  is-emb :  (f : A → B) → Type (l1 ⊔ l2)
  is-emb f = ∀ x y → is-equiv (ap f {x = x} {y = y})

equiv-eq : (A ≡ B) → (A ≃ B)
equiv-eq (refl _) = idEquiv

module _ {ℓ} where
  Univalence : Type (lsuc ℓ)
  Univalence = ∀ (A B : Type ℓ) → is-equiv (equiv-eq {A = A} {B})
  UnivalenceAlt : Type (lsuc ℓ)
  UnivalenceAlt = ∀ (A B : Type ℓ) → (A ≡ B) ≃ (A ≃ B)

module _ {ℓ} {A : Type ℓ} {UA : UnivalenceAlt {ℓ}} where
  alt-to-ua-lem : is-contr (Σ B ꞉ Type ℓ , A ≃ B)
  alt-to-ua-lem = fund-theorem-id-types-i-to-ii A (λ B → fwd (UA A B)) λ B → _≃_.is-equivalence (UA A B)
  -- alt-to-ua-lem {A = A} = {!fund-theorem-id-types-i-to-ii {B = A ≃_}!}

-- prop ext
-- Prop U := Σ x ꞉ U , is-prop x
Propp : (ℓ : Level) → Type (lsuc ℓ)
Propp ℓ = Σ X ꞉ Type ℓ , is-prop X
-- is an embedding

-- is-emb

-- P ≃ Q
-- ≃
-- pr₁ P

-- " = (P ↔ Q)"

-- iff-eq : (P ≡ Q) → (P ↔ Q)
-- is an equivalence

_↔_ : Type l1 → Type l2 → Type (l1 ⊔ l2)
A ↔ B = (A → B) × (B → A)

-- Cor
-- Consider P, Q : A → Prop
-- Then (P ≡ Q) ≃ ((a : A) → P a ↔ Q a)
module _ (P Q : A → Propp ℓ) where
  thrm : (P ≡ Q) ≃ ((a : A) → pr₁ (P a) ↔ pr₁ (Q a))
  thrm = {!!}

module _ {A : Type} where
  thing : (A → Propp ℓ) ≃ (Σ X ꞉ Type ℓ , (X → A))
  thing = mkEquiv
    (λ B → (Σ x ꞉ A , pr₁ (B x)) , pr₁)
    (λ X f → {!fib ? f!} , {!!})
    {!!}
    {!!}

-- Lemma
-- Σ Y ꞉ Type ℓ , Σ g ꞉ (Y → A) , Σ e ꞉ (X ≃ Y) , ((f ∼ g) ∘ e)
-- Swap
-- ...
-- ≃
-- Σ (G : X → A) f ∼ g
-- ≃ Unit

-- Commuting triangle
-- X -≃-> Σ (a : A) fib f a
-- |       /
-- f      /
-- ∨    L
-- A

-- ...

-- QED


-- Proof that LEM is inconsistent with ua for non-prop

-- BS : {ℓ : Level} → ℕ → Type ?
-- BS {ℓ} n = Σ X ꞉ Type ℓ , ∥ Fin n ≃ X ∥₋₁
BS : ℕ → Type₁
BS n = Σ X ꞉ Type , ∥ Fin n ≃ X ∥₋₁

variable
  n : ℕ

getBS : ∀ n → BS n → Type
getBS n = pr₁

BSn-of : (n : ℕ) → Type → Type
BSn-of n tp = {!!}

-- pr₁ on BS is embedding
getBS-is-emb : is-emb (getBS n)
getBS-is-emb = {!!}

pointed-thing : ℕ → Type₁
pointed-thing n = Σ X ꞉ BS n , getBS n X
-- pointed-thing n = Σ getBS n

pt-contr : is-contr (pointed-thing n)
pt-contr = {!!}

postulate
  ∥_∥'₋₁ : Type ℓ → Type ℓ
  ∣_∣' : {A : Type ℓ} → A → ∥ A ∥'₋₁
  trunc' : {A : Type ℓ} → is-prop ∥ A ∥'₋₁

trunc-map' : (A Q : Type ℓ) → (∥ A ∥'₋₁ → Q) → A → Q
trunc-map' _ _ p x = p ∣ x ∣'

postulate
  trunc'-universal : {A Q : Type ℓ} → is-prop Q
    → is-equiv (trunc-map' A Q)

untrunc' : {A Q : Type ℓ} → is-prop Q
  → (A → Q) → ∥ A ∥'₋₁ → Q
untrunc' z = is-equiv.post-inverse (trunc'-universal z)
untrunc'' : {A Q : Type ℓ} → is-prop Q
  → ∥ A ∥'₋₁ → (A → Q) → Q
untrunc'' ip p f = untrunc' ip f p




-- Cor: No global choice (with ua)
-- Global-choice : ∀ l → Type (lsuc l)
-- Global-choice l = (X : Type l) → ∥ X ∥'₋₁ → X
Global-choice : Agda.Primitive.Setω
Global-choice = {l : Level} (X : Type l) → ∥ X ∥'₋₁ → X

no-global-choice : Global-choice → 𝟘
no-global-choice gc = {!!}
  where
   H : (X : BS 2) → ∥ X .pr₁ ∥'₋₁ → X .pr₁
   H X = gc (pr₁ X)
   H' : (X : BS 2) → X .pr₁
   H' X = {!pr₂ X!}
    -- H' : ∥ BS 2 ∥'₋₁ → BS 2
    -- H' = gc (lsuc lzero) (BS 2)
-- (H : (X : BS 2) → ∥ X ∥₋₁ → X)
-- ((x : BS 2) → X) ↯

-- Axiom of choice asserts
-- ∀ A

-- is-decidable : Type ℓ → Type ℓ
-- is-decidable A = A ∔ ¬ A

-- Cor: no dep fn X + ¬ X
--  (X : Type ℓ) → is-dec X
-- global-lem : ∀ l → Type ?
-- global-lem = λ ℓ → (X : Type ℓ) → is-decidable X

-- no-global-lem : global-lem → 𝟘
-- no-global-lem gl = {!BS 2!}

-- LEM states that (P ∨ ¬ P) ≃ (P ∔ ¬ P)
-- Safe LEM states that (P ∨ ¬ P)
