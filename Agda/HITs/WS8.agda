{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

open import new-prelude
open import Lecture5-notes
-- open import Solutions4 using (ap-!; to-from-base; to-from-loop; s2c ; b2c ; c2s; susp-func)
-- open import prelude
-- open import decidability
-- open import sums
module WS8 where

-- is-prop : Type → Type
-- is-prop X = (x y : X) → x ≡ y

_↔_ : Type -> Type -> Type
A ↔ B = (A → B) × (B → A)

h-level : ℕ → Type → Type
h-level zero    A = (a b : A) → is-prop (a ≡ b)
h-level (suc n) A = (a b : A) → h-level n (a ≡ b)

data _∔_ (A B : Type) : Type where
 inl : A → A ∔ B
 inr : B → A ∔ B

infixr 20 _∔_

Path : ∀ (A : Type) → A → A → Type
Path A x y = x ≡ y
syntax Path A x y = x ≡ y [ A ]

-- record is-equiv {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) : Type (l1 ⊔ l2) where
--   constructor Inverse
--   field
--     post-inverse    : B → A
--     is-post-inverse : post-inverse ∘ f ∼ id
--     pre-inverse     : B → A
--     is-pre-inverse  : f ∘ pre-inverse ∼ id

-- record _≃_ {l1 l2 : Level} (A : Type l1) (B : Type l2) : Type (l1 ⊔ l2) where
--   constructor
--     Equivalence
--   field
--     map : A → B
--     is-equivalence : is-equiv map

variable A B : Type
inl≠inr : (a : A) (b : B) → ¬ (inl a ≡ inr b)
inl≠inr = λ a b ()
-- or more formally via coding
-- inl => 𝟙, inr => 𝟘

un-inl : {a b : A} → inl a ≡ inl b [ A ∔ B ] → a ≡ b
un-inl = {!!}

e1-1 : is-prop A → is-prop B → is-prop (A ∔ B) ↔ (A → ¬ B)
e1-1 ipA ipB =
  (λ ipAB a b → inl≠inr a b (ipAB (inl a) (inr b)))
  ,
  λ { a¬b (inl x) (inl y) → ap inl (ipA x y)
    ; a¬b (inl x) (inr y) → 𝟘-nondep-elim (a¬b x y)
    ; a¬b (inr x) (inl y) → 𝟘-nondep-elim (a¬b y x)
    ; a¬b (inr x) (inr y) → ap inr (ipB x y)
    }

-- inl-equiv : (a b : A) → (inl a ≡ inl b [ A ∔ B ]) ≃ a ≡ b
-- inl-equiv = ?

-- truncation invariant under equivalence

e1-2 : (k : ℕ) → h-level (suc (suc k)) A → h-level (suc (suc k)) B → h-level (suc (suc k)) (A ∔ B)
e1-2 k hA hB (inl a) (inl b) p q = {!hA a b (un-inl p) (un-inl q)!}
e1-2 k hA hB (inl a) (inr b) p q = 𝟘-nondep-elim (inl≠inr a b p)
e1-2 k hA hB (inr a) (inl b) p q = 𝟘-nondep-elim (inl≠inr b a (sym p))
e1-2 k hA hB (inr a) (inr b) p q = {!hB a b!}
