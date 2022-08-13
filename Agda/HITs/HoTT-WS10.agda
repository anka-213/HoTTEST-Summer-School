-- {-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}
{-# OPTIONS --rewriting --without-K --allow-unsolved-metas --postfix-projections #-}

open import new-prelude

open import Lecture6-notes
open import Lecture5-notes
open import Lecture4-notes
open import HoTT-WS9
open import RandomLemmas

module HoTT-WS10 where

private
  variable
    ℓ l1 l2 l3 : Level
    A B C P Q : Type

-- postulate
--   ∥_∥₋₁ : Type → Type
--   ∣_∣ : {A : Type} → A → ∥ A ∥₋₁
--   trunc : {A : Type} →  is-prop ∥ A ∥₋₁


trunc-map : (A Q : Type) → (∥ A ∥₋₁ → Q) → A → Q
trunc-map _ _ p x = p ∣ x ∣

postulate
  trunc-universal : {A Q : Type} → is-prop Q
    → is-equiv (trunc-map A Q)

untrunc : {Q : Type} → is-prop Q
  → (A → Q) → ∥ A ∥₋₁ → Q
untrunc = λ z → is-equiv.post-inverse (trunc-universal z)

bindtrunc : {B : Type} → (A → ∥ B ∥₋₁) → ∥ A ∥₋₁ → ∥ B ∥₋₁
bindtrunc = untrunc trunc

_>>=_ : ∥ A ∥₋₁ → (A → ∥ B ∥₋₁) → ∥ B ∥₋₁
m >>= f = bindtrunc f m

_[_]>>=_ : ∥ A ∥₋₁ → is-prop P → (A → P) → P
m [ prp ]>>= f = untrunc prp f m

unit : A → ∥ A ∥₋₁
unit = ∣_∣

join : {A : Type} → ∥ ∥ A ∥₋₁ ∥₋₁ → ∥ A ∥₋₁
join = bindtrunc (λ x → x)

bind-unit-l : (k : A → ∥ B ∥₋₁) → (a : A) → bindtrunc k (unit a) ≡ k a
bind-unit-l k a = trunc _ _

bind-unit-r : (m : ∥ A ∥₋₁) → bindtrunc unit m ≡ m
bind-unit-r m = trunc _ _

maptrunc : {B : Type} → (A → B) → ∥ A ∥₋₁ → ∥ B ∥₋₁
maptrunc f = bindtrunc (λ x → ∣ f x ∣)

_↔_ : (P Q : Type) → Type
P ↔ Q = (P → Q) × (Q → P)

-- Q1a

q1a : ∥ ∥ A ∥₋₁ ∥₋₁ ↔ ∥ A ∥₋₁
q1a .pr₁ = untrunc trunc (λ x → x)
q1a .pr₂ = ∣_∣

-- exists = trunc of sigma
Exists :  (A : Type) (B : A → Type) → Type
Exists A B = ∥ Σ x ꞉ A , B x ∥₋₁

syntax Exists A (λ x → b) = ∃ x ꞉ A , b

infix -1 Exists


-- q1b : {B : A → Type} → ∥ Σ x ꞉ A , ∥ B x ∥₋₁ ∥₋₁ ↔ ∥ Σ x ꞉ A , B x ∥₋₁
q1b : {B : A → Type} → (∃ x ꞉ A , ∥ B x ∥₋₁) ↔ ∥ Σ x ꞉ A , B x ∥₋₁
-- q1b .pr₁ = bindtrunc (λ {(a , btr) → maptrunc (λ b → a , b) btr})
q1b .pr₁ abtr = do
  (a , btr) ← abtr
  b ← btr
  ∣ a , b ∣
q1b .pr₂ = maptrunc (λ {(a , b) → a , ∣ b ∣ })
-- q1b : {B : A → Type} → (Σ x ꞉ A , ∥ B x ∥₋₁) ↔ ∥ Σ x ꞉ A , B x ∥₋₁
-- q1b .pr₁ (a , btr) = untrunc trunc (λ b → ∣ a , b ∣) btr
-- q1b .pr₂ = untrunc {!!} λ { (a , b) → a , ∣ b ∣}

trunc-on-fun : {B : A → Type} → ∥ (∀ (x : A) → B x) ∥₋₁ → (∀ (x : A) → ∥ B x ∥₋₁)
trunc-on-fun f x = f >>= λ f' → ∣ f' x ∣

-- trunc-on-fun-bwd : {B : A → Type} → (∀ (x : A) → ∥ B x ∥₋₁) → ∥ (∀ (x : A) → B x) ∥₋₁
-- trunc-on-fun-bwd f = {!ky!}

data 𝟘 : Type where

𝟘-elim : {A : 𝟘 → Type} (x : 𝟘) → A x
𝟘-elim ()
𝟘-nondep-elim : {A : Type} → 𝟘 → A
𝟘-nondep-elim {A} = 𝟘-elim {λ _ → A}

𝟘-prop : is-prop 𝟘
𝟘-prop ()

_↯ = 𝟘-nondep-elim

¬_ : Type → Type
¬ A = A → 𝟘
infix 1000 ¬_
-- -c ∣_∣
q1c1 : (¬ (¬ ∥ A ∥₋₁)) → (¬ (¬ A))
q1c1 nnpa na = nnpa (untrunc (λ ()) na)
-- q1c1 x y = x (untrunc (λ x ()) y)
q1c2 : (¬ (¬ A)) → (¬ (¬ ∥ A ∥₋₁))
q1c2 = λ z z₁ → z (λ z₂ → z₁ ∣ z₂ ∣)
q1c : ¬ (¬ ∥ A ∥₋₁) ↔ ¬ (¬ A)
q1c = q1c1 , q1c2

-- data _∔_ (A B : Type) : Type where
--  inl+ : A → A ∔ B
--  inr+ : B → A ∔ B

-- infixr 20 _∔_
is-decidable : Type → Type
is-decidable A = A ∔ ¬ A


q1d : is-decidable A → (∥ A ∥₋₁ → A)
q1d (inl+ a) pa = a
q1d (inr+ na) pq = untrunc 𝟘-prop na pq ↯
-- q1d (inr+ na) pq = untrunc (λ ()) na pq ↯


-- Question 2

-- flip-equiv : (A ≃ B) → (B ≃ A)
-- flip-equiv (Equivalence map (Inverse post-inverse is-post-inverse pre-inverse is-pre-inverse)) =
--   Equivalence post-inverse (Inverse map (λ x → ! (ap (map ∘ post-inverse) (is-pre-inverse x)) ∙ (ap map (is-post-inverse (pre-inverse x)) ∙ is-pre-inverse x)) map is-post-inverse)


record is-prop-trunc (f : A → P) : Type₁ where
  ptrunc-map : (Q : Type) → (P → Q) → A → Q
  ptrunc-map _ p x = p (f x)
  field
    prop : is-prop P
    ptrunc-universal : {Q : Type} → is-prop Q
      → is-equiv (ptrunc-map Q)
  pequivalence : {Q : Type} → is-prop Q → (P → Q) ≃ (A → Q)
  pequivalence qProp = Equivalence (ptrunc-map _) (ptrunc-universal qProp)
  puntrunc : {Q : Type} → is-prop Q → (A → Q) → P → Q
  puntrunc = λ z → is-equiv.post-inverse (ptrunc-universal z)
  puntrunc-equiv : {Q : Type} → (qProp : is-prop Q) → is-equiv (puntrunc qProp)
  puntrunc-equiv qProp = _≃_.is-equivalence (flip-equiv (pequivalence qProp))


-- postulate
--   ∥_∥₋₁ : Type → Type
--   ∣_∣ : {A : Type} → A → ∥ A ∥₋₁
--   trunc : {A : Type} →  is-prop ∥ A ∥₋₁


-- trunc-map : (A Q : Type) → (∥ A ∥₋₁ → Q) → A → Q
-- trunc-map _ _ p x = p ∣ x ∣

-- postulate
--   trunc-universal : {A Q : Type} → is-prop Q
--     → is-equiv (trunc-map A Q)

-- untrunc : {Q : Type} → is-prop Q
--   → (A → Q) → ∥ A ∥₋₁ → Q
-- untrunc = λ z → is-equiv.post-inverse (trunc-universal z)

-- improve-ie : ∀ {l1 l2 : Level} {A : Type l1} {B : Type l2} {f : A → B} → is-bijection f → is-equiv f
-- improve-ie (Inverse g gf fg) = Inverse g gf g fg

curry : (A × B → C) → A → B → C
curry f a b = f (a , b)
uncurry : (A → B → C) → A × B → C
uncurry f (a , b) = f a b

propMap : is-prop Q → is-prop (P → Q)
propMap ipQ f g = λ≡ (λ x → ipQ (f x) (g x))

module _ (f : A → P) (g : B → Q) where -- P and Q are both propositions
  f×g : A × B → P × Q
  f×g (a , b) = f a , g b
  open is-prop-trunc
  q2a : is-prop-trunc f → is-prop-trunc g
      → is-prop-trunc f×g
  q2a ptf ptg .prop x y = pair≡ (prop ptf _ _) (prop ptg _ _)
  q2a ptf ptg .ptrunc-universal {Q = R} ipR = improve-ie (Inverse
      (λ abr → uncurry (puntrunc ptf (propMap ipR)
                (λ a → puntrunc ptg ipR (curry abr a))))
      (λ pq-r → propMap ipR _ _ )
      (λ ab-r → propMap ipR _ _))

open is-equiv
-- module _ where
--   -- is-equiv-ap : (f : (P → Q) → A → Q) → is-equiv f
--   -- is-equiv-ap : (f : A → B → P) → is-equiv f → (x : A) → is-equiv (f x)
--   is-equiv-ap : (f : (P → Q) → A → Q) → is-equiv f
--               → (g : P → Q) → is-equiv (f g)
--   is-equiv-ap f ie g .post-inverse = {!ie .post-inverse!}
--   is-equiv-ap f ie g .is-post-inverse = {!!}
--   is-equiv-ap f ie g .pre-inverse = {!!}
--   is-equiv-ap f ie g .is-pre-inverse = {!!}

open is-prop-trunc
module _ (f : A → P) (g : A → Q) where -- P and Q are both propositions
  theorem-from-class : is-prop-trunc f → is-prop-trunc g
                     → P ≃ Q
  theorem-from-class ptf ptg = improve (Isomorphism
    (puntrunc ptf (prop ptg) g)
    (Inverse
      (puntrunc ptg (prop ptf) f)
      (λ p → prop ptf _ _)
      (λ q → prop ptg _ _)))
  -- theorem-from-class ptf ptg = Equivalence (puntrunc ptf (prop ptg) g)
  --      {!!}
  -- theorem-from-class ptf ptg = Equivalence (puntrunc ptf (prop ptg) g) (is-equiv-ap _ (puntrunc-equiv ptf (prop ptg)) g)


trunc-is-trunc : is-prop-trunc {A} ∣_∣
trunc-is-trunc = record { prop = trunc ; ptrunc-universal = trunc-universal }

-- b) conclude that
module _ {A B : Type} where
  q2b : ∥ A × B ∥₋₁ ≃ (∥ A ∥₋₁ × ∥ B ∥₋₁)
  q2b = theorem-from-class ∣_∣ tr-map trunc-is-trunc isTrunc
    where
      tr-map : A × B → ∥ A ∥₋₁ × ∥ B ∥₋₁
      tr-map = f×g ∣_∣ ∣_∣
      isTrunc : is-prop-trunc tr-map
      isTrunc = q2a ∣_∣ ∣_∣ trunc-is-trunc trunc-is-trunc


-- Q3
{-
Consider a map f : A → B. Show that the following are equivalent:
(i) f is an equivalence
(ii) f is both surjective and an embedding
-}

is-surj : (f : A → B) → Type
is-surj {A = A} {B = B} f = (b : B) → ∥ fib f b ∥₋₁
-- is-surj {A = A} {B = B} f = (b : B) → ∥ Σ a ꞉ A , fib f b ∥₋₁

-- is-emb : (f : A → B) → Type
-- is-emb f = ∀ x y → is-equiv (ap f {x = x} {y = y})

elim-invs' : ∀ {x : A}
            (f : A → B) (g : B → A)
            (gf : g (f x) ≡ x)
          → ! gf ∙ (refl _ ∙ gf) ≡ refl _
elim-invs' f g gf =
  ! gf ∙ (refl _ ∙ gf) ≡⟨ ap (! gf ∙_) (∙unit-l _) ⟩
  ! gf ∙ gf ≡⟨ !-inv-l gf ⟩
  refl _ ∎

elim-invs : ∀ {x y : A}
            (f : A → B) (g : B → A)
            (gf : (x : A) → g (f x) ≡ x)
            (x=y : x ≡ y) →
            ! (gf x) ∙ (ap g (ap f x=y) ∙ gf y) ≡ x=y
elim-invs f g gf (refl _) = elim-invs' f g (gf _)
  -- ! (gf _) ∙ (ap g (ap f (refl _)) ∙ gf _) ≡⟨⟩
  -- ! (gf _) ∙ (refl _ ∙ gf _) ≡⟨ ap (! (gf _) ∙_) (∙unit-l _) ⟩
  -- ! (gf _) ∙ gf _ ≡⟨ !-inv-l (gf _) ⟩
  -- refl _ ∎

-- elim-invs' : ∀ {x y : A}
--             (f : A → B) (g : B → A)
--             (gf : (x : A) → g (f x) ≡ x)
--             (x=y : x ≡ y) →
--             ! (gf x) ∙ (ap g (ap f x=y) ∙ gf y) ≡ x=y
-- elim-invs' = ?

elim-invs-2 : ∀ {x y : A} (f : A → B)
                (g : B → A) (gf : (z : A) → g (f z) ≡ z)
                (fx=fy : f x ≡ f y) →
              ap f (! (gf x) ∙ (ap g fx=fy ∙ gf y)) ≡ fx=fy
elim-invs-2 {x = x} {y = y} f g gf fx=fy =
  ap f (! (gf _) ∙ (ap g fx=fy ∙ gf _)) ≡⟨ {!!} ⟩
  ap f (! (gf _)) ∙ ap f (ap g fx=fy ∙ gf _) ≡⟨ {!!} ⟩
  ap f (! (gf _)) ∙ (ap f (ap g fx=fy) ∙ ap f (gf _)) ≡⟨ {!!} ⟩
  ! (ap f (gf _)) ∙ (ap f (ap g fx=fy) ∙ ap f (gf _)) ≡⟨ elim-invs g f {!λ b → ap f (gf b)!} fx=fy ⟩
  -- ap f (! (gf _) ∙ (ap g fx=fy ∙ gf _)) ≡⟨ ap (λ z → ap f (! (gf _) ∙ (ap g z ∙ gf _))) fxy-ap ⟩
  -- ap f (! (gf _) ∙ (ap g (ap f x=y) ∙ gf _)) ≡⟨ ap (ap f) (elim-invs f g gf x=y) ⟩
  -- ap f x=y ≡⟨ ! fxy-ap ⟩
  fx=fy ∎
  where
   x=y : x ≡ y
   x=y = {!!}
   fxy-ap : fx=fy ≡ ap f x=y
   fxy-ap = {!!}

module _ (f : A → B) where
  equiv-to-surj : is-equiv f → is-surj f
  equiv-to-surj f-eqv b = ∣ f-eqv' b .pr₁ ∣
    where f-eqv' = conv-is-equiv f-eqv

  equiv-to-emb : is-equiv f → is-emb f
  equiv-to-emb = is-equiv-to-is-emb f
  -- equiv-to-emb ie x y = improve-ie (Inverse
  --   (λ fx=fy →
  --     x ≡⟨ ! (f-is-inv-l x) ⟩
  --     f-inv-l (f x) ≡⟨ ap f-inv-l fx=fy ⟩
  --     f-inv-l (f y) ≡⟨ f-is-inv-l y ⟩
  --     y ∎)
  --   --  ap (ie .post-inverse) fx=fy
  --   (λ x=y → elim-invs f f-inv-l f-is-inv-l x=y)
  --   -- λ where fx=fy → {!ap (ap f)!}
  --   λ fx=fy → {!elim-invs-2 f f-inv-l f-is-inv-l fx=fy!}
  --   )
  --   where
  --     f-inv-l = ie .post-inverse
  --     f-is-inv-l = ie .is-post-inverse
  --     -- f-inv-r = ie .pre-inverse
  --     -- f-is-inv-r = ie .is-pre-inverse
  -- -- equiv-to-emb f-eqv x y = conv-is-equiv-bwd (λ fx=fy →
  -- --    {!ap f-inv fx=fy!})
  -- --   where
  -- --     f-eqv' = conv-is-equiv f-eqv
  -- --     f-inv : (y : B) → A
  -- --     f-inv = λ y → f-eqv' y .pr₁ .pr₁

  surj-emb-to-equiv : is-surj f → is-emb f → is-equiv f
  surj-emb-to-equiv = {!!}

{-
Question 4:

Prove Lawvere’s fixed point theorem: For any two types A and B, if there is a surjective map f : A → BA, then for any h : B → B, there (merely) exists an x : B such that h(x) = x. In other words, show that

􏰄∃(f:A→(A→B))is-surj(f)􏰅 → 􏰄∀(h:B→B)∃(b:B)h(b) = b􏰅
-}

module _ {A B : Type} where
  lawvere : (∃ f ꞉ (A → A → B) , is-surj(f)) → (∀ (h : B → B) → ∃ b ꞉ B , (h b ≡ b))
  lawvere ex h = bindtrunc inner ex
    where
    inner : (Σ f ꞉ (A → A → B) , is-surj(f)) → (∃ b ꞉ B , (h b ≡ b))
    inner (f , f-surj) = maptrunc (λ {(a2 , eq) → f a2 a2 , ! (app≡ eq a2)}) (f-surj F)
      where
      F : A → B
      F a = h (f a a)

{-
Disclaimer In the following exercises, we will use {0,...,n} to denote the elements of Fin_{n+1}, the finite type of n + 1 elements.

5 (⋆)
(a) Construct an equivalence Fin_{n^m} ≃ (Fin_m → Fin_n). Conclude that if A and B are finite,
then (A → B) is finite.
(b) Construct an equivalence Fin_{n!} ≃ (Fin_n ≃ Fin_n). Conclude that if A is finite, then
A ≃ A is finite.

-}

data Fin : ℕ → Type where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

infixr 20 _+_
infixr 30 _*_
infixr 40 _^_

_+_ : ℕ → ℕ → ℕ
zero + m = m
suc n + m = suc (n + m)

_*_ : ℕ → ℕ → ℕ
zero * m = zero
suc n * m = m + n * m

_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ suc m = n * (n ^ m)

fin0-elim : {A : Type} → Fin zero → A
fin0-elim ()

-- 5. a)
fin1≃fin0-to : ∀ n → Fin (n ^ zero) ≃ (Fin zero → Fin n)
fin1≃fin0-to n =
  improve (Isomorphism (λ _ ())
                     (Inverse (λ _ → zero) (λ { zero → refl _})
                              λ {x → λ≡ (λ ())}))
fin0≃to-fin0 : ∀ m → Fin 0 ≃ (Fin (suc m) → Fin zero)
fin0≃to-fin0 m = improve (Isomorphism
  (λ z _ → z) (Inverse
  (λ z → z zero)
  refl
  λ x → fin0-elim (x zero)))

-- Goal: Fin (n * n ^ m) ≃ (Fin (suc m) → Fin n)
-- Have: Fin (n ^ m) ≃ (Fin m → Fin n)

exp-to-func : (n m : ℕ) → Fin (n ^ m) ≃ (Fin m → Fin n)
exp-to-func n zero = fin1≃fin0-to n
exp-to-func n (suc m) = {!exp-to-func n m!}
-- exp-to-func zero (suc m) = fin0≃to-fin0 m
-- exp-to-func (suc n) (suc m) = {!!}

{-

6 (⋆⋆⋆)

Consider a map f : X → Y, and suppose that X is finite.

(a) For y : Y , define inIm_f (y) := ∃x:X (f (x) = y). Show that, if type the Y has decidable equality, then inImf is decidable.

(b) Suppose that f is surjective. Show that the following two statements are equivalent:
  (i) The type Y has decidable equality
  (ii) The type Y is finite

Hint for (i) =⇒ (ii): Induct on the size of X. If f : X ≃ Finn+1 → Y, consider its restriction fn : Finn → Y . Use (a) to do a case distinction on whether or not inImfn(f(n)) holds.

-}

is-discrete : Type → Type
is-discrete A = (x y : A) → is-decidable (x ≡ y)

is-finite : Type → Type
is-finite A = ∃ n ꞉ ℕ , (Fin n ≃ A)

module _ {A B : Type} where
  is-surjective : (f : A → B) → Type
  is-surjective f = (y : B) → ∥ fib f y ∥₋₁

prop-𝟘 : is-prop 𝟘
prop-𝟘 ()

prop-¬ : is-prop (¬ A)
prop-¬ na na' = λ≡ (λ a → prop-𝟘 _ _)

is-discrete-Fin : ∀ n → is-discrete (Fin n)
is-discrete-Fin = {!!}

prop-pair : is-prop P → is-prop Q → is-prop (P × Q)
prop-pair ipP ipQ x y = pair≡ (ipP _ _) (ipQ _ _)

prop-∔-disjoint : is-prop P → is-prop Q → (P → Q → 𝟘) → is-prop (P ∔ Q)
prop-∔-disjoint ipP ipQ disj (inl+ x) (inl+ y) = ap inl+ (ipP x y)
prop-∔-disjoint ipP ipQ disj (inl+ x) (inr+ y) = disj x y ↯
prop-∔-disjoint ipP ipQ disj (inr+ x) (inl+ y) = disj y x ↯
prop-∔-disjoint ipP ipQ disj (inr+ x) (inr+ y) = ap inr+ (ipQ x y)

prop-dec-prop' : ∀ A (ipA : is-prop A) (x y : A ∔ (A → 𝟘)) → x ≡ y
prop-dec-prop' A ipA = prop-∔-disjoint ipA prop-¬ λ a ¬a → ¬a a
-- prop-dec-prop' A ipA (inl+ x) (inl+ y) = ap inl+ (ipA x y)
-- prop-dec-prop' A ipA (inl+ x) (inr+ ny) = ny x ↯
-- prop-dec-prop' A ipA (inr+ nx) (inl+ y) = (nx y) ↯
-- prop-dec-prop' A ipA (inr+ nx) (inr+ ny) = ap inr+ (λ≡ (λ a →  nx a ↯))

-- prop-dec-prop : ∀ A → is-prop (is-decidable A)
prop-dec-prop : ∀ A (x y : ∥ A ∥₋₁ ∔ (∥ A ∥₋₁ → 𝟘)) → x ≡ y
prop-dec-prop A x y = prop-dec-prop' ∥ A ∥₋₁ trunc x y
-- prop-dec-prop A (inl+ x) (inl+ y) = ap inl+ (trunc x y)
-- prop-dec-prop A (inl+ x) (inr+ ny) = ny x ↯
-- prop-dec-prop A (inr+ nx) (inl+ y) = (nx y) ↯
-- prop-dec-prop A (inr+ nx) (inr+ ny) = ap inr+ (λ≡ (λ a →  nx a ↯))

infix  0 case_return_of_
infix  0 case_of_

case_return_of_ : ∀ {a} {b} {A : Set a} (x : A) (B : A → Set b) →
                  ((x : A) → B x) → B x
case x return B of f = f x

case_of_ : A → (A → B) → B
case x of f = case x return _ of f

decide-fin : ∀ {N} (B : Fin N → Type)
           → (∀ (n : Fin N) → is-decidable (B n))
           → (is-decidable (Σ B))
           -- → (is-decidable (Σ n ꞉ ℕ , B n))
decide-fin {N = zero} B dec = inr+ λ ()
decide-fin {N = suc N} B dec = case dec zero of λ where
    (inl+ b) → inl+ (zero , b)
    (inr+ nzero) → case decide-fin {N = N} (λ n → B (suc n)) (λ n → dec (suc n)) of λ where
      (inl+ (n , eq)) → inl+ (suc n , eq)
      (inr+ nsuc) → inr+ λ where
        (zero , eqm) → nzero eqm
        (suc m , eqm) → nsuc (m , eqm)

bwd2 : ∀ {l1 l2 : Level} {A : Type l1} {B : Type l2} → A ≃ B → B → A
bwd2 e = is-equiv.pre-inverse (_≃_.is-equivalence e)

fwd-bwd2 : ∀ {l1 l2 : Level} {A : Type l1} {B : Type l2} → (eq : A ≃ B) → (x : B) → fwd eq (bwd2 eq x) ≡ x
fwd-bwd2 eq x = is-equiv.is-pre-inverse (_≃_.is-equivalence eq) x

mkEquiv : ∀ {l1 l2 : Level} {A : Type l1} {B : Type l2}
          (f : A → B)
          (g : B → A)
          (fg : (g ∘ f) ∼ id)
          (gf : (f ∘ g) ∼ id)
        → A ≃ B
mkEquiv f g fg gf = improve (Isomorphism f (Inverse g fg gf))

idEquiv : A ≃ A
idEquiv = improve (Isomorphism id (Inverse id refl refl))

fin-finite : ∀ {n} → is-finite (Fin n)
fin-finite {n} = ∣ n , idEquiv ∣

inIm : {X Y : Type} (f : X → Y) (y : Y) → Type
inIm {X} {Y} f y = ∃ x ꞉ X , (f (x) ≡ y)

module _ {X Y : Type} (f : X → Y) (fin-X : is-finite X) where



  hlpr : ∀ (y-discr : is-discrete Y) (y : Y) →
        Sigma ℕ (λ n → Fin n ≃ X) → is-decidable (inIm f y)
        -- Sigma ℕ (λ n → Fin n ≃ X) → ∥ Sigma X (λ x → f x ≡ y) ∥₋₁
  hlpr y-discr y (zero , eq) = inr+ (untrunc prop-𝟘 λ {(x , fb) → fin0-elim (bwd eq x)})
  -- hlpr y-discr y (zero , eq) = inr+ (λ x → fin0-elim {!untrunc!})
  hlpr y-discr y (suc n , eq) = case decide-fin _ decide of λ where
      (inl+ (m , eq1)) → inl+ ∣ (fwd eq m , eq1) ∣
      (inr+ nIm) → inr+ (untrunc prop-𝟘 (λ {(x , eq2) → nIm ((bwd2 eq x) , (ap f (fwd-bwd2 eq x) ∙ eq2))}))
  -- hlpr y-discr y (suc n , eq) = case dec-fx=y of λ where
  --     (inl+ eq) → inl+ ∣ x1 , eq ∣
  --     (inr+ neq) → {!decide!}
    where
      decide : ∀ n → is-decidable (f (fwd eq n) ≡ y)
      decide n = y-discr (f (fwd eq n)) y
      x1 = fwd eq zero
      dec-fx=y : is-decidable (f x1 ≡ y)
      dec-fx=y = y-discr (f x1) y
  -- fwd eq zero

  q6a : is-discrete Y → (y : Y) → is-decidable (inIm f y)
  q6a y-discr y = untrunc (prop-dec-prop (fib f y))
                          (hlpr y-discr y) fin-X
  -- q6a y-discr y = inl+ (fin-A >>= {!hlpr y-discr y!})

  {-
  (b) Suppose that f is surjective. Show that the following two statements are equivalent:
    (i) The type Y has decidable equality
    (ii) The type Y is finite

  Hint for (i) ⇒ (ii): Induct on the size of X. If f : X ≃ Fin_{n+1} → Y,
    consider its restriction f_n : Fin_n → Y .
    Use (a) to do a case distinction on whether or not inIm_{f_n} (f(n)) holds.

  -}


pair≡d-refl : {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
         {a : A}
         {b : B a} {b' : B a} (q : b ≡ b' [ B a ])
       → (a , b) ≡ (a , b') [ Σ B ]
pair≡d-refl (refl _) = refl _

finite-to-set : ∀ (fin-Y : is-finite A) → (x y : A) → is-prop (x ≡ y)
finite-to-set = {!!}

image : (f : A → B) → Type
image {A} {B} f = Σ y ꞉ B , inIm f y

module _ {X Y : Type} (f : X → Y) (fin-X : is-finite X) (f-surj : is-surjective f) where

  q6b-fwd : is-discrete Y → is-finite Y
  q6b-fwd y-discr = fin-X >>= lem
    where
      y-set : is-set Y
      y-set = {!!}

      lem1 : ∀ n → (fn : Fin n → Y) → is-surjective fn → (Fin n ≃ X) → ∥ Sigma ℕ (λ n → Fin n ≃ Y) ∥₋₁
      lem1 zero fn fn-surj eq = unit (zero , mkEquiv
        fin0-elim bwd-fn (λ ())
        λ y → fin0-elim (bwd-fn y))
        where
        bwd-fn = (λ y → untrunc (λ ()) (λ {(z , zeq) → bwd eq z}) (f-surj y))
      -- lem1 (suc n) f eq = {!f-surj!}
      lem1 (suc n) fn fn-surj eq = case q6a fn fin-finite y-discr (fn zero) of λ where
        (inl+ 0-inIm) → maptrunc (λ {(x , xeq) → suc n , {!lem (n , ?)!}}) 0-inIm
        (inr+ 0-not-inIm) → {!lem1 n fn'!}
          where
          -- The ristriction of f where n > 0
          fn' : Fin n → Y
          fn' m = fn (suc m)
          -- f-n' m = f (fwd eq (suc m))

          imAtZero = λ y → (fn zero ≡ y) × ¬ (inIm fn' y)
          imAt = λ y → inIm fn' y ∔ imAtZero y
          -- imAt = λ y → inIm fn' y ∔ (fn zero ≡ y)
          -- imAt = λ y → inIm fn' y ∔ ((fn zero ≡ y) × ¬ (inIm fn' y))

          imAtZero-prop : ∀ y → is-prop (imAtZero y)
          imAtZero-prop y = prop-pair (y-set _ y) prop-¬

          imAt-prop : ∀ y → is-prop (imAt y)
          imAt-prop y = prop-∔-disjoint trunc (imAtZero-prop y) λ where
            im (_ , ¬im) → ¬im im

          y-to-im'' : (y : Y) → imAt y
          y-to-im'' y = case q6a fn' fin-finite y-discr y of λ where
             (inl+ y-inIm) → inl+ y-inIm
             (inr+ ¬in-im) → inr+ ((fn-surj y [ imAtZero-prop y ]>>= λ where
               (zero , fn0=y) → fn0=y , ¬in-im
               (suc n' , n'eq) → (¬in-im ∣ n' , n'eq ∣) ↯))


          myIm = Σ imAt

          Y≃im : Y ≃ myIm
          Y≃im = mkEquiv to' fro froTo toFro
            where
            to' : Y → myIm
            to' y = y , y-to-im'' y

            fro : myIm → Y
            -- fro = pr₁
            fro (y , _) = y

            toFro : ∀ im → to' (fro im) ≡ im
            toFro (y , x) = pair≡d-refl (imAt-prop _ _ _)

            froTo : ∀ y → fro (to' y) ≡ y
            froTo y = refl _

          -- map-∔ :
          -- y-to-im' : Y → image fn' ∔ (Σ λ y → fn zero ≡ y)
          -- y-to-im' y = case y-to-im'' y of λ where
          --   (inl+ x) → inl+ (y , x)
          --   (inr+ x) → inr+ (y , x)

          -- y-to-im' y = case q6a fn' fin-finite y-discr y of λ where
          --    (inl+ y-inIm) → inl+ (y , y-inIm)
          --    (inr+ ¬in-im) → inr+ (y , (fn-surj y [ {!!} ]>>= λ where
          --      (zero , fn0=y) → fn0=y
          --      (suc n' , n'eq) → (¬in-im ∣ n' , n'eq ∣) ↯))

          -- y-to-im : Y → image fn' ∔ Unit
          -- y-to-im y = case q6a fn' fin-finite y-discr y of λ where
          --    (inl+ y-inIm) → inl+ (y , y-inIm)
          --    (inr+ ¬in-im) → inr+ ⋆
          --    -- (inr+ ¬in-im) → inr+ {!fn-surj y!}
          -- im-to-y : image fn' ∔ Unit → Y
          -- im-to-y (inl+ (y , y-in-inm)) = y
          -- im-to-y (inr+ ⋆) = fn zero
          -- y-im-y : (y : Y) → im-to-y (y-to-im y) ≡ y
          -- y-im-y y = case y-to-im y of λ where
          --    (inl+ y-inIm) → {!y-to-im y!}
          --    (inr+ ¬in-im) → {!!}
          -- -- y-im-y y = case q6a fn' fin-finite y-discr y of λ where
          -- --    (inl+ y-inIm) → {!y-to-im y!}
          -- --    (inr+ ¬in-im) → {!!}
          -- im-y-im : (im : image fn' ∔ Unit) → y-to-im (im-to-y im) ≡ im
          -- im-y-im (inl+ x) = {!!}
          -- im-y-im (inr+ x) = {!!}

      -- lem (n , eq) = pr₁ q1b ∣ (n , lem1 n eq) ∣
      lem : Sigma ℕ (λ n → Fin n ≃ X) → ∥ Sigma ℕ (λ n → Fin n ≃ Y) ∥₋₁
      lem (n , eq) = lem1 n fn fn-surj eq
        where
          fwd-mp : Fin n → X
          fwd-mp = fwd eq
          eq' : Fin n ≃' X
          eq' = conv-equiv eq
          eq'-bwd : is-equiv' fwd-mp
          eq'-bwd = _≃'_.is-equivalence eq'

          fn = (λ x → f (fwd eq x))
          fn-surj : is-surjective fn
          fn-surj = {!!}

          rev-fn : Y → ∥ Fin n ∥₋₁
          rev-fn y = maptrunc (λ fb → {! (eq'-bwd (pr₁ fb))!}) (f-surj y)
      -- lem (zero , eq) = pr₁ q1b ∣ zero , {!!} ∣
      -- lem (zero , eq) = unit (zero , mkEquiv
      --   fin0-elim bwd-fn (λ ())
      --   λ y → fin0-elim (bwd-fn y))
      --   where
      --   bwd-fn = (λ y → untrunc (λ ()) (λ {(z , zeq) → bwd eq z}) (f-surj y))
      -- lem (suc n , eq) = {!f-surj!} where
      --   -- The ristriction of f where n > 0
      --   f-n : Fin n → Y
      --   f-n m = f (fwd eq (suc m))

      -- lem (suc n , eq) = case q6a f fin-X y-discr (f (fwd eq zero)) of λ where
      --   (inl+ 0-inIm) → maptrunc (λ {(x , xeq) → suc n , {!lem (n , ?)!}}) 0-inIm
      --   (inr+ 0-not-inIm) → {!!}

  -- q6b-fwd f-surj y-discr = do
  --   f-surj' ← f-surj
  --   fin-X' ← fin-X
  --   lem f-surj' fin-X'
  -- q6b-fwd f-surj y-discr = fin-X >>= (λ fnx → {!trunc-on-fun!})
  --   where
  --     lem : ((y : Y) → fib f y) → Σ (λ n → Fin n ≃ X) → ∥ Σ (λ n → Fin n ≃ Y) ∥₋₁
  --     lem srj (zero , eq) = unit (zero , mkEquiv fin0-elim {!f-surj!} {!!} {!!})
  --     lem srj (suc n , eq) = {!!}
  -- q6b-fwd y-discr = do
  --   (n , ne) ← fin-X
  --   {!!}

  q6b-bwd' : ∀ (x y : Y) → Σ (λ n → Fin n ≃ Y) → is-decidable (x ≡ y)
  q6b-bwd' x y (n , eqv) = case (is-discrete-Fin _ xn yn) of λ where
       (inl+ xn=yn) → inl+ (
          x ≡⟨ ! (fwd-bwd2 eqv x) ⟩
          fwd eqv xn ≡⟨ ap (fwd eqv) xn=yn ⟩
          fwd eqv yn ≡⟨ fwd-bwd2 eqv y ⟩
          y ∎)
       (inr+ ¬xn=yn) → inr+ λ x=y → ¬xn=yn (
         xn ≡⟨⟩
         bwd2 eqv x ≡⟨ ap (bwd2 eqv) x=y ⟩
         bwd2 eqv y ≡⟨⟩
         yn ∎)
    where
      xn = bwd2 eqv x
      yn = bwd2 eqv y

  q6b-bwd : is-finite Y → is-discrete Y
  q6b-bwd fin-Y x y = untrunc (prop-dec-prop' (x ≡ y) (finite-to-set fin-Y x y)) (q6b-bwd' x y) fin-Y

{-
 ∥ A ∥₋₁
 ∣_∣ untrunc trunc

          Y≃im = mkEquiv to' fro froTo toFro
            where
            to' : Y → myIm
            to' = ?

            fro : myIm → Y
            fro = ?

            toFro : ∀ b → to' (fro b) ≡ b
            toFro = ?

            froTo : ∀ s → fro (to' s) ≡ s
            froTo = ?


-}
