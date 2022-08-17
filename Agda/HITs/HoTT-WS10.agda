-- {-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}
{-# OPTIONS --rewriting --without-K --allow-unsolved-metas --postfix-projections #-}

open import new-prelude

open import Lecture6-notes
open import Lecture5-notes
open import Lecture4-notes
open import HoTT-WS9
open import RandomLemmas
open import AlternativeEquivalence

module HoTT-WS10 where

private
  variable
    ℓ l1 l2 l3 : Level
    A B C D P Q : Type
    Al Bl : Type ℓ

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

_<&>_ : {B : Type} → ∥ A ∥₋₁ → (A → B) → ∥ B ∥₋₁
x <&> f = maptrunc f x


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

-- elim-invs-2 : ∀ {x y : A} (f : A → B)
--                 (g : B → A) (gf : (z : A) → g (f z) ≡ z)
--                 (fx=fy : f x ≡ f y) →
--               ap f (! (gf x) ∙ (ap g fx=fy ∙ gf y)) ≡ fx=fy
-- elim-invs-2 {x = x} {y = y} f g gf fx=fy =
--   ap f (! (gf _) ∙ (ap g fx=fy ∙ gf _)) ≡⟨ {!!} ⟩
--   ap f (! (gf _)) ∙ ap f (ap g fx=fy ∙ gf _) ≡⟨ {!!} ⟩
--   ap f (! (gf _)) ∙ (ap f (ap g fx=fy) ∙ ap f (gf _)) ≡⟨ {!!} ⟩
--   ! (ap f (gf _)) ∙ (ap f (ap g fx=fy) ∙ ap f (gf _)) ≡⟨ elim-invs g f {!λ b → ap f (gf b)!} fx=fy ⟩
--   -- ap f (! (gf _) ∙ (ap g fx=fy ∙ gf _)) ≡⟨ ap (λ z → ap f (! (gf _) ∙ (ap g z ∙ gf _))) fxy-ap ⟩
--   -- ap f (! (gf _) ∙ (ap g (ap f x=y) ∙ gf _)) ≡⟨ ap (ap f) (elim-invs f g gf x=y) ⟩
--   -- ap f x=y ≡⟨ ! fxy-ap ⟩
--   fx=fy ∎
--   where
--    x=y : x ≡ y
--    x=y = {!!}
--    fxy-ap : fx=fy ≡ ap f x=y
--    fxy-ap = {!!}

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


flip-iso : A ≅ B → B ≅ A
flip-iso (Isomorphism bijection (Inverse inverse η ε)) = Isomorphism inverse (Inverse bijection ε η)

idEquiv : Al ≃ Al
idEquiv = improve (Isomorphism id (Inverse id refl refl))

fin-suc≅fin+Unit : ∀ N → Fin (suc N) ≅(Fin N ∔ Unit)
-- fin-suc≃fin+Unit n = {!!}
fin-suc≅fin+Unit N = mkIso to' fro froTo toFro
            where
            to' : Fin (suc N) → Fin N ∔ Unit
            to' zero = inr+ ⋆
            to' (suc m) = inl+ m

            fro : Fin N ∔ Unit → Fin (suc N)
            fro (inl+ m) = suc m
            fro (inr+ ⋆) = zero

            toFro : ∀ b → to' (fro b) ≡ b
            toFro (inl+ m) = refl _
            toFro (inr+ ⋆) = refl _

            froTo : ∀ s → fro (to' s) ≡ s
            froTo zero = refl _
            froTo (suc m) = refl _

fin-suc≃fin+Unit : ∀ N → Fin (suc N) ≃ (Fin N ∔ Unit)
fin-suc≃fin+Unit n = improve (fin-suc≅fin+Unit n)

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

empty-equiv : (A → 𝟘) → (B → 𝟘) → A ≃ B
empty-equiv f g = mkEquiv (𝟘-nondep-elim ∘ f) (𝟘-nondep-elim ∘ g) (λ x → f x ↯) λ x → g x ↯

distr-∔-× : (A × C ∔ B × C) ≃ ((A ∔ B) × C)
distr-∔-× = {!!}

unit-×-l : A ≃ (Unit {ℓ} × A)
unit-×-l = mkEquiv (_,_ ⋆) pr₂ refl refl

fin-suc : ∀ n → (Unit ∔ Fin n) ≃ Fin (suc n)
fin-suc = {!!}
  -- where
  -- lem : (Fin n ∔ Unit) ≃ Fin (suc n)
  -- lem = improve (flip-iso (fin-suc≅fin+Unit n))

fin-plus : (n m : ℕ) → Fin (n + m) ≃ (Fin n ∔ Fin m)
fin-plus zero m = {!!}
fin-plus (suc n) m = {!fin-plus n m!}

fin-mul : (n m : ℕ) → Fin (n * m) ≃ (Fin n × Fin m)
-- fin-mul zero m = empty-equiv (λ ()) (λ ())
fin-mul zero m = mkEquiv (λ ()) (λ ()) (λ ()) (λ ())
fin-mul (suc n) m = fin-plus m (n * m) ∙≃ ap≃-∔ unit-×-l (fin-mul n m) ∙≃ distr-∔-× ∙≃ ap≃-× (fin-suc n) idEquiv

fun-from-zero : (f : Fin zero → A) → (λ ()) ≡ f
fun-from-zero f = λ≡ (λ ())

exp-step : ∀ n → (A × (Fin n → A)) ≃ (Fin (suc n) → A)
exp-step {A} N = mkEquiv to' fro froTo toFro
  where
    F = A × (Fin N → A)
    T = Fin (suc N) → A
    to' : F → T
    to' (a , f) zero = a
    to' (a , f) (suc n) = f n

    fro : T → F
    fro f .pr₁ = f zero
    fro f .pr₂ n = f (suc n)

    toFro : ∀ b → to' (fro b) ≡ b
    toFro f = λ≡ (λ where
      zero → refl _
      (suc z) → refl _)

    froTo : ∀ s → fro (to' s) ≡ s
    froTo (a , f) = pair≡ (refl _) (refl _)

-- Goal: Fin (n * n ^ m) ≃ (Fin (suc m) → Fin n)
-- Have: Fin (n ^ m) ≃ (Fin m → Fin n)

exp-to-func : (n m : ℕ) → Fin (n ^ m) ≃ (Fin m → Fin n)
exp-to-func n zero = fin1≃fin0-to n
-- exp-to-func zero (suc m) = fin0≃to-fin0 m
-- exp-to-func (suc n) (suc m) = {!exp-to-func n (suc m)!}
--   where
--     IH : Fin (n * n ^ m) ≃ (Fin (suc m) → Fin n)
--     IH = exp-to-func n (suc m)
--     Goal : Fin (suc n ^ m + n * suc n ^ m) ≃ (Fin (suc m) → Fin (suc n))
--     Goal = {!!}

exp-to-func n (suc m) = Goal
  where
    IH : Fin (n ^ m) ≃ (Fin m → Fin n)
    IH = exp-to-func n m
    Goal : Fin (n * n ^ m) ≃ (Fin (suc m) → Fin n)
    Goal =  (fin-mul n (n ^ m) ∙≃ ap≃-× idEquiv IH) ∙≃ exp-step m

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
is-discrete-Fin .(suc _) zero zero = inl+ (refl zero)
is-discrete-Fin .(suc _) zero (suc m) = inr+ (λ ())
is-discrete-Fin .(suc _) (suc n) zero = inr+ (λ ())
is-discrete-Fin .(suc _) (suc n) (suc m) = map-∔ (ap suc) (λ where neq (refl _) → neq (refl _)) (is-discrete-Fin _ n m)

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

-- unap : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) {x y : A} → f x ≡ f y → x ≡ y
-- unap f (refl x) = refl ?

-- un-inl+ :

discr-∔ : is-discrete A → is-discrete B → is-discrete (A ∔ B)
discr-∔ _==A_ _==B_ (inl+ x) (inl+ y) = map-∔ (ap inl+) (λ {neq (refl _) → neq (refl _)}) (x ==A y)
discr-∔ _==A_ _==B_ (inl+ x) (inr+ y) = inr+ λ ()
discr-∔ _==A_ _==B_ (inr+ x) (inl+ y) = inr+ λ ()
discr-∔ _==A_ _==B_ (inr+ x) (inr+ y) = map-∔ (ap inr+) (λ {neq (refl _) → neq (refl _)}) (x ==B y)

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


pair≡d-prop-trunc : {l1 : Level} {A : Type l1} {B : A → Type}
         {a a' : A} (p : a ≡ a')
         {b : ∥ B a ∥₋₁} {b' : ∥ B a' ∥₋₁}
       → (a , b) ≡ (a' , b') [ Σ a ꞉ A , ∥ B a ∥₋₁ ]
pair≡d-prop-trunc p = pair≡d-prop p (λ _ → trunc)

𝟘-elim-irrel : .𝟘 → A
𝟘-elim-irrel ()


module _ {A : Type} (_==_ : is-discrete A) where
  ¬¬ = λ x → ¬ (¬ x)
  dneg : B → ¬¬ B
  dneg = λ z z₁ → z₁ z
  private
    -- Thanks to decidable equality, we can remove truncation
    untrunc-eq-dneg : (x y : A) → ¬¬ (x ≡ y) → x ≡ y
    untrunc-eq-dneg x y p = case x == y of λ where
      (inl+ x=y) → x=y
      (inr+ x≠y) → p x≠y ↯ -- untrunc 𝟘-prop x≠y p ↯

    -- The set of all points equal to x
    equalPoints-dneg : A → Type
    equalPoints-dneg x = Σ y ꞉ A , ¬¬ (x ≡ y)
    -- is contractible, thanks to the truncation
    equal-contr-dneg : (x : A) → is-contr (equalPoints-dneg x)
    equal-contr-dneg x .pr₁ = x , dneg (refl _)
    equal-contr-dneg x .pr₂ (y , eq) = pair≡d-prop (untrunc-eq-dneg _ _ eq) λ _ → prop-¬
    -- Which means it's also a set
    eqp-set-dneg : ∀ x → is-set (equalPoints-dneg x)
    eqp-set-dneg x = contr-to-set (equal-contr-dneg x)

  discrete-to-set-dneg : is-set A
  discrete-to-set-dneg x y p q =
    p ≡⟨ ! pair≡d-prop-pr₁ ⟩
    ap pr₁ pp ≡⟨ ap (ap pr₁) (inner-prop pp qq) ⟩
    ap pr₁ qq ≡⟨ pair≡d-prop-pr₁ ⟩
    q ∎
    where
    xx = x , dneg ( refl x )
    yy = y , dneg p
    inner-prop : is-prop (xx ≡ yy)
    inner-prop = eqp-set-dneg x xx yy
    pp qq : xx ≡ yy
    pp = pair≡d-prop p λ _ → prop-¬
    qq = pair≡d-prop q λ _ → prop-¬
    new-equality : pp ≡ qq
    new-equality = inner-prop pp qq

  private

    record EqualPointsIrr (a : A) : Type where
      constructor _#_
      field
        elem         : A
        .certificate : a ≡ elem

    forget : (x y : A) → .(p : x ≡ y) → x ≡ y
    forget x y p = case x == y of λ where
      (inl+ x=y) → x=y
      (inr+ x≠y) → 𝟘-elim-irrel (x≠y p)
    equal-contr-irr : (x : A) → is-contr (EqualPointsIrr x)
    equal-contr-irr x .pr₁ = x # refl _
    equal-contr-irr x .pr₂ (y # eq) = case (forget x y eq) of λ where
      (refl .x) → refl _
    eqp-set-irr : ∀ x → is-set (EqualPointsIrr x)
    eqp-set-irr x = contr-to-set (equal-contr-irr x)
  discrete-to-set-irr : is-set A
  discrete-to-set-irr x y p q = {!!}
    where
      help : is-prop ((x # _) ≡ (y # _))
      help = eqp-set-irr x (x # refl _) (y # p)
    -- equal-contr-irr x .pr₂ (y # eq) = ap (_# eq) (forget x y eq)
    -- equalPointsIrr : A → Type
    -- equalPointsIrr x = Σ y ꞉ A , . (x ≡ y)
    -- forget : (x y : A) → (p : x ≡ y) → x ≡ y
    -- forget x y p = case x == y of λ where
    --   (inl+ x=y) → x=y
    --   (inr+ x≠y) → x≠y p ↯

  private
    -- Thanks to decidable equality, we can remove truncation
    untrunc-eq : (x y : A) → ∥ x ≡ y ∥₋₁ → x ≡ y
    untrunc-eq x y p = case x == y of λ where
      (inl+ x=y) → x=y
      (inr+ x≠y) → untrunc 𝟘-prop x≠y p ↯

    -- The set of all points equal to x
    equalPoints : A → Type
    equalPoints x = Σ y ꞉ A , ∥ x ≡ y ∥₋₁
    -- is contractible, thanks to the truncation
    equal-contr : (x : A) → is-contr (equalPoints x)
    equal-contr x .pr₁ = x , ∣ refl _ ∣
    equal-contr x .pr₂ (y , eq) = pair≡d-prop-trunc (untrunc-eq _ _ eq)
    -- Which means it's also a set
    eqp-set : ∀ x → is-set (equalPoints x)
    eqp-set x = contr-to-set (equal-contr x)

  discrete-to-set : is-set A
  discrete-to-set x y p q =
    p ≡⟨ ! pair≡d-prop-pr₁ ⟩
    ap pr₁ pp ≡⟨ ap (ap pr₁) (inner-prop pp qq) ⟩
    ap pr₁ qq ≡⟨ pair≡d-prop-pr₁ ⟩
    q ∎
    where
    inner-prop : is-prop ((x , ∣ refl x ∣) ≡ (y , ∣ p ∣))
    inner-prop = eqp-set x (x , ∣ refl _ ∣) (y , ∣ p ∣)
    pp : (x , ∣ refl x ∣) ≡ (y , ∣ p ∣)
    pp = pair≡d-prop-trunc p
    qq : (x , ∣ refl x ∣) ≡ (y , ∣ p ∣)
    qq = pair≡d-prop-trunc q
    new-equality : pp ≡ qq
    new-equality = inner-prop pp qq
  -- discrete-to-set _==_ x y p q = case x == y of λ where
  --   (inl+ x=y) → {!!}
  --   (inr+ x≠y) → x≠y p ↯
  -- discrete-to-set = {!prop-to-set!}
-- discrete-to-set discr x y p q = {!contr-to-contr-path!}

-- finite-to-set : ∀ (fin-Y : is-finite A) → is-set A
-- -- finite-to-set : ∀ (fin-Y : is-finite A) → (x y : A) → is-prop (x ≡ y)
-- finite-to-set = {!!}

image : (f : A → B) → Type
image {A} {B} f = Σ y ꞉ B , inIm f y

map-to-image : (f : A → B) → A → image f
map-to-image f a = (f a) , ∣ a , (refl _) ∣

map-to-image-surjective : (f : A → B) → is-surjective (map-to-image f)
map-to-image-surjective f (b , iim) = iim <&> λ where (a , fa=b) → a , (pair≡d-prop fa=b λ _ → trunc)

image-discrete : (f : A → B) → is-discrete B → is-discrete (image f)
image-discrete f compare-B (x , xi) (y , yi) = case compare-B x y of λ where
  (inl+ x=y) → inl+ (pair≡d-prop x=y λ _ → trunc)
  (inr+ x≠y) → inr+ λ xi=yi → x≠y (ap pr₁ xi=yi)



discrete-to-finite-fin : ∀ {Y : Type} (n : ℕ) → (fn : Fin n → Y) → is-surjective fn → is-discrete Y → is-finite Y
discrete-to-finite-fin {Y} zero fn fn-surj y-discr = unit (zero , mkEquiv
    fin0-elim bwd-fn (λ ())
    λ y → fin0-elim (bwd-fn y))
  where
    bwd-fn :  Y → Fin zero
    bwd-fn y = fn-surj y [ (λ ()) ]>>= pr₁
  -- bwd-fn = (λ y → untrunc (λ ()) (λ {(z , zeq) → bwd eq z}) (f-surj y))
-- discrete-to-finite-fin (suc n) f eq = {!f-surj!}
-- discrete-to-finite-fin {Y} (suc n) fn fn-surj y-discr = case q6a fn' fin-finite y-discr (fn zero) of λ where
--   -- (inl+ 0-inIm) → maptrunc (λ {(x , xeq) → suc n , {!discrete-to-finite-fin n fn' (fn'-surj 0-inIm)!}}) 0-inIm
--   (inl+ 0-inIm) → discrete-to-finite-fin n fn' (fn'-surj 0-inIm) y-discr
--   (inr+ 0-not-inIm) → {!discrete-to-finite-fin n fn-on-image fnoi-surj discr-im!}
discrete-to-finite-fin {Y} (suc n) fn fn-surj y-discr with q6a (fn ∘ suc) fin-finite y-discr (fn zero)
  -- (inl+ 0-inIm) → maptrunc (λ {(x , xeq) → suc n , {!discrete-to-finite-fin n fn' (fn'-surj 0-inIm)!}}) 0-inIm
... | (inl+ 0-inIm) = discrete-to-finite-fin n fn' (fn'-surj 0-inIm) y-discr
    where
      -- The ristriction of f where n > 0
      fn' : Fin n → Y
      fn' m = fn (suc m)
      fn'-surj : inIm fn' (fn zero) → is-surjective fn'
      fn'-surj 0-inIm y = fn-surj y >>= λ where
        (zero , meq) → 0-inIm <&> λ where (z , zeq) → z , (zeq ∙ meq)
        (suc m , meq) → ∣ m , meq ∣
... | (inr+ 0-not-inIm) = discrete-to-finite-fin n fn-on-image fnoi-surj discr-im <&> λ where
        -- (n , fin-n≃image-fn') → suc n , ((fin-suc≃fin+Unit n ∙≃ ap≃ (_∔ Unit) {!!} fin-n≃image-fn') ∙≃ im'≃Y)
        (n , fin-n≃image-fn') → suc n , ((fin-suc≃fin+Unit n ∙≃ ap≃-∔ fin-n≃image-fn' idEquiv) ∙≃ im'≃Y)
    where
    y-set : is-set Y
    y-set = discrete-to-set y-discr
    -- The ristriction of f where n > 0
    fn' : Fin n → Y
    fn' m = fn (suc m)
    -- f-n' m = f (fwd eq (suc m))

    -- TODO: Prove split Fin + Fin



    fn-on-image : Fin n → image fn'
    fn-on-image = map-to-image fn'

    fnoi-surj : is-surjective fn-on-image
    fnoi-surj = map-to-image-surjective fn'
    discr-im : is-discrete (image fn')
    discr-im = image-discrete fn' y-discr
    -- → is-finite (image fn')

    image-finite : is-finite (image fn')
    image-finite = discrete-to-finite-fin n fn-on-image fnoi-surj discr-im

    -- This is my alternative definition that was easier to show (without with-abstraction)
    imAtZero = λ y → (fn zero ≡ y) × ¬ (inIm fn' y)
    imAt = λ y → inIm fn' y ∔ imAtZero y
    myIm = Σ imAt
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

    y-to-im''' : (y : Y) → imAt y
    y-to-im''' y with q6a fn' fin-finite y-discr y
    ...  | (inl+ y-inIm) = inl+ y-inIm
    ...  | (inr+ ¬in-im) = inr+ ((fn-surj y [ imAtZero-prop y ]>>= λ where
          (zero , fn0=y) → fn0=y , ¬in-im
          (suc n' , n'eq) → (¬in-im ∣ n' , n'eq ∣) ↯))

    -- both-eq : (y : Y) → y-to-im'' y ≡ y-to-im''' y
    -- both-eq y with q6a fn' fin-finite y-discr y
    -- ...  | (inl+ y-inIm) = {!!}
    -- ...  | (inr+ ¬in-im) = {!!}

    -- both-eq' : (y : Y) → y-to-im'' y ≡ y-to-im''' y
    -- both-eq' y = case q6a fn' fin-finite y-discr y of λ where
    --        (inl+ y-inIm) → {!!}
    --        (inr+ ¬in-im) → {!!}

    im-discrete : is-discrete myIm
    im-discrete (x , xi) (y , yi) = case y-discr x y of λ where
      (inl+ x=y) → inl+ (pair≡d-prop x=y imAt-prop)
      (inr+ neq) → inr+ (λ where (refl _) → neq (refl _))

    im≃Y : myIm ≃ Y
    im≃Y = mkEquiv fro to' toFro froTo
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

    -- This is the version from the solutions
    myIm' = image fn' ∔ Unit
    -- myIm' = Σ (inIm fn') ∔ Unit

    im'-discrete : is-discrete myIm'
    im'-discrete = discr-∔
      (λ where
        (x , xeq) (y , yeq) → case y-discr x y of λ where
          (inl+ x=y) → inl+ (pair≡d-prop-trunc x=y)
          (inr+ neq) → inr+ (λ where (refl _) → neq (refl _))
         )
      λ x y → inl+ (refl _)

    im'≃Y : myIm' ≃ Y
    im'≃Y = mkEquiv fro to' toFro froTo
      where
      to' : Y → myIm'
      to' y with q6a fn' fin-finite y-discr y
      ...  | (inl+ y-inIm) = inl+ (y , y-inIm)
      ...  | (inr+ ¬in-im) = inr+ ⋆
      -- y , y-to-im'' y

      fro : myIm' → Y
      fro (inl+ (y , y-inIm)) = y
      fro (inr+ ⋆) = fn zero
      -- fro y with q6a fn' fin-finite y-discr y
      -- ...  | (inl+ y-inIm) = ?
      -- ...  | (inr+ ¬in-im) = ?
      -- fro (y , _) = y

      toFro : ∀ im → to' (fro im) ≡ im
      toFro (inl+ (y , y-inIm)) with q6a fn' fin-finite y-discr y
      ...  | (inl+ y-inIm) = ap inl+ (pair≡d-prop-trunc (refl _))
      ...  | (inr+ ¬in-im) = ¬in-im y-inIm ↯
      toFro (inr+ ⋆) with q6a fn' fin-finite y-discr (fn zero)
      ...  | (inl+ 0-inIm) = 0-not-inIm 0-inIm ↯
      ...  | (inr+ ¬in-im) = refl _

      -- = {!!} -- 0-not-inIm {!!} ↯
      -- toFro y with q6a fn' fin-finite y-discr y
      -- ...  | (inl+ y-inIm) = ?
      -- ...  | (inr+ ¬in-im) = ?
      -- toFro (y , x) = pair≡d-refl (imAt-prop _ _ _)

      froTo : ∀ y → fro (to' y) ≡ y
      -- froTo y = {!!}
      froTo y with q6a fn' fin-finite y-discr y
      ...  | (inl+ y-inIm) = refl _
      ...  | (inr+ ¬in-im) = (fn-surj y [ y-set (fn zero) y ]>>= λ where
          (zero , fn0=y) → fn0=y -- fn0=y , ¬in-im
          (suc n' , n'eq) → (¬in-im ∣ n' , n'eq ∣) ↯
               )

module _ {X Y : Type} (f : X → Y) (fin-X : is-finite X) (f-surj : is-surjective f) where

  q6b-fwd : is-discrete Y → is-finite Y
  q6b-fwd y-discr = fin-X >>= lem
    where
      y-set : is-set Y
      y-set = discrete-to-set y-discr


      -- lem (n , eq) = pr₁ q1b ∣ (n , discrete-to-finite-fin n eq ?) ∣
      lem : Sigma ℕ (λ n → Fin n ≃ X) → ∥ Sigma ℕ (λ n → Fin n ≃ Y) ∥₋₁
      lem (n , eq) = discrete-to-finite-fin n fn fn-surj y-discr
        where
          fwd-mp : Fin n → X
          fwd-mp = fwd eq
          eq' : Fin n ≃' X
          eq' = conv-equiv eq
          eq'-bwd : is-equiv' fwd-mp
          eq'-bwd = _≃'_.is-equivalence eq'

          fn : (x : Fin n) → Y
          fn = (λ x → f (fwd eq x))
          fn-surj : is-surjective fn
          fn-surj y = f-surj y <&> λ where
             (x , fx=y) → (bwd2 eq x) , (ap f (fwd-bwd2 eq x) ∙ fx=y)

          -- rev-fn : Y → ∥ Fin n ∥₋₁
          -- rev-fn y = maptrunc (λ fb → {! (eq'-bwd (pr₁ fb))!}) (f-surj y)

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
  -- q6b-bwd fin-Y x y = untrunc (prop-dec-prop' (x ≡ y) (finite-to-set fin-Y x y)) (q6b-bwd' x y) fin-Y
  q6b-bwd fin-Y x y = untrunc (prop-dec-prop' (x ≡ y) (Y-set x y)) (q6b-bwd' x y) fin-Y
    where
      Y-set : is-set Y
      Y-set = fin-Y [ {!is-prop-is-set!} ]>>= λ where
        fin → {!(q6b-bwd' x y)!}
        --  fin-Y

{-
 ∥ A ∥₋₁
 ∣_∣ untrunc trunc

          Y≃im = mkEquiv to' fro froTo toFro
            where
            F = Fin (suc n)
            T = Fin n ∔ Unit
            to' : F → T
            to' = ?

            fro : T → F
            fro = ?

            toFro : ∀ b → to' (fro b) ≡ b
            toFro = ?

            froTo : ∀ s → fro (to' s) ≡ s
            froTo = ?


-}
