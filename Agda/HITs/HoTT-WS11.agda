-- {-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}
{-# OPTIONS --rewriting --without-K --allow-unsolved-metas --postfix-projections #-}

open import new-prelude

open import Lecture6-notes
open import Lecture5-notes
open import Lecture4-notes
open import HoTT-WS9 hiding (is-emb ; _∔_)
open import HoTT-WS10 hiding (_↔_ ; is-decidable ; _>>=_)
open import RandomLemmas
open import AlternativeEquivalence
open import UnivalenceLecture
open import StuffFromBook

module HoTT-WS11 where

private
  variable
    ℓ l1 l2 l3 : Level
    A B C D P Q : Type ℓ
    AA BB : Type ℓ

open _≃_


-- _≃⟨_⟩_ : (X {Y} {Z} : Type) → X ≅ Y → Y ≅ Z → X ≅ Z
-- _ ≃⟨ d ⟩ e = ≅-trans d e

-- _■ : (X : Type) → X ≅ X
-- _■ = ≃-refl



-- Question 1

q1-1 : equiv-eq (refl A) ≡ idEquiv
q1-1 = refl _

q1-2 : (p : A ≡ B) (q : B ≡ C) → map (equiv-eq (p ∙ q)) ≡ map (equiv-eq q) ∘ map (equiv-eq p)
-- q1-2 : (p : A ≡ B) (q : B ≡ C) → {!!}
q1-2 (refl _) (refl _) = refl _

q1-2' : (p : A ≡ B) (q : B ≡ C) → equiv-eq (p ∙ q) ≡ equiv-eq p ∙≃ equiv-eq q
q1-2' = {!!}

q1-3 : (p : A ≡ B) → map (equiv-eq (! p)) ≡ map (flip-equiv (equiv-eq p))
q1-3 (refl _) = refl _

{-
  ua  : ∀ {l : Level} {X Y : Type l} → X ≃ Y → X ≡ Y
  uaβ : ∀{l : Level} {X Y : Type l} (e : X ≃ Y) {x : X}
     → transport (\ X → X) (ua e) x ≡ fwd e x

-}

open is-equiv

postulate
  ua-equiv : is-equiv (equiv-eq {A = A} {B = B})

eq-equiv : (A ≃ B) → (A ≡ B)
eq-equiv = ua-equiv .post-inverse
eq-equiv₂ : (A ≃ B) → (A ≡ B)
eq-equiv₂ = ua-equiv .pre-inverse

eq-equiv-post : (p : A ≡ B) → eq-equiv (equiv-eq p) ≡ p
eq-equiv-post = ua-equiv .is-post-inverse
eq-equiv-pre : (p : A ≃ B) → equiv-eq (eq-equiv₂ p) ≡ p
eq-equiv-pre = ua-equiv .is-pre-inverse

-- Assume univalence:
q1b-1 : eq-equiv idEquiv ≡ refl A
q1b-1 = eq-equiv-post (refl _)
-- q1b-1 : ua-equiv .post-inverse idEquiv ≡ refl A
-- q1b-1 = ua-equiv .is-post-inverse (refl _)
-- q1b-1 = {!ua-equiv .is-pre-inverse!}

q1b-2 : (p : A ≃ B) (q : B ≃ C) → (eq-equiv (p ∙≃ q)) ≡ (eq-equiv p) ∙ (eq-equiv q)
q1b-2 p q =
  eq-equiv (p ∙≃ q) ≡⟨ {!q1-2' (eq-equiv p) (eq-equiv q)!} ⟩
  -- ? ≡⟨ q1-2 (eq-equiv p) (eq-equiv q) ⟩
  -- ? ≡⟨ ? ⟩
  eq-equiv p ∙ eq-equiv q ∎

-- q2-1

module q2a {A B : Type l1} (P : Type l1 → Type l2)  where

{-
Consider a type familly P : Type → Type, and let p : A = B in Type. We can form
apP (p) : P(A) = P(B)
, and we can transport along p to get an equivalence
p∗ : P(A) ≃ P(B)
.

(a) Show that equiv–eq(apP (p)) = p∗. When Type is univalent, deduce that
apP (p) = eq–equiv(p∗).
-}

  _* : (p : A ≡ B) → P A ≃ P B
  refl .A * = idEquiv
  -- _* p = improve (Isomorphism (transport P p)
  --          (Inverse (transport P (! p))
  --          (λ where x → {!p!})
  --          {!!}))
  q2a-1 : (p : A ≡ B) → equiv-eq (ap P p) ≡ (p *)
  q2a-1 (refl .A) = refl _

  -- Assuming ua
  q2a-2 : (p : A ≡ B) → ap P p ≡ eq-equiv (p *)
  q2a-2 p =
    ap P p ≡⟨ ! (ua-equiv .is-post-inverse (ap P p)) ⟩
    eq-equiv (equiv-eq (ap P p))
           ≡⟨ ap eq-equiv (q2a-1 p) ⟩
    eq-equiv (p *) ∎

{-
(b) Let A,B,C : Type. Using the universal property of propositional truncations, con- struct functions ∥A = B∥ → ∥B = C∥ → ∥A = C∥ and ∥A = B∥ → ∥B = A∥ corresponding to composition of truncated paths and inversion of truncated paths, respectively.
-}

bindtrunc' : {A B : Type ℓ} → (A → ∥ B ∥'₋₁) → ∥ A ∥'₋₁ → ∥ B ∥'₋₁
bindtrunc' = untrunc' trunc'

_>>=_ : {A B : Type ℓ} → ∥ A ∥'₋₁ → (A → ∥ B ∥'₋₁) → ∥ B ∥'₋₁
m >>= f = bindtrunc' f m

liftA2 : {A B C : Type ℓ} → (A → B → C) →  ∥ A ∥'₋₁ → ∥ B ∥'₋₁ → ∥ C ∥'₋₁
liftA2 f pa pb = do
  a ← pa
  b ← pb
  ∣ f a b ∣'

q2b-1 : ∥ A ≡ B ∥'₋₁ → ∥ B ≡ C ∥'₋₁ → ∥ A ≡ C ∥'₋₁
q2b-1 = liftA2 _∙_
-- q2b-1 pp pq = do
--   p ← pp
--   q ← pq
--   ∣ p ∙ q ∣'

-- q2b-1 p q = untrunc'' trunc' p λ where
--     pp → untrunc'' trunc' q λ where
--       qq → ∣ pp ∙ qq ∣'

q2b-2 : ∥ A ≡ B ∥'₋₁ → ∥ B ≡ A ∥'₋₁
q2b-2 pp = do
  p ← pp
  ∣ ! p ∣'


{-
We will use the usual symbols for composition and inversion of truncated paths, since the operation is clear from the context.

Recall (or show) that in the family
X􏰗→(A=X):Type→Type,
a path p:X=Y acts by post-composition: for any q:A=X, we have that
p (q)=. q·p:(A=Y).

(c)Show that in the family
X ↦ ∥A=X∥ : Type→Type
,a path
p:X=Y actsby truncated post-composition:
for any q : ∥A = X∥, we have that
p∗(q) = q · |p| : ∥A = Y ∥ .
-}

_∙∣_ : (p : ∥ A ≡ B ∥'₋₁) → (q : ∥ B ≡ C ∥'₋₁) → ∥ A ≡ C ∥'₋₁
_∙∣_ = q2b-1

module _ {X Y A B : Type}  where
  private
    myFamR : Type lzero → Type (lsuc lzero)
    myFamR X = A ≡ X
    myFam : Type lzero → Type (lsuc lzero)
    myFam X = ∥ A ≡ X ∥'₋₁

  module _ where
    open q2a {A = X} {Y} myFamR

    -- in the family myFam, a path p : X ≡ Y acts by post-composition
    recall : (p : X ≡ Y) → (q : A ≡ X) → map (p *) q ≡ q ∙ p
    recall p q = {!!}
    -- recall (refl .X) (refl .X) = {!map (refl X *) ∣ refl X ∣' ≡ ∣ refl X ∣'

  open q2a {A = X} {Y} myFam


  q2c : (p : X ≡ Y) → (q : ∥ A ≡ X ∥'₋₁) → (map (p *) q) ≡ (q ∙∣ ∣ p ∣')
  q2c = {!!}

-- q3-1

ctr-types = Σ A ꞉ Type , is-contr A

q3-1 : is-contr ctr-types
q3-1 = {!!}
-- X is contr iff the map X -> 𝟙 is an equivalence
-- thus
--   Σ X ꞉ Type , is-contr A
-- ≃⟨ Σ X ꞉ Type , (X ≃ Unit)
-- ≃ Σ X ꞉ Type , (X ≡ Unit)
-- is contractible with center (1 , refl_𝟙)

Type-≤k-2 : (k : ℕ) → Type (lsuc lzero)
Type-≤k-2 k = Σ A ꞉ Type , is-k-2-truncated k A

q3-2 : (k : ℕ) → is-k-2-truncated (suc k) (Type-≤k-2 k)
q3-2 zero = k+1-truncation zero (q3-1)
q3-2 (suc k) = {!!}

-- X=_{U≤k}Y is k-truncated
--  ↓ ~ equivalence
-- (X ≡_U Y)

-- q3.3
¬'_ : Type ℓ → Type ℓ
¬' A = A → 𝟘
infix 1000 ¬'_

q3-3 : ¬' (is-prop (Type-≤k-2 1))
q3-3 = {!!}

q3-4 : ¬' (is-set (Type-≤k-2 2))
q3-4 = {!!}


-- Q 4

-- Give example of type family B : A → Type for which
-- ¬􏰄Π(a:A)B(a)􏰅 −→ 􏰄Σ(a:A)¬B(a)􏰅
-- is false.

module _ where
  private
    counterB : A → Type (lsuc lzero)
    counterB A = BS 2

  BS2 : Type (lsuc lzero)
  BS2 = Σ X ꞉ Type , ∥ Fin 2 ≃ X ∥'₋₁
  -- no function
  -- theorem-from-somewhere : ((X : (BS 2)) → pr₁ X) ≃ 𝟘
  theorem-from-somewhere : ¬' ((X : (BS 2)) → pr₁ X)
  theorem-from-somewhere f = {!!}
  goal : (Σ Xx ꞉ BS 2 , ¬ (pr₁ Xx)) → 𝟘
  goal = {!!}
  ws11q4 :
     Σ A ꞉ Type ,
     Σ B ꞉ (A → Type) ,
     (¬ ((a : A) → B(a)) → Σ a ꞉ A , ¬ B a)
     → 𝟘
  ws11q4 = {!!}

-- Q 5

BAut : (A : Type) → Type (lsuc lzero)
BAut A = Σ X ꞉ Type , ∥ A ≡ X ∥'₋₁
--  is called the path component of A in Type.

-- a) Show that for (X, p), (Y, q) : BAut(A), we have 􏰄(X, p) =BAut(A) (Y, q)􏰅 ≃ (X = Y ).


module _ (Xp Yq : BAut(A)) where
 X = pr₁ Xp
 p = pr₂ Xp
 Y = pr₁ Yq
 qq = pr₂ Yq
 q5a : ((X , p) ≡ (Y , qq)) ≃ (X ≡ Y )
 q5a = {!!}

-- Note that (A,|reflA|) : BAut(A), so that BAut(A) is pointed. Write pt for this base point, and denote Aut(A) := (A ≃ A).

-- (b) Assuming Type is univalent, deduce that (pt =BAut(A) pt) ≃ Aut(A).

{-

Next, show that BAut(A) is connected:
(c) Show that for every (X, p), (Y, q) : BAut(A) we merely have a path:
􏰘􏰘 􏰘(X,p)=BAut(A) (Y,q)􏰘.
-}

{-
Proof:
By (a) , we have
∥ X ≡ Y [ BAut A ] ∥'₋₁ ≃ ∥ X ≡ Y [ A ] ∥'₋₁
and we have

-- mear paths
   p        q
X ---> A ------ Y : ∥ X ≡ Y [ Type ] ∥₋₁

qed?
-}

{-
The type BAut(𝟚) =. BS_𝟚 is also called the universe of 2-element sets. 2
(d) By combining the previous points and exercise 5 from worksheet 10, show that

(pt ≡[ BAut(𝟚) ] pt) ≃ 𝟚
-}

{-
Let Type be a univalent universe, and consider A : Type. Recall (or show!) the type-theoretic
Yoneda lemma (Theorem 13.3.3): for any P : A → Type and a : A we have an equivalence

􏰄Πb:A(a = b) → P(b)􏰅 ≃ P(a).

(a) Suppose Σa:AP(a) is contractible. Show that you then get an equivalence

􏰄Πb:A(a = b) ≃ P(b)􏰅 ≃ P(a).

-}

module _ (A : Type) (P : A → Type) (a : A) where

  yoneda : ((b : A) → (a ≡ b) → P(b)) ≃ P(a)
  yoneda = {!!}

  --
  ws11q6a : is-contr (Σ a ꞉ A , P a)
    → ((b : A) → (a ≡ b) ≃ P(b)) ≃ P(a)
  ws11q6a = {!!}
  -- -- use the fundamental theorem of identity types
  -- -- fund-theorem-id-types-ii-to-i
  -- Use: 11.1.3

  qs11-q6b : is-emb (Path A)
  qs11-q6b = {!!}
    where
    isRep : (p : A → Type lzero) → Type (lsuc lzero)
    isRep p = (Σ a ꞉ A , (_≡_ a ≡ p))
    isRep' : (p : A → Type lzero) → Type (lsuc lzero)
    isRep' p = (Σ a ꞉ A , ∀ (b : A) → ( _≡_ a b ≡ p b))
    -- isRep ≃ isRep'
    isRepP : (p : A → Type lzero) → is-prop (isRep p)
    isRepP p = {!!}
     -- isRep p
     -- = ...
     -- ≃ (Σ a ꞉ A , ∀ (b : A) → ( _≡_ a b ≡ p b))
      where
       helper : isRep p → is-contr (isRep p)
       helper (a , η) = {!!}
       foo : is-contr (Σ b ꞉ A , p b)
       foo = {!!}
       bar : isRep p ≃ isRep' p
       bar = {!!}
       -- ≃ Σ b ꞉ A , p b
       -- ≃ 𝟙
