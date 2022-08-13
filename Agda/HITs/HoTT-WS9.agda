{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}
-- {-# OPTIONS --rewriting --without-K --allow-unsolved-metas --postfix-projections #-}

open import new-prelude

open import Lecture6-notes
open import Lecture5-notes
open import Lecture4-notes

module HoTT-WS9 where

private
  variable A B C : Type

data _∔_ (A B : Type) : Type where
 inl+ : A → A ∔ B
 inr+ : B → A ∔ B

infixr 20 _∔_


is-emb : (f : A → B) → Type
is-emb f = ∀ x y → is-equiv (ap f {x = x} {y = y})

fib : (f : A → B) → B → Type
fib {A = A} f y = Σ x ꞉ A , f x ≡ y

is-contr : ∀ {ℓ} → Type ℓ → Type ℓ
is-contr A = Σ x ꞉ A , (∀ y → x ≡ y)

-- Definition 10.3.4
is-contr-map : (f : A → B) → Type
is-contr-map f = ∀ b → is-contr (fib f b)

is-equiv-new : (f : A → B) → Type
is-equiv-new {B = B} f = (y : B) → is-contr (fib f y)

-- 1. a) Show (A + B) -> C equivalent to (A -> C) x (B -> C)
exp-plus : ((A ∔ B) → C) ≃ ((A → C) × (B → C))
exp-plus = improve (Isomorphism
  (λ f → (λ a → f (inl+ a)) , (λ b → f (inr+ b)))
  (Inverse
    (λ { (f , g) (inl+ a) → f a
       ; (f , g) (inr+ b) → g b})
    (λ ab2c → λ≡ λ { (inl+ a) → refl _ ; (inr+ b) → refl _})
    λ { (a2c , b2c) → pair≡ (refl _) (refl _)}))

-- 1. b) Σ

ex1b : {C : A ∔ B → Type} → ((ab : (A ∔ B)) → C ab) ≃ (((a : A) → C (inl+ a)) × ((b : B) → C (inr+ b)))
ex1b = improve (Isomorphism
  (λ f → (λ a → f (inl+ a)) , (λ b → f (inr+ b)))
  (Inverse
    (λ { (f , g) (inl+ a) → f a
       ; (f , g) (inr+ b) → g b})
    (λ fg → λ≡ (λ { (inl+ a) → refl _ ; (inr+ b) → refl _}))
    λ { (f , g) → pair≡ (refl _) (refl _)}))

-- 2. If B(x) is prop (resp contr) for each (x : A), show that Π[ x : A ] B(x) is prop

ex2 : {B : A → Type} → (∀ (x : A) → is-prop (B x)) → is-prop ((x : A) → B x)
ex2 allProp f g = λ≡ (λ x → allProp x (f x) (g x))

contr-to-prop : is-contr A → is-prop A
contr-to-prop (a , pa) x y = ! (pa x) ∙ pa y

prop-to-contr : is-prop A → A → is-contr A
prop-to-contr ip x = x , ip x

ex2b : {B : A → Type} → (∀ (x : A) → is-contr (B x)) → is-contr ((x : A) → B x)
ex2b allContr  = (λ x → pr₁ (allContr x)) , ex2 (λ x → contr-to-prop (allContr x)) λ x → pr₁ (allContr x)

-- 3. Show is-contr is a prop

contr-path : Type → Type
contr-path A = (x y : A) → is-contr (x ≡ y)

contr-to-contr-path : is-contr A → contr-path A
-- contr-to-contr-path = const-emb-to-contr-path ∘ contr-to-const-emb
contr-to-contr-path ctr x y .pr₁ = contr-to-prop ctr x y
contr-to-contr-path ctr x .x .pr₂ (refl .x) = !-inv-l (pr₂ ctr x)


contr-to-set : is-contr A → is-set A
contr-to-set c x y = contr-to-prop (contr-to-contr-path c x y)
--
-- prop-to-set : is-prop A → is-set A
-- prop-to-set x = {!contr-to-contr-path !}
-- prop-to-set prp = ax-k-to-set (λ x p → {!ap !})

ex3 : is-prop (is-contr A)
-- ex3 (a , pa) (b , pb) = pair≡d (pa b) {!!}
ex3 (a , pa) (b , pb) = pair≡d (pa b) (fwd (transport-to-pathover _ _ _ _)
    -- (λ≡ λ x → {!contr-to-contr-path (b , pb) !}))
    (ex2 (contr-to-set (b , pb) b) _ pb))
    -- (ex2 (prop-to-set (contr-to-prop (b , pb)) b) _ pb))
    -- (ex2 {!prop-to-set (contr-to-prop (b , pb)) b!} _ pb))

-- ex3 (a , pa) (b , pb) = pair≡d (pa b) (PathOver-Π {!!})
-- ex3 (a , pa) (b , pb) = Σ≡ (pa b) (PathOver-Π λ {q → {!PathOver-path-to!}})
-- ex3 (a , pa) (b , pb) = Σ≡ (pa b) {!ex3-lem pa pb (pa b)!}
-- ex3 (a , pa) (b , pb) = Σ≡ (pa b) (fwd (transport-to-pathover _ _ _ _) (λ≡ (λ a' → {!!})))


is-k-2-truncated : ℕ → Type → Type
is-k-2-truncated zero X = is-contr X
is-k-2-truncated (suc k) X = (x y : X) → is-k-2-truncated k (x ≡ y)

-- k+1-truncation : (k : ℕ) → is-k-2-truncated k A → is-k-2-truncated (suc k) A
-- k+1-truncation zero tr x y = contr-to-contr-path tr x y
-- -- k+1-truncation zero tr x y = (pr₁ (pr₁ (fiber-contractible (contr-to-prop tr x y))))
-- --                            , (λ z → ! (pr₂ (pr₁ (some-lem (contr-to-prop tr x y))))
-- --                                   ∙ {!pr₂ (some-lem (contr-to-prop tr x y))!})
-- -- k+1-truncation zero tr x y = (contr-to-prop tr x y) , (λ p → {!pr₂ (some-lem (contr-to-prop tr x y))!})
-- -- k+1-truncation zero tr x y = contr-to-prop tr x y , (λ p → {!!})
-- k+1-truncation (suc k) tr x y p q = k+1-truncation k (tr x y) p q

ex3b : ∀ k → is-prop (is-k-2-truncated k A)
ex3b zero = ex3
ex3b (suc k) = ex2 (λ x → ex2 (λ y → ex3b k))
-- ex3b (suc k) f g = λ≡ (λ x → λ≡ (λ y → ex3b k (f x y) (g x y)))


-- Question 4.

q4 : ∀ (f : A → B) → is-prop (is-equiv-new f)
q4 f = ex2 (λ _ → ex3)


-- Formalize a bunch of stuff from the book in an attempt to prove contr-to-contr-path


-- -- the same as pair≡d
-- Σ≡ : {l1 l2 : Level} {A : Type l1} {B : A → Type l2} {x x' : A} {y : B x} {y' : B x'}
--       → (p : x ≡ x')
--       → y ≡ y' [ B ↓ p ]
--       → _≡_{_}{Σ B} (x , y) (x' , y')
-- Σ≡ (refl _) (reflo) = refl _

improve-ie : ∀ {l1 l2 : Level} {A : Type l1} {B : Type l2} {f : A → B} → is-bijection f → is-equiv f
improve-ie (Inverse g gf fg) = Inverse g gf g fg

-- Theorem 10.3.5 Any contractible map is an equivalence.
contr-map-to-equiv : (f : A → B) → is-contr-map f → is-equiv f
contr-map-to-equiv {A = A} {B = B} f ctr = improve-ie (Inverse g gf fg)
  where
  g : B → A
  g b = pr₁ (pr₁ (ctr b))
  fg : ∀ b → f (g b) ≡ b
  fg b = pr₂ (pr₁ (ctr b))
  gf : ∀ a → g (f a) ≡ a
  gf a = ap pr₁ qq
   where
     p : f (g (f a)) ≡ f a
     p = fg (f a)
     mf : fib f (f a)
     mf = g (f a) , p
     qq : mf ≡ (a , refl _)
     qq = pr₂ (ctr (f a)) (a , refl _)
  -- (λ a → ap pr₁ (pr₂ (ctr (f a)) (pr₁ (ctr (f a)))) ∙ {!pr₂ (pr₁ (ctr (f a)))!})
  -- (λ a → {!pr₂ (pr₁ (ctr (f a)))!})

-- Definition 10.4.1 Coherently invertible map
record is-coh-invertible (f : A → B) : Type where
  constructor CohInv
  field
    is-bij : is-bijection f
  open is-bijection is-bij public
  field
    is-coherent : ε ∘ f ∼ λ x → ap f (η x)

-- Proposition 10.4.2 Any coherently invertible map has contractible fibers.
coh-inv-to-contr-fib : (f : A → B) → is-coh-invertible f → (y : B) → is-contr (fib f y)
coh-inv-to-contr-fib f ch-inv b = (g b , fg b) , λ fb → {!!}
  where
    open is-coh-invertible ch-inv renaming (inverse to g ; η to gf ; ε to fg)

-- Theorem 10.4.6 Any equivalence is a contractible map.
equiv-to-contr-map : (f : A → B) → is-equiv f → is-contr-map f
equiv-to-contr-map f = {!!}

some-lem : ∀ (c : A) → is-contr (Σ x ꞉ A , (c ≡ x))
some-lem c = (c , refl c) , (λ y → pair≡d (y .pr₂) (PathOver-path-to (∙unit-l _)))

const : (A : Type) {B : Type} → (b : B) → A → B
const _ b _ = b

const-emb : Type → Type
const-emb A = is-emb (const A ⋆)
-- const-emb A = is-emb {A} {𝟙} (λ _ → ⋆)


contr-to-equiv : (f : A → B) → is-contr B → is-equiv f
contr-to-equiv = {!!}

-- Exercise 10.3 a, forward direction
book-exercise-10-3-a-1 : is-equiv (const A ⋆) → is-contr A
book-exercise-10-3-a-1 (Inverse post-inverse is-post-inverse pre-inverse is-pre-inverse)
  = post-inverse ⋆ , is-post-inverse
  -- = (pre-inverse ⋆) , λ x →
  --   pre-inverse ⋆                            ≡⟨ ! (is-post-inverse (pre-inverse ⋆)) ⟩
  --   post-inverse (const _ ⋆ (pre-inverse ⋆)) ≡⟨ refl _ ⟩
  --   post-inverse ⋆                           ≡⟨ refl _ ⟩
  --   post-inverse (const _ ⋆ x)               ≡⟨ is-post-inverse x ⟩
  --   x                                        ∎
  -- = (pre-inverse ⋆) , λ x → ! (is-post-inverse (pre-inverse ⋆)) ∙ is-post-inverse x

book-exercise-10-3-a-2 : is-contr A → is-equiv (const A ⋆)
book-exercise-10-3-a-2 ctr = improve-ie (Inverse (λ _ → pr₁ ctr) (pr₂ ctr) (λ x → refl _))

flip-equiv : (A ≃ B) → (B ≃ A)
flip-equiv (Equivalence map (Inverse post-inverse is-post-inverse pre-inverse is-pre-inverse)) =
  Equivalence post-inverse (Inverse map (λ x → ! (ap (map ∘ post-inverse) (is-pre-inverse x)) ∙ (ap map (is-post-inverse (pre-inverse x)) ∙ is-pre-inverse x)) map is-post-inverse)

-- Exercise 10.3 b
module _ (f : A → B) where
  book-exercise-10-3-b-1 : is-contr A → is-contr B → is-equiv f
  book-exercise-10-3-b-1 (x , p) ctrB = improve-ie (Inverse (λ _ → x) p (contr-to-prop ctrB (f x)))
  book-exercise-10-3-b-2' : is-equiv f → is-contr A → is-contr B
  book-exercise-10-3-b-2' eq (x , p) = (f x) ,
     λ y → ap f (p (is-equiv.pre-inverse eq y)) ∙ (is-equiv.is-pre-inverse eq y)

book-exercise-10-3-b-2 : (A ≃ B) → is-contr A → is-contr B
book-exercise-10-3-b-2 eq = book-exercise-10-3-b-2' (fwd eq) (_≃_.is-equivalence eq)

book-exercise-10-3-b-3 : (A ≃ B) → is-contr B → is-contr A
book-exercise-10-3-b-3 eq = book-exercise-10-3-b-2 (flip-equiv eq)

-- Definition 11.1.1
module _ {A : Type} {B C : A → Type} where
  tot : (f : (x : A) → B x → C x) → Σ B → Σ C
  tot f (x , y) = x , f x y

-- Theorem 11.1.3 Let 𝑓 : Π (𝑥:𝐴) → 𝐵(𝑥) → 𝐶(𝑥) be a family of maps. The following are equivalent:
module _ {A : Type} {B C : A → Type} (f : (a : A) → B a → C a) where
  theorem-11-1-3-fwd : (∀ (a : A) → is-equiv (f a)) → is-equiv (tot f)
  theorem-11-1-3-fwd mkeqv = Inverse
    (λ { (a , c) → a , is-equiv.post-inverse (mkeqv a) c})
    (λ { (a , b) → pair≡d (refl _) (path-to-pathover (is-equiv.is-post-inverse (mkeqv a) b))})
    (λ { (a , c) → a , is-equiv.pre-inverse (mkeqv a) c})
    (λ { (a , b) → pair≡d (refl _) (path-to-pathover (is-equiv.is-pre-inverse (mkeqv a) b))})

  theorem-11-1-3-bwd : is-equiv (tot f) → (∀ (a : A) → is-equiv (f a))
  theorem-11-1-3-bwd toteq a = Inverse
    (λ c → {! (post-inverse (a , c))!})
    {!!}
    {!!}
    {!!}
    where open is-equiv toteq

-- Theorem 11.2.2 (The fundamental theorem of identity types)
module _ {A : Type} {B : A → Type} (a : A) (f : (x : A) → (a ≡ x) → B x) where
  fund-theorem-id-types-i-to-ii : ((x : A) → is-equiv (f x)) → is-contr (Σ B)
  fund-theorem-id-types-i-to-ii = {!!}
  fund-theorem-id-types-ii-to-i : is-contr (Σ B) → ((x : A) → is-equiv (f x))
  fund-theorem-id-types-ii-to-i = {!!}

-- Theorem 11.4.2 Any equivalence is an embedding.
is-equiv-to-is-emb : (e : A → B) → is-equiv e → is-emb e
is-equiv-to-is-emb e ise x = fund-theorem-id-types-ii-to-i x (λ y → ap e)
  (book-exercise-10-3-b-2 lem (equiv-to-contr-map e ise (e x)))
  -- is-contr (Σ (λ y → e x ≡ e y))
  where
    lem : Σ (λ y → e y ≡ e x) ≃ Σ (λ y → e x ≡ e y) -- = fib e (e x)
    lem = {!!}

-- contr-to-const-emb : is-contr A → const-emb A
contr-to-const-emb : is-contr A → is-emb (const A ⋆)
contr-to-const-emb = is-equiv-to-is-emb _ ∘ book-exercise-10-3-a-2

-- is-contr A implies is-equiv(const) which implies is-emb(const)
contr-given-a-to-const-emb : (A → is-contr A) → const-emb A
contr-given-a-to-const-emb c x y = contr-to-const-emb (c x) x y
-- contr-given-a-to-const-emb c x y = {!is-equiv-to-is-emb _ (contr-to-const-emb (c x) x y)!} -- is-contr A implies is-equiv(const) which implies is-emb(const)
-- contr-given-a-to-const-emb c x y = Inverse (λ _ → contr-to-prop (c x) x y) (λ x₁ → {!!}) (λ _ → contr-to-prop (c x) x y) {!!}

axiom-k : (A : Type) → Type
axiom-k A = (x : A) (p : x ≡ x) → p ≡ refl x

ax-k-to-set : axiom-k A → is-set A
-- ax-k-to-set axk x .x p (refl .x) = axk x p
ax-k-to-set axk x y p q =
  p             ≡⟨ refl _ ⟩
  p ∙ refl y    ≡⟨ ap (p ∙_) (! (!-inv-l q)) ⟩
  p ∙ (! q ∙ q) ≡⟨ ∙assoc p (! q) q ⟩
  (p ∙ ! q) ∙ q ≡⟨ ap (_∙ q) (axk x (p ∙ ! q)) ⟩
  refl x ∙ q    ≡⟨ ∙unit-l q ⟩
  q             ∎

const-emb-to-contr-path : const-emb A → contr-path A
const-emb-to-contr-path = {!!}


contr-to-contr-path-book : is-contr A → contr-path A
contr-to-contr-path-book = const-emb-to-contr-path ∘ contr-to-const-emb
