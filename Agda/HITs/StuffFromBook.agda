{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}
-- {-# OPTIONS --rewriting --without-K --allow-unsolved-metas --postfix-projections #-}

open import new-prelude

open import Lecture6-notes
open import Lecture5-notes
open import Lecture4-notes
open import HoTT-WS9

module StuffFromBook where

private
  variable
    ℓ l1 l2 l3 : Level

private
  variable A B C : Type ℓ
  variable Al Bl Cl : Type ℓ



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
record is-coh-invertible (f : A → B) : Type {!!} where
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

const : (A : Type ℓ) {B : Type ℓ} → (b : B) → A → B
const _ b _ = b

const-emb : Type ℓ → Type ℓ
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
module _ {A : Type ℓ} {B : A → Type l2} (a : A) (f : (x : A) → (a ≡ x) → B x) where
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

axiom-k : (A : Type ℓ) → Type ℓ
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
contr-to-contr-path-book = {!const-emb-to-contr-path!}
-- contr-to-contr-path-book = const-emb-to-contr-path ∘ contr-to-const-emb
