{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}
-- {-# OPTIONS --rewriting --without-K --allow-unsolved-metas --postfix-projections #-}

open import new-prelude

open import Lecture6-notes
open import Lecture5-notes
open import Lecture4-notes

module HoTT-WS9 where

private
  variable
    ℓ l1 l2 l3 : Level

private
  variable A B C : Type
  variable Al Bl Cl : Type ℓ

data _∔_ (A B : Type ℓ) : Type ℓ where
 inl+ : A → A ∔ B
 inr+ : B → A ∔ B

infixr 1 _∔_


module _ {l1 l2 : Level} {A : Type l1} {B : Type l2} where
  is-emb : (f : A → B) → Type (l1 ⊔ l2)
  is-emb f = ∀ x y → is-equiv (ap f {x = x} {y = y})

  fib : (f : A → B) → B → Type (l1 ⊔ l2)
  fib f y = Σ x ꞉ A , f x ≡ y

is-contr : ∀ {ℓ} → Type ℓ → Type ℓ
is-contr A = Σ x ꞉ A , (∀ y → x ≡ y)

module _ {l1 l2 : Level} {A : Type l1} {B : Type l2} where
  -- Definition 10.3.4
  is-contr-map : (f : A → B) → Type (l1 ⊔ l2)
  is-contr-map f = ∀ b → is-contr (fib f b)

  is-equiv-new : (f : A → B) → Type (l1 ⊔ l2)
  is-equiv-new f = (y : B) → is-contr (fib f y)

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

contr-to-prop : is-contr Al → is-prop Al
contr-to-prop (a , pa) x y = ! (pa x) ∙ pa y

prop-to-contr : is-prop A → A → is-contr A
prop-to-contr ip x = x , ip x

ex2b : {B : A → Type} → (∀ (x : A) → is-contr (B x)) → is-contr ((x : A) → B x)
ex2b allContr  = (λ x → pr₁ (allContr x)) , ex2 (λ x → contr-to-prop (allContr x)) λ x → pr₁ (allContr x)

-- 3. Show is-contr is a prop

contr-path : Type ℓ → Type ℓ
contr-path A = (x y : A) → is-contr (x ≡ y)

contr-to-contr-path : is-contr Al → contr-path Al
-- contr-to-contr-path = const-emb-to-contr-path ∘ contr-to-const-emb
contr-to-contr-path ctr x y .pr₁ = contr-to-prop ctr x y
-- contr-to-contr-path ctr x .x .pr₂ (refl .x) = !-inv-l (pr₂ ctr x)
contr-to-contr-path ctr x .x .pr₂ (refl .x) = {!!}

prop-to-contr-path : is-prop A → contr-path A
prop-to-contr-path ipA x = contr-to-contr-path (x , ipA x) x

contr-to-set : is-contr A → is-set A
contr-to-set c x y = contr-to-prop (contr-to-contr-path c x y)

prop-to-set : is-prop A → is-set A
prop-to-set ipA x y = contr-to-prop (prop-to-contr-path ipA x y)
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

is-k-2-truncated : ℕ → Type ℓ → Type ℓ
is-k-2-truncated zero X = is-contr X
is-k-2-truncated (suc k) X = (x y : X) → is-k-2-truncated k (x ≡ y)

k+1-truncation : {A : Type ℓ} (k : ℕ) → is-k-2-truncated k A → is-k-2-truncated (suc k) A
k+1-truncation zero tr x y = contr-to-contr-path tr x y
-- k+1-truncation zero tr x y = (pr₁ (pr₁ (fiber-contractible (contr-to-prop tr x y))))
--                            , (λ z → ! (pr₂ (pr₁ (some-lem (contr-to-prop tr x y))))
--                                   ∙ {!pr₂ (some-lem (contr-to-prop tr x y))!})
-- k+1-truncation zero tr x y = (contr-to-prop tr x y) , (λ p → {!pr₂ (some-lem (contr-to-prop tr x y))!})
-- k+1-truncation zero tr x y = contr-to-prop tr x y , (λ p → {!!})
k+1-truncation (suc k) tr x y p q = k+1-truncation k (tr x y) p q

ex3b : ∀ k → is-prop (is-k-2-truncated k A)
ex3b zero = ex3
ex3b (suc k) = ex2 (λ x → ex2 (λ y → ex3b k))
-- ex3b (suc k) f g = λ≡ (λ x → λ≡ (λ y → ex3b k (f x y) (g x y)))


-- Question 4.

q4 : ∀ (f : A → B) → is-prop (is-equiv-new f)
q4 f = ex2 (λ _ → ex3)

