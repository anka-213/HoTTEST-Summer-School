# Week 02 - Agda Exercises

## Please read before starting the exercises

**The exercises are designed to increase in difficulty so that we can cater to
our large and diverse audience. This also means that it is *perfectly fine* if
you don't manage to do all exercises: some of them are definitely a bit hard for
beginners and there are likely too many exercises! You *may* wish to come back
to them later when you have learned more.**

Having said that, here we go!

This is a markdown file with Agda code, which means that it displays nicely on
GitHub, but at the same time you can load this file in Agda and fill the holes
to solve exercises.

**Please make a copy of this file to work in, so that it doesn't get overwritten
  (in case we update the exercises through `git`)!**

```agda
{-# OPTIONS --without-K --allow-unsolved-metas --postfix-projections #-}

module 02-Exercises-my where

open import prelude
open import decidability
open import sums
```

## Part I: Propositions as types


### Exercise 1 (★)

Prove
```agda
uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
uncurry f (a , b) = f a b

curry : {A B X : Type} → (A × B → X) → (A → B → X)
curry f a b = f (a , b)
```
You might know these functions from programming e.g. in Haskell.
But what do they say under the propositions-as-types interpretation?


### Exercise 2 (★)

Consider the following goals:
```agda
[i] : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
[i] (inl (a , b)) = inl a , inl b
[i] (inr c) = inr c , inr c

[ii] : {A B C : Type} → (A ∔ B) × C → (A × C) ∔ (B × C)
[ii] (inl (a , b)) = inl a , inl b
[ii] (inr c) = inr c , inr c

[iii] : {A B : Type} → ¬ (A ∔ B) → ¬ A × ¬ B
[iii] z = (λ x → z (inl x)) , (λ x → z (inr x))

DNE = ∀ {A : Type} → ¬ (¬ A) → A

[iv]-type : Type₁
[iv]-type = {A B : Type} → ¬ (A × B) → ¬ A ∔ ¬ B

-- [iv]-to-dne : [iv]-type → DNE
-- [iv]-to-dne = {!!}

-- [iv] : {A B : Type} → ¬ (A × B) → ¬ A ∔ ¬ B
-- [iv] z = {!-d!}

[v] : {A B : Type} → (A → B) → ¬ B → ¬ A
[v] f nb = λ a → nb (f a)

[vi]-type = {A B : Type} → (¬ A → ¬ B) → B → A
-- [vi] : {A B : Type} → (¬ A → ¬ B) → B → A
-- [vi] f b = {!!} -- impossible

[vi]-to-dne : [vi]-type → DNE
[vi]-to-dne [vi] nna = [vi] (λ na → 𝟘-elim (nna na)) ⋆

-- dne-to-[vi] : DNE → [vi]-type
-- dne-to-[vi] = {!!}

[vii]-type = {A B : Type} → ((A → B) → A) → A

-- [vii] : {A B : Type} → ((A → B) → A) → A
-- [vii] f = {!-d!} -- impossible in general unless we can produce an arbitrary B

lem-[vii] : [vii]-type → {A : Type} → ¬ (¬ A) → A
lem-[vii] [vii] nna = [vii] λ x → 𝟘-elim (nna x)

[viii] : {A : Type} {B : A → Type}
    → ¬ (Σ a ꞉ A , B a) → (a : A) → ¬ B a
[viii] ns a b = ns (a , b)

[ix]-type : Type₁
[ix]-type = {A : Type} {B : A → Type}
    → ¬ ((a : A) → B a) → (Σ a ꞉ A , ¬ B a)

-- [ix] : {A : Type} {B : A → Type}
--     → ¬ ((a : A) → B a) → (Σ a ꞉ A , ¬ B a)
-- [ix] nf = {!!} -- impossible



[x] : {A B : Type} {C : A → B → Type}
      → ((a : A) → (Σ b ꞉ B , C a b))
      → Σ f ꞉ (A → B) , ((a : A) → C a (f a))
[x] a2p = (λ x → pr₁ (a2p x)) , (λ a → pr₂ (a2p a))
```
For each goal determine whether it is provable or not.
If it is, fill it. If not, explain why it shouldn't be possible.
Propositions-as-types might help.


### Exercise 3 (★★)

```agda
¬¬_ : Type → Type
¬¬ A = ¬ (¬ A)

¬¬¬ : Type → Type
¬¬¬ A = ¬ (¬¬ A)
```
In the lecture we have discussed that we can't  prove `∀ {A : Type} → ¬¬ A → A`.
What you can prove however, is
```agda
tne : ∀ {A : Type} → ¬¬¬ A → ¬ A
tne ¬¬¬a a = ¬¬¬a (λ ¬a → ¬a a)
```


### Exercise 4 (★★★)
Prove
```agda
¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor f ¬¬a = λ ¬b → ¬¬a (λ a → ¬b (f a))

¬¬-kleisli : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
¬¬-kleisli f nna = tne (¬¬-functor f nna)
```
Hint: For the second goal use `tne` from the previous exercise





## Part II: `_≡_` for `Bool`

**In this exercise we want to investigate what equality of booleans looks like.
In particular we want to show that for `true false : Bool` we have `true ≢ false`.**

### Exercise 1 (★)

Under the propositions-as-types paradigm, an inhabited type corresponds
to a true proposition while an uninhabited type corresponds to a false proposition.
With this in mind construct a family
```agda
bool-as-type : Bool → Type
bool-as-type true = 𝟙
bool-as-type false = 𝟘
```
such that `bool-as-type true` corresponds to "true" and
`bool-as-type false` corresponds to "false". (Hint:
we have seen canonical types corresponding true and false in the lectures)


### Exercise 2 (★★)

Prove
```agda
bool-≡-char₁ : ∀ (b b' : Bool) → b ≡ b' → (bool-as-type b ⇔ bool-as-type b')
bool-≡-char₁ b .b (refl .b) = (λ x → x) , (λ x → x)
```


### Exercise 3 (★★)

Using ex. 2, concldude that
```agda
true≢false : ¬ (true ≡ false)
true≢false eq = pr₁  helper  ⋆
  where helper = bool-≡-char₁ true false eq

true≢false₁ : ¬ (true ≡ false)
true≢false₁ ()
```
You can actually prove this much easier! How?


### Exercise 4 (★★★)

Finish our characterisation of `_≡_` by proving
```agda
bool-≡-char₂ : ∀ (b b' : Bool) → (bool-as-type b ⇔ bool-as-type b') → b ≡ b'
bool-≡-char₂ true true (b'2b , b2b') = refl true
bool-≡-char₂ true false (b'2b , b2b') = 𝟘-elim (b'2b ⋆)
bool-≡-char₂ false true (b'2b , b2b') = 𝟘-elim (b2b' ⋆)
bool-≡-char₂ false false (b'2b , b2b') = refl false
```


## Part III (🌶)
A type `A` is called *discrete* if it has decidable equality.
Consider the following predicate on types:
```agda
has-bool-dec-fct : Type → Type
has-bool-dec-fct A = Σ f ꞉ (A → A → Bool) , (∀ x y → x ≡ y ⇔ (f x y) ≡ true)
```
Prove that
```agda

-- out-sigma : {A B : Type} {C : A → B → Type}
--       → (Σ f ꞉ (A → B) , ((a : A) → C a (f a)))
--       → ((a : A) → (Σ b ꞉ B , C a b))
-- out-sigma = {!!}

sigma-fun : {A B : Type} {C : A → B → Type}
      → ((a : A) → (Σ b ꞉ B , C a b))
      → Σ f ꞉ (A → B) , ((a : A) → C a (f a))
sigma-fun = [x]

decidable-equality-char : (A : Type) → has-decidable-equality A ⇔ has-bool-dec-fct A
decidable-equality-char A .pr₁ dec-eq =
        [x] {C = λ x fx  → ∀ y → x ≡ y ⇔ (fx y) ≡ true}
  λ x → [x] {C = λ y fxy →       x ≡ y ⇔ fxy    ≡ true}
  λ y → ∔-nondep-elim (λ p → true , ((λ _ → refl true) , (λ _ → p)))
                      (λ np → false , ((λ p → 𝟘-nondep-elim (np p)) , λ {()}))
                      (dec-eq x y)
-- decidable-equality-char A .pr₁ dec-eq .pr₁ a b = ∔-nondep-elim (λ _ → true) (λ _ → false) (dec-eq a b)
-- decidable-equality-char A .pr₁ dec-eq .pr₂ a .a .pr₁ (refl .a) = ∔-elim (λ x → ∔-nondep-elim (λ _ → true) (λ _ → false) x ≡ true) (λ x → refl true) (λ x → 𝟘-nondep-elim (x (refl a))) (dec-eq a a)
-- decidable-equality-char A .pr₁ dec-eq .pr₂ a b .pr₂ = {!!}
decidable-equality-char A .pr₂ (_~_ , iso-f) a b = {!iso!}
  where iso = iso-f a b
  -- ∔-nondep-elim {!!} {!!} {!iso-f a b!}
```
