**TODO:** this needs to be cleaned and should follow the style of the
  other exercise sheets.

```agda
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Exercises7-my where

open import cubical-prelude
open import Lecture7-notes
```

We define P to be a family of types in this file (**TODO:** this used
to be B, but there is now a clash)

```agda
variable
  A : Type ℓ
  B : Type ℓ
  P : A → Type ℓ
```

# Exercise 1

State and prove funExt for dependent functions f g : (x : A) → B x

```agda
funExt' : {f g : (x : A) → P x} → (∀ x → f x ≡ g x) → f ≡ g
funExt' p = λ i x → p x i

```
Experiment with pattern matching

```text
postulate Q : Type

-- fromq : Q → A
-- fromq q = {!q!}

```

# Exercise 2

Generalize the type of ap to dependent function f : (x : A) → B x
(hint: the result should be a PathP)

```agda
apd : (f : (a : A) → P a) {x y : A} → (p : x ≡ y) → PathP (λ i → P (p i)) (f x) (f y)
apd f p i = f (p i)
```

# Exercise 3

State and prove that inhabited propositions are contractible

```agda

inhabited-prop-is-contr : isProp A → A → isContr A
inhabited-prop-is-contr ip a = a , ip a
```
# Exercise 4

We could have stated isProp as follows:

```agda
isProp' : Type ℓ → Type ℓ
isProp' A = (x y : A) → isContr (x ≡ y)
```

Prove that isProp' A implies isProp A.

```agda
iP'-to-iP : isProp' A → isProp A
iP'-to-iP iP' x y = pr₁ (iP' x y)

```
TODO: For the converse we need path composition, see ExerciseSession2 ???

# Exercise 5

Prove isPropΠ:

```agda
isPropΠ : (h : (x : A) → isProp (P x)) → isProp ((x : A) → P x)
isPropΠ h f g = funExt' {f = f} {g = g} λ x → h x _ _
-- isPropΠ h f g i x = h x (f x) (g x) i
```

# Exercise 6

Prove the inverse of funExt (sometimes called happly):

```agda
funExt⁻ : {f g : (x : A) → P x} → f ≡ g → ((x : A) → f x ≡ g x)
funExt⁻ p x = λ i → p i x
```

# Exercise 7

Use funExt⁻ to prove isSetΠ:

```agda
isSetΠ : (h : (a : A) → isSet (P a)) → isSet ((a : A) → P a)
-- isSetΠ h f g p q = {!funExt' {f = f} {g}!}
isSetΠ h x y p q = λ i j a → h a (x a) (y a) (funExt⁻ p a) (funExt⁻ q a) i j
-- isSetΠ h x y p q = {!funExt⁻ p!}
```


# Exercise 8 (harder): alternative contractibility of singletons

We could have defined the type of singletons as follows

```agda
singl' : {A : Type ℓ} (a : A) → Type ℓ
singl' {A = A} a = Σ x ꞉ A , x ≡ a
```

Prove the corresponding version of contractibility of singetons for
singl' (hint: use a suitable combinations of connections and ~_)

```agda
isContrSingl' : (x : A) → isContr (singl' x)
isContrSingl' x = {!!}
```

# Exercise 9: Equality in Σ-types

Having the primitive notion of equality be heterogeneous is an
easily overlooked, but very important, strength of cubical type
theory. This allows us to work directly with equality in Σ-types
without using transport:

**TODO:** turn these into exercises

```agda
module _ {A : Type ℓ} {B : A → Type ℓ'} {x y : Σ A B} where

  ΣPathP : Σ p ꞉ pr₁ x ≡ pr₁ y , PathP (λ i → B (p i)) (pr₂ x) (pr₂ y)
         → x ≡ y
  ΣPathP eq i = pr₁ eq i , pr₂ eq i

  PathPΣ : x ≡ y
         → Σ p ꞉ pr₁ x ≡ pr₁ y , PathP (λ i → B (p i)) (pr₂ x) (pr₂ y)
  PathPΣ eq = (λ i → pr₁ (eq i)) , (λ i → pr₂ (eq i))

  -- The fact that these cancel is proved by refl
```

If one looks carefully the proof of prf in Lecture 7 uses ΣPathP
inlined, in fact this is used all over the place when working
cubically and simplifies many proofs which in Book HoTT requires long
complicated reasoning about transport.

# Exercise 10

Prove some equivalences of HITs:

- Susp(Unit) = Interval
- Susp(Bool) = S1
...

# Exercise 11

Define suspension using the Pushout HIT and prove that it's equivalent
to Susp.
