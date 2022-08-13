# Week 8 - Cubical Agda Exercises

## Standard disclaimer:

**The exercises are designed to increase in difficulty so that we can cater to
our large and diverse audience. This also means that it is *perfectly fine* if
you don't manage to do all exercises: some of them are definitely a bit hard for
beginners and there are likely too many exercises! You *may* wish to come back
to them later when you have learned more.**

Having said that, here we go!

In case you haven't done the other Agda exercises:
This is a markdown file with Agda code, which means that it displays nicely on
GitHub, but at the same time you can load this file in Agda and fill the holes
to solve exercises.

**When solving the problems,
please make a copy of this file to work in, so that it doesn't get overwritten
(in case we update the exercises through `git`)!**


```agda
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Exercises8-my where

open import cubical-prelude
open import Lecture7-notes
open import Lecture8-notes
open import Solutions7

private
  variable
    A B : Type ℓ

```

## Part I: `transp` and `hcomp`

### Exercise 1 (★)

Prove the propositional computation law for `J`:

```
my-J : {x : A} (P : (y : A) → x ≡ y → Type ℓ'')
    (d : P x refl) {y : A} (p : x ≡ y) → P y p
my-J {x = x} P d {y} p = subst {A = singl x}
    (λ z → P (z .pr₁) (z .pr₂))
    (isContrSingl x .pr₂ (y , p)) d
-- subst (λ X → P (pr₁ X) (pr₂ X)) (isContrSingl x .pr₂ (_ , p)) d

subst-refl : (B : A → Type ℓ') {x : A} → (b : B x) → subst B refl b ≡ b
subst-refl B b = transportRefl b

JRefl : {A : Type ℓ} {x : A} (P : (z : A) → x ≡ z → Type ℓ'')
  (d : P x refl) → J P d refl ≡ d
-- JRefl {x = x} P d = {!J P d refl!}
JRefl {x = x} P d = transportRefl d
-- JRefl {x = x} P d = subst-refl ((λ z → P (z .pr₁) (z .pr₂))) d
  -- where
  -- isContrSingl x .pr₂ (x , refl)

```

### Exercise 2 (★★)

Using `transp`, construct a method for turning dependent paths into paths.

**Hint**:
Transport the point `p i` to the fibre `A i1`, and set `φ = i` such that the
transport computes away at `i = i1`.
```text
   x ----(p i)----> y
  A i0    A i      A i1
```

```

-- transp-ex : (A : I → Type ℓ) (i : I) → (x : A i0) → A i1
-- transp-ex A i x = transp (λ j → A {!j!}) i x

fromPathP : {A : I → Type ℓ} {x : A i0} {y : A i1} →
  PathP A x y → transport (λ i → A i) x ≡ y
fromPathP {A = A} p i = transp (λ j → A (j ∨ i)) i (p i)
-- fromPathP {A = A} {x = x} {y = y} p i =
--   {!transport (\i -> PathP (\j -> A (i ∨ j)) (transportFill (\i -> A i) x i) y) p !}

fromPathP' : {A : I → Type ℓ} {x : A i0} {y : A i1} →
  PathP A x y → transport (λ i → A i) x ≡ y
fromPathP' {A = A} {x = x} {y = y} p i = comp A
   (λ { j (i = i0) → transportFill (λ k → A k) x j
      ; j (i = i1) → p j
      })
   x

-- hfill : {A : Type ℓ} {φ : I} (u : ∀ i → Partial φ A) (u0 : A [ φ ↦ u i0 ]) (i : I) → A
myComp : ∀ {ℓ} (A : (i : I) → Type ℓ) {φ : I} (u : ∀ i → Partial φ (A i)) (a : A i0 [ φ ↦ u i0 ]) → A i1
myComp A {φ} u a = comp A {φ = φ} u {!outS a!}
```

### Exercise 3 (★★★)

Using `hcomp`, cunstruct a method for turning paths into dependent paths.

**Hint**:
At each point `i`, the verical fibre of the following diagram should lie in
`A i`. The key is to parametrise the bottom line with a dependent path from `x`
to `transport A x`. This requires writing a `transp` that computes away at
`i = i0`.

```text
       x  - - - -> y
       ^           ^
       ¦           ¦
  refl ¦           ¦ p j
       ¦           ¦
       ¦           ¦
       x ---> transport A x
```



```
toPathP : {A : I → Type ℓ} {x : A i0} {y : A i1} →
  transport (λ i → A i) x ≡ y → PathP A x y
toPathP {A = A} {x = x} p i =
  hcomp (λ where
          j (i = i0) → x
          j (i = i1) → p j
        ) (transportFill (λ k → A k) x i)
```

### Exercise 4 (★)

Using `toPathP`, prove the following lemma, which lets you fill in dependent
lines in hProps, provided their boundary.

```
isProp→PathP : {A : I → Type ℓ} (p : (i : I) → isProp (A i))
  (a₀ : A i0) (a₁ : A i1) → PathP A a₀ a₁
isProp→PathP p a₀ a₁ = toPathP (p i1 _ a₁)
```


### Exercise 5 (★★)

Prove the following lemma charictarising equality in subtypes:

```
Σ≡Prop : {A : Type ℓ} {B : A → Type ℓ'} {u v : Σ A B} (h : (x : A) → isProp (B x))
       → (p : pr₁ u ≡ pr₁ v) → u ≡ v
-- Σ≡Prop {B = B} {u = u} {v = v} h p i = (p i) , h (p i) {!pr₂ u!} {!!} i
Σ≡Prop {B = B} {u = u} {v = v} h p = ΣPathP (p , toPathP (h _ _ _))
```

### Exercise 6 (★★★)

Prove that `isContr` is a proposition:

**Hint**:
This requires drawing a cube (yes, an actual 3D one)!

```
isPropIsContr : {A : Type ℓ} → isProp (isContr A)
isPropIsContr (c0 , h0) (c1 , h1) j = (h0 c1 j) , (λ y i → hcomp
  (λ where
    k (i = i0) → h0 c1 (j ∧ k)
    k (i = i1) → h0 y k
    k (j = i0) → h0 y (i ∧ k)
    k (j = i1) → h0 (h1 y i) k)
  c0)
```
             y
       y  --------->  y
       ∧              ∧
       |              |
h0 y i |              |  h1 y i
       |              |
       |              |
       c0 ----------> c1
            h0 c1 j

https://q.uiver.app/?q=WzAsOCxbMiwyLCJ5Il0sWzQsMiwieSJdLFsyLDQsImNfMCJdLFs0LDQsImMxIl0sWzAsMCwiY18wIl0sWzAsNiwiY18wIl0sWzYsNiwiY18wIl0sWzYsMCwiYzAiXSxbMiwwLCJoMCh5LGkpIiwxXSxbMiwzLCJoXzAoYzEsaikiLDJdLFszLDEsImgxKHksaSkiLDFdLFswLDEsInkiLDAseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJzcXVpZ2dseSJ9fX1dLFs0LDAsImhfMCh5LGspIiwxXSxbNSwyLCJrIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoic3F1aWdnbHkifX19XSxbNiwzLCJoXzAoY18xLGspIiwxXSxbNywxLCJoXzAgXFw7IHkgXFw7IGsiLDFdLFs1LDYsImoiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJzcXVpZ2dseSJ9fX1dLFs1LDQsImkiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJzcXVpZ2dseSJ9fX1dLFs0LDcsIiIsMSx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6InNxdWlnZ2x5In19fV0sWzYsNywiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoic3F1aWdnbHkifX19XSxbMTYsOSwiaF8wKGMxLGpcXHdlZGdlIGopIiwxLHsic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfX1dLFsxOCwxMSwiaF8wIFxcOyB5IFxcOyBrIiwxLHsic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfX1dLFsxNyw4LCJoXzAgXFw7IHkgXFw7IChpIFxcd2VkZ2UgaykiLDIseyJzaG9ydGVuIjp7InNvdXJjZSI6MjAsInRhcmdldCI6MjB9fV0sWzE5LDEwLCJoXzAgXFw7IChoXzEgXFw7IHkgXFw7IGkpIFxcOyBrIiwwLHsic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfX1dXQ==

h0 y i = ?10 (j = i0) : A (blocked on _212)
h1 y i = ?10 (j = i1) : A (blocked on _212)
?10 (i = i1) = y : A (blocked on _210, belongs to problem 348)
?10 (i = i0) = h0 c1 j : A
