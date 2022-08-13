# Week 7 - Cubical Agda Exercises

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

module Exercises7-my2 where

open import cubical-prelude
open import Lecture7-notes
```

```agda
private
  variable
    A : Type ℓ
    B : A → Type ℓ
    P : A → Type ℓ
```

## Part I: Generalizing to dependent functions

### Exercise 1 (★)

State and prove funExt for dependent functions `f g : (x : A) → B x`

```agda
funExt' : {f g : (x : A) → P x} → (∀ x → f x ≡ g x) → f ≡ g
funExt' p = λ i x → p x i

```

### Exercise 2 (★)

Generalize the type of ap to dependent function `f : (x : A) → B x`
(hint: the result should be a `PathP`)

```agda
apd : (f : (a : A) → P a) {x y : A} → (p : x ≡ y) → PathP (λ i → P (p i)) (f x) (f y)
apd f p i = f (p i)
```

## Part II: Some facts about (homotopy) propositions and sets

The first three homotopy levels `isContr`, `isProp` and `isSet`
are defined in `cubical-prelude` in the usual way
(only using path types of course).

### Exercise 3 (★)

State and prove that inhabited propositions are contractible

```agda
inhabited-prop-is-contr : isProp A → A → isContr A
inhabited-prop-is-contr ip a = a , ip a
```

### Exercise 4-old

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

### Exercise 4 (★)

Prove

```agda
isPropΠ : (h : (x : A) → isProp (B x)) → isProp ((x : A) → B x)
isPropΠ h f g = funExt' {f = f} {g = g} λ x → h x _ _
-- isPropΠ h f g i x = h x (f x) (g x) i
```

### Exercise 5 (★)

Prove the inverse of `funExt` (sometimes called `happly`):

```agda
funExt⁻ : {f g : (x : A) → B x} → f ≡ g → ((x : A) → f x ≡ g x)
funExt⁻ p x = λ i → p i x
```

### Exercise 6 (★★)

Use funExt⁻ to prove isSetΠ:

```agda
isSetΠ : (h : (x : A) → isSet (B x)) → isSet ((x : A) → B x)
-- isSetΠ h f g p q = {!isPropΠ {B = λ a → f a ≡ g a} ? (λ a → funExt⁻ p a) (λ a → funExt⁻ q a)!}
-- isSetΠ h f g p q = {!funExt' {f = f} {g}!}
isSetΠ h x y p q = λ i j a → h a (x a) (y a) (funExt⁻ p a) (funExt⁻ q a) i j
-- isSetΠ h x y p q = {!funExt⁻ p!}
```

### Exercise 7 (★★★): alternative contractibility of singletons

We could have defined the type of singletons as follows

```agda
singl' : {A : Type ℓ} (a : A) → Type ℓ
singl' {A = A} a = Σ x ꞉ A , x ≡ a
```

Prove the corresponding version of contractibility of singetons for
`singl'` (hint: use a suitable combinations of connections and `~_`)

```agda
isContrSingl' : (x : A) → isContr (singl' x)
-- isContrSingl' x = (x , refl) , (λ { (y , p) i → p (~ i) , (λ j → {!!})})
isContrSingl' x = (x , refl) , (λ { (y , p) i → p (~ i) , (λ j → p (j ∨ ~ i))})
```

## Part III: Equality in Σ-types
### Exercise 8 (★★)

Having the primitive notion of equality be heterogeneous is an
easily overlooked, but very important, strength of cubical type
theory. This allows us to work directly with equality in Σ-types
without using transport.

Fill the following holes (some of them are easier than you might think):

```agda
module _ {A : Type ℓ} {B : A → Type ℓ'} {x y : Σ A B} where

  ΣPathP : Σ p ꞉ pr₁ x ≡ pr₁ y , PathP (λ i → B (p i)) (pr₂ x) (pr₂ y)
         → x ≡ y
  ΣPathP (p , q) i = p i , q i

  PathPΣ : x ≡ y
         → Σ p ꞉ pr₁ x ≡ pr₁ y , PathP (λ i → B (p i)) (pr₂ x) (pr₂ y)
  PathPΣ pq = (λ i → pr₁ (pq i)) , (λ i → pr₂ (pq i))

  ΣPathP-PathPΣ : ∀ p → PathPΣ (ΣPathP p) ≡ p
  ΣPathP-PathPΣ p = refl

  PathPΣ-ΣPathP : ∀ p → ΣPathP (PathPΣ p) ≡ p
  PathPΣ-ΣPathP p = refl
```

If one looks carefully the proof of prf in Lecture 7 uses ΣPathP
inlined, in fact this is used all over the place when working
cubically and simplifies many proofs which in Book HoTT requires long
complicated reasoning about transport.


## Part III: Some HITs

Now we want prove some identity of HITs analogous to `Torus ≡ S¹ × S¹`
Hint: you can just `isoToPath` in all of them.


### Exercise 9 (★★)

We saw two definitions of the torus:
`Torus` having a dependent path constructor `square`
and `Torus'` with a path constructor `square` that involves composition.

Using these two ideas, define the *Klein bottle* in two different ways.

```agda
data Klein : Type₀ where
  kpoint : Klein
  kline1 : kpoint ≡ kpoint
  kline2 : kpoint ≡ kpoint
  ksquare : PathP (λ i → kline1 i ≡ kline1 i) kline2 (sym kline2)

data Klein' : Type₀ where
  kpoint : Klein'
  kline1 : kpoint ≡ kpoint
  kline2 : kpoint ≡ kpoint
  ksquare : kline1 ∙ kline2 ≡ kline2 ∙ kline1
```

This may or may not be a Klein bottle
```agda
data MbKlein : Type where
  mkpt : MbKlein
  mkloop : mkpt ≡ mkpt
  mkface : mkloop ≡ sym mkloop
```

### Exercise 10 (★★★)

Prove the following facts about suspensions:

```agda

su2i : Susp Unit → Interval
su2i north = zero
su2i south = one
su2i (merid a i) = seg i
i2su : Interval → Susp Unit
i2su zero = north
i2su one = south
i2su (seg i) = merid ⋆ i

isui : section su2i i2su
isui zero = refl
isui one = refl
isui (seg i) = refl

suisu : retract su2i i2su
suisu north = refl
suisu south = refl
suisu (merid a i) = refl

suspUnitChar : Susp Unit ≡ Interval
suspUnitChar = isoToPath (iso su2i i2su isui suisu)
```

Part b
```agda


{-
comp-filler : {x y z : A} (p : x ≡ y) (q : y ≡ z) → PathP (λ i → x ≡ q i) p (p ∙ q)
comp-filler {x = x} p q j i = hfill
    (λ k → λ { (i = i0) → x
             ; (i = i1) → q k
             })
    (inS (p i))
    j

rUnit : {x y : A} (p : x ≡ y) → p ≡ p ∙ refl
  rUnit {x = x} {y = y} p j i = hfill
    (λ { k (i = i0) → x
       ; k (i = i1) → y
       })
    (inS (p i))
    j

-}

hfill' : {A : Type ℓ} {φ : I} (u : ∀ i → Partial φ A) (u0 : A [ φ ↦ u i0 ]) (i : I) → A
hfill' {φ = φ} u u0 i =
  hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                 ; (i = i0) → outS u0
                 }) (outS u0)

hfill3 : {A : Type ℓ} {φ : I} (u : ∀ i → Partial φ A) (u0 : A [ φ ↦ u i0 ]) → outS u0 ≡ hcomp u (outS u0)
hfill3 u ua i = hfill u ua i

-- hcomp-my : {A : Type ℓ} {φ : I} (u : ∀ i → Partial φ A) (u0 : A [ φ ↦ u i0 ]) (i : I) → A
-- hcomp-my {φ = φ} u u0 i = {!hcomp!}
hcomp-my : {A : Type ℓ} {φ : I}
         → (u : I → Partial φ A) → (u0 : A [ φ ↦ u i0 ]) → A
-- hcomp-my {φ = φ} u u0 = hcomp {φ = φ} u (outS u0)
hcomp-my {φ = φ} u u0 = hcomp u (outS u0)
hcomp-my2 : {A : Type ℓ} {φ : I}
         → (u : I → Partial φ A) → (u0 : A [ φ ↦ u i0 ]) → A [ φ ↦ u i1 ]
hcomp-my2 {φ = φ} u u0 = inS (hcomp u (outS u0))


-- hfill-my : {A : Type ℓ} {φ : I} (u : ∀ i → Partial φ A) (u0 : A [ φ ↦ u i0 ]) (i : I) → A [ φ ∨ ~ i ↦ u i1 ]
-- hfill-my u ua i = -- inS (hfill u ua i)
-- hfill-my {φ = φ} u u0 i =
--   hcomp-my2 (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
--                      ; (i = i0) → outS u0
--                      }) (inS (outS u0))
module _ {A : Type ℓ} {φ : I} (u : ∀ i → Partial φ A) (u0 : A [ φ ↦ u i0 ]) (i : I) where
  u1 : (j : I) → Partial (φ ∨ ~ i) A
  u1 = (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                ; (i = i0) → outS u0
                })
  hfill-my : A [ φ ∨ ~ i ↦ u1 i1 ]
  hfill-my = hcomp-my2 u1 (inS (outS u0))
  -- hfill-my2 : A [ φ ↦ u i1 ]
  -- hfill-my2 = inS (
  --   hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
  --                 ; (i = i0) → outS u0
  --                 }) (outS u0)
  --                 )

-- postulate
hcomp-inv-l : {A : Type ℓ} {φ : I} (u : ∀ i → Partial φ A) (u0 : A [ φ ↦ u i0 ])
          -- → hcomp (λ i → u (~ i)) (hcomp u (outS u0)) ≡ outS u0
          → outS u0 ≡ hcomp (λ i → u (~ i)) (hcomp u (outS u0))
-- hcomp-inv-l {φ = φ} u u0 i = hfill3 (λ i → u (~ i)) {!inS (hfill3 u u0 i)!} i
-- hcomp-inv-l {φ = φ} u u0 i = {!hfill (λ i → u (~ i)) (inS (hfill u u0 i)) i!}
hcomp-inv-l {φ = φ} u u0 i =
    -- hcomp (λ j → λ { (φ = i1) → u (~ i ∧ j) 1=1
    hcomp (λ j → λ { (φ = i1) → u (i ∧ ~ j) 1=1
                   ; (i = i0) → outS u0
                   })
      (hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                      ; (i = i0) → outS u0
                      })
                      (outS u0))

-- module _ {A : Type ℓ} {φ : I} (u : ∀ i → Partial φ A) (u0 : A [ φ ↦ u i0 ]) (k : I) where
--   φ₁ : I
--   φ₁ = φ ∨ ~ k ∨ k
--   new-bounds : I → Partial φ₁ A
--   new-bounds i (φ = i1) = u i 1=1
--   new-bounds i (k = i0) = {!!}
--   new-bounds i (k = i1) = {!outS u0!}

--   -- hcomp-my2 (λ i → u (~ i)) (hcomp-my2 u u0) ≡ u0
--   hcomp-inv-l2 : A [ φ₁ ↦ new-bounds i1 ]
--   hcomp-inv-l2 = {!!}

-- _∙_ : {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
-- _∙_ {x = x} p q i = hcomp (λ j → λ { (i = i0) → x
--                                    ; (i = i1) → q j })
--                           (p i)
comp-filler : {x y z : A} (p : x ≡ y) (q : y ≡ z) → PathP (λ i → x ≡ q i) p (p ∙ q)
comp-filler {x = x} p q j i = hfill
            (λ k → λ { (i = i0) → x
                     ; (i = i1) → q k
                     })
            (inS (p i)) j
  -- hcomp (λ j → λ { (i = i0) → x
  --                ; (i = i1) → ? })
  --       ?

-- comp-filler2 : {x y z : A} (p : x ≡ y) (q : y ≡ z) → PathP (λ i → p i ≡ z) (p ∙ q) q
-- comp-filler2 {x = x} p q j i = {!!}
-- comp-filler2 {x = x} p q j i = hfill
--             (λ k → λ { (i = i0) → {!!}
--                      ; (i = i1) → {!!}
--                      })
--             (inS {!p i!}) (~ j)

rUnit : {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
rUnit p = sym (comp-filler p refl)


silly-id : A → A
silly-id a = hcomp {φ = i0} (λ i ()) a

sb2c : Susp Bool → S¹
sb2c north = base
sb2c south = base
sb2c (merid true i) = loop i
sb2c (merid false i) = base

c2sb : S¹ → Susp Bool
c2sb base = north
c2sb (loop i) = (merid true ∙ sym (merid false)) i


csbc-lem' : apd (λ x → sb2c (c2sb x)) loop ≡ loop
csbc-lem' =
  apd (λ x → sb2c (c2sb x)) loop ≡⟨⟩
  (λ i → sb2c (c2sb (loop i))) ≡⟨⟩
  apd sb2c (merid true ∙ sym (merid false)) ≡⟨⟩
  apd sb2c (merid true) ∙ apd sb2c (sym (merid false)) ≡⟨⟩
  loop ∙ refl ≡⟨ rUnit loop ⟩
  loop ∎

csbc-lem : PathP (λ i → sb2c (c2sb (loop i)) ≡ loop i) refl refl
csbc-lem i j = csbc-lem' j i

csbc : section sb2c c2sb
csbc base = refl
csbc (loop i) = csbc-lem i

PathOver : {A : Type ℓ} (B : A → Type ℓ)
         {a1 a2 : A} (p : a1 ≡ a2)
         (b1 : B a1) (b2 : B a2) → Type (ℓ ⊔ ℓ)
PathOver B p b1 b2 = PathP (λ i → B (p i)) b1 b2

syntax PathOver B p b1 b2 = b1 ≡ b2 [ B ↓ p ]

-- PathOver-roundtrip≡ : ∀ {A B : Type} (g : B → A) (f : A → B)
--                         {a a' : A} (p : a ≡ a')
--                         {q : g (f a) ≡ a}
--                         {r : g (f a') ≡ a'}
--                       → sym q ∙ ((ap g (ap f p)) ∙ r) ≡ p
--                       → q ≡ r [ (\ x → g (f x) ≡ x) ↓ p ]
-- PathOver-roundtrip≡ g f p h = {!!}

-- from-to-loop : sym refl ∙
--                ap c2sb (ap sb2c (merid true)) ∙ merid false
--                ≡ merid true
-- from-to-loop =
--   sym refl ∙ ap c2sb (ap sb2c (merid true)) ∙ merid false ≡⟨ {!!} ⟩
--   merid true ∎

-- helper : ∀ i → c2sb (sb2c (merid true i)) ≡ merid true i
-- helper : PathP (λ i → c2sb (sb2c (merid true i)) ≡ merid true i) refl (merid false)
helper : PathP (λ i → (merid true ∙ sym (merid false)) i ≡ merid true i) refl (merid false)
-- helper = PathOver-roundtrip≡ c2sb sb2c (merid true) from-to-loop
helper i j = hcomp
  (λ { k (i = i0) → north
    ; k (i = i1) → merid false (~ k ∨ j)
    ; k (j = i1) → merid true i
     })
  (merid true i)

helper' : PathP (λ i → north ≡ merid false i) (merid true ∙ sym (merid false)) (merid true)
helper' i = comp-filler (merid true) (sym (merid false)) (~ i)

sbcsb : retract sb2c c2sb
sbcsb north = refl
sbcsb south = merid false
-- sbcsb (merid true i) = helper i
sbcsb (merid true i) j = helper' j i
sbcsb (merid false i) = λ j → merid false (j ∧ i)

suspBoolChar : Susp Bool ≡ S¹
suspBoolChar = isoToPath (iso sb2c c2sb csbc sbcsb)

```


### Exercise 11 (★★★)

Define suspension using the Pushout HIT and prove that it's equal to Susp.

data Susp (A : Type ℓ) : Type ℓ where

```agda
PSusp : (A : Type ℓ) → Type ℓ
PSusp A = Pushout {A = A} (λ _ → ⋆) (λ _ → ⋆)

module _ {A : Type ℓ} where
  ps2s : PSusp A → Susp A
  ps2s (inl x) = north
  ps2s (inr x) = south
  ps2s (push a i) = merid a i

  s2ps : Susp A → PSusp A
  s2ps north = inl ⋆
  s2ps south = inr ⋆
  s2ps (merid a i) = push a i

  ps-sect : section ps2s s2ps
  ps-sect north = refl
  ps-sect south = refl
  ps-sect (merid a i) = refl

  ps-retr : retract ps2s s2ps
  ps-retr (inl x) = refl
  ps-retr (inr x) = refl
  ps-retr (push a i) = refl

  ps=s : PSusp A ≡ Susp A
  ps=s = isoToPath (iso ps2s s2ps ps-sect ps-retr)
```

### Exercise 12 (?)

Alternative definition of torus
```agda
data Torus' : Type where
  point : Torus'
  line1' : point ≡ point
  line2' : point ≡ point
  square' : line1' ∙ line2' ≡ line2' ∙ line1'
```
(Probably very hard) Exercise: prove that Torus ≃ Torus'
```agda

module _ {A : I → Type ℓ} {x : A i0} {y : A i1} where
  toPathP : transp A i0 x ≡ y → PathP A x y
  toPathP p i = hcomp (λ j → λ { (i = i0) → x
                               ; (i = i1) → p j })
                      (transp (λ j → A (i ∧ j)) (~ i) x)

  fromPathP : PathP A x y → transp A i0 x ≡ y
  fromPathP p i = transp (λ j → A (i ∨ j)) i (p i)

-- fromPathP square : transp (λ i → line1 i ≡ line1 i) i0 line2 ≡ line2

Square :
  {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
  {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
  (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
  → Type _
Square a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋

private
  variable
    x y z w : A

_∙∙_∙∙_ : w ≡ x → x ≡ y → y ≡ z → w ≡ z
(p ∙∙ q ∙∙ r) i =
  hcomp (λ j → λ { (i = i0) → p (~ j)
                 ; (i = i1) → r j })
        (q i)

∙∙-fill : (p : w ≡ x) → (q : x ≡ y) → (r : y ≡ z)
        → PathP (λ i → p (~ i) ≡ r i) q (p ∙∙ q ∙∙ r)
∙∙-fill p q r k i =
  hcomp (λ j → λ { (i = i0) → p (~ j ∨ ~ k)
                 ; (i = i1) → r (j ∧ k)
                 ; (k = i0) → q i
                 })
        (q i)

-- comp-filler : {x y z : A} (p : x ≡ y) (q : y ≡ z)
--             → PathP (λ i → x ≡ q i) p (p ∙ q)

{-
         hcomp
   pt ------------> pt
    ^    hcomp      ^
    |               |
 pt | pt      line2 | line1
    |               |
    |    line1      |
   pt ------------> pt
         line2


         hcomp
   pt ------------> pt
    ^    hcomp      ^
    |               |
 pt | pt      line2 | line1
    |               |
    |    line1      |
   pt ------------> pt
         line2


-- square : PathP (λ i → line1 i ≡ line1 i) line2 line2

-- square i0 = line2
-- square i i0 = line1 i

-}

from-square'-alt : Square (line1 ∙ line2) ((sym line1) ∙∙ line1 ∙∙ refl)
                          (line2 ∙ line1) ((sym line2) ∙∙ line2 ∙∙ refl)
from-square'-alt i j = hcomp (λ
  { k (i = i0) (j = i0) → point
  ; k (i = i0) (j = i1) → line2 k
  ; k (i = i1) (j = i0) → line1 k
  ; k (i = i1) (j = i1) → point
  })
  (square j i)


-- Same as below: https://tinyurl.com/mr3v325m
-- Rotate diagram: https://q.uiver.app/?q=WzAsMTIsWzUsMSwiYiJdLFs0LDIsImMiXSxbMSwxLCJhIl0sWzIsMiwiYSJdLFsyLDQsImEiXSxbNCw0LCJjIl0sWzEsNSwiYiJdLFs1LDUsImMiXSxbMCwwLCJiIl0sWzYsMCwiYiJdLFs2LDYsImIiXSxbMCw2LCJiIl0sWzAsMSwicSIsMV0sWzIsMywiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoic3F1aWdnbHkifX19XSxbMiwwLCJwIiwxXSxbMywxLCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbNiw3LCJxIiwxXSxbNyw1LCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJzcXVpZ2dseSJ9fX1dLFs2LDQsIiFwIiwxXSxbNCw1LCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbMiw2LCJwIiwxXSxbMyw0LCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJzcXVpZ2dseSJ9fX1dLFsxLDUsIiIsMSx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6InNxdWlnZ2x5In19fV0sWzAsNywicSIsMV0sWzgsMiwiIXAiLDFdLFs4LDksIiIsMSx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6InNxdWlnZ2x5In19fV0sWzksMCwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoic3F1aWdnbHkifX19XSxbOSwxMCwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoic3F1aWdnbHkifX19XSxbMTAsNywicSIsMV0sWzgsMTEsIiIsMSx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6InNxdWlnZ2x5In19fV0sWzExLDEwLCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJzcXVpZ2dseSJ9fX1dLFsxMSw2LCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJzcXVpZ2dseSJ9fX1dLFsxNSwxOSwiIiwxLHsib2Zmc2V0Ijo0LCJzaG9ydGVuIjp7InNvdXJjZSI6MjAsInRhcmdldCI6MjB9LCJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbMTQsMTYsIiIsMSx7InNob3J0ZW4iOnsic291cmNlIjoxMCwidGFyZ2V0IjoxMH0sInN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFsyNSwzMCwiIiwxLHsib2Zmc2V0IjotNSwic2hvcnRlbiI6eyJzb3VyY2UiOjEwLCJ0YXJnZXQiOjEwfSwic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoic3F1aWdnbHkifX19XV0=

rot-lem : {a b c : A} (p : a ≡ b) (q : b ≡ c) → Square p q p q
rot-lem {b = b} p q i j = hcomp (λ
  {k (i = i0) → p (j ∨ ~ k)
  ;k (j = i0) → p (i ∨ ~ k)
  ;k (i = i1) → q (j ∧ k)
  ;k (j = i1) → q (i ∧ k)
  }) b

rotate : {a b c : A} (p : a ≡ b) (q : b ≡ c) → (refl ∙∙ p ∙∙ q) ≡ (p ∙∙ q ∙∙ refl)
rotate p q i j = hcomp (λ
     { k (j = i0) → p (~ k ∧ i)
     ; k (j = i1) → q (k ∨ i)
     }) (rot-lem p q i j)


square-to-comps : {a : A} (p : a ≡ a) (q : a ≡ a) → Square p p q q
                → (q ∙∙ p ∙∙ refl) ≡ (refl ∙∙ p ∙∙ q)
square-to-comps p q sq i j = hcomp (λ
     { k (j = i0) → q (~ k ∧ ~ i)
     ; k (j = i1) → q (k ∨ ~ i)
     }) (sq (~ i) j)

from-square'-3 : (line2 ∙∙ line1 ∙∙ refl) ≡ (refl ∙∙ line1 ∙∙ line2)
from-square'-3 i j = hcomp (λ
     { k (j = i0) → line2 (~ k ∧ ~ i)
     ; k (j = i1) → line2 (k ∨ ~ i)
     }) (square j (~ i))

square-tp : Square line2 line2 line1 line1
square-tp = square

from-square' : line2 ∙ line1 ≡ line1 ∙ line2
from-square' = rotate line2 line1 ∙ from-square'-3


-- from-square' i j = hcomp (λ
--      { k (j = i0) → point
--      ; k (j = i1) → square (i ∨ k) ({!~ i!} ∨ k)
--      }) {!square (i ∨ j) (i ∧ j)!}

-- from-square' i j = hcomp (λ
--      { k (i = i0) (j = i0) → point
--      ; k (i = i0) (j = i0) → point
--      ; k (i = i0) (j = i1) → {!!}
--      ; k (i = i1) (j = i1) → {!!}
--      }) {!square (i ∨ j) (i ∧ j)!}

t'2t : Torus' → Torus
t'2t point = point
t'2t (line1' i) = line1 i
t'2t (line2' i) = line2 i
t'2t (square' i j) = from-square' (~ i) j

-- https://q.uiver.app/?q=WzAsMTIsWzMsMSwiYSJdLFs0LDEsImMiXSxbMywyLCJhIl0sWzQsMiwiYyJdLFswLDQsImEiXSxbMSw0LCJhIl0sWzAsNSwiYSJdLFsxLDUsImEiXSxbMiwzLCJiIl0sWzUsMywiYyJdLFsyLDAsImEiXSxbNSwwLCJiIl0sWzAsMSwicCBcXGNkb3QgcSIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFsyLDMsInEgXFxjZG90XFxjZG90XFwgcFxcIFxcY2RvdFxcY2RvdFxcIHJlZmwiLDIseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbNCw2LCJwIiwxXSxbNSw3LCJwIiwxXSxbNiw3LCJxIiwxXSxbNCw1LCJxIiwxXSxbOCwyLCJcXHNpbSBxIiwyXSxbOSwzLCIiLDAseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJzcXVpZ2dseSJ9fX1dLFs4LDksInAiLDFdLFswLDIsIiIsMSx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6InNxdWlnZ2x5In19fV0sWzEsMywiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoic3F1aWdnbHkifX19XSxbMTAsMTEsInAiLDFdLFsxMCwwLCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJzcXVpZ2dseSJ9fX1dLFsxMSwxLCJxIiwxXSxbMTAsOCwicSIsMV0sWzExLDksInEiLDFdLFsxNCwxNSwiPyIsMyx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH0sInN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFsxMywxMiwic3F1YXJlJyIsMSx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH19XSxbMjYsMjEsInEgKGlcXHdlZGdlICEgaykiLDIseyJzaG9ydGVuIjp7InNvdXJjZSI6MjAsInRhcmdldCI6MjB9fV0sWzI3LDIyLCJxKGlcXHZlZSBrKSIsMCx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH19XSxbMjAsMTMsImZpbGwiLDEseyJzaG9ydGVuIjp7InNvdXJjZSI6MjAsInRhcmdldCI6MjB9LCJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbMjMsMTIsImZpbGxeciIsMSx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH19XV0=

module _ {a : A} (p : a ≡ a) (q : a ≡ a) where
 top-fill : Square p (p ∙ q) refl q
 top-fill = comp-filler p q

 bot-fill : Square p (q ∙∙ p ∙∙ refl) (sym q) refl
 bot-fill j i = hfill
          (λ k → λ { (i = i0) → q (~ k)
                   ; (i = i1) → a
                   })
          (inS (p i)) j

 left-side : Square q refl refl (sym q)
 left-side k i = q (i ∧ ~ k)

 right-side : Square q refl q refl
 right-side k i = q (i ∨ k)

 sides : (i j k : I) → Partial _ A
 sides i j k (i = i0) = top-fill   k j
 sides i j k (i = i1) = bot-fill   k j
 sides i j k (j = i0) = left-side  k i
 sides i j k (j = i1) = right-side k i

 -- sides i j k = λ
 --   { (i = i0) → top-fill   k j
 --   ; (i = i1) → bot-fill   k j
 --   ; (j = i0) → left-side  k i
 --   ; (j = i1) → right-side k i
 --   }

 -- back-to-front : (q ∙∙ p ∙∙ refl) ≡ (refl ∙∙ p ∙∙ q)
 back-to-front :  (refl ∙∙ p ∙∙ q) ≡ (q ∙∙ p ∙∙ refl)
               → Square p p q q
 back-to-front sq i j = hcomp (λ k → sides i j (~ k)) (sq i j)
 -- back-to-front sq i j = hcomp (λ k → λ
 --   { (i = i0) → top-fill   (~ k) j
 --   ; (i = i1) → bot-fill   (~ k) j
 --   ; (j = i0) → left-side  (~ k) i
 --   ; (j = i1) → right-side (~ k) i
 --   })
 --   (sq i j)

 -- Version without the extra sides needed for reverse direction
 front-to-back' : Square p p q q
               → (refl ∙∙ p ∙∙ q) ≡ (q ∙∙ p ∙∙ refl)
 front-to-back' sq i j = hcomp (λ k → λ
   { (j = i0) → left-side  k i
   ; (j = i1) → right-side k i
   })
   (sq i j)

 front-to-back : Square p p q q
               → (refl ∙∙ p ∙∙ q) ≡ (q ∙∙ p ∙∙ refl)
 front-to-back sq i j = hcomp (sides i j) (sq i j)
 -- front-to-back sq i j = hcomp (λ k → λ
 --   { (i = i0) → top-fill   k j
 --   ; (i = i1) → bot-fill   k j
 --   ; (j = i0) → left-side  k i
 --   ; (j = i1) → right-side k i
 --   })
 --   (sq i j)
{-
λ i j →
  hcomp
  (λ { k (i = i0) → top-fill (~ k) j
     ; k (i = i1) → bot-fill (~ k) j
     ; k (j = i0) → left-side (~ k) i
     ; k (j = i1) → right-side (~ k) i
     })
  (hcomp
   (λ { k (i = i0) → top-fill k j
      ; k (i = i1) → bot-fill k j
      ; k (j = i0) → left-side k i
      ; k (j = i1) → right-side k i
      })
   (sq i j))
-}
 front-back-front : ∀ sq → back-to-front (front-to-back sq) ≡ sq
 front-back-front sq k i j = hcomp-inv-l (sides i j) (inS (sq i j)) (~ k)
 -- front-back-front sq k i j = hcomp-inv-l (sides i j) (inS (sq i j)) k

 back-front-back : ∀ sq → front-to-back (back-to-front sq) ≡ sq
 back-front-back sq k i j = hcomp-inv-l (λ l → sides i j (~ l)) (inS (sq i j)) (~ k)

-- hcomp-inv

comps-to-square : {a : A} (p : a ≡ a) (q : a ≡ a)
                → (q ∙∙ p ∙∙ refl) ≡ (refl ∙∙ p ∙∙ q)
                → Square p p q q
comps-to-square p q sq = back-to-front p q (sym sq)

from-square : Square line2' line2' line1' line1'
from-square = comps-to-square line2' line1' (sym (rotate line1' line2') ∙ square')
-- from-square = comps-to-square line2' line1' {!square' ∙ rotate line2' line1'!}

-- from-square i j = hcomp (λ
--   { k (i = i0) → comp-filler2 line1' line2' k j
--   ; k (i = i1) → {!comp-filler2 line1' line2' k j!}
--   ; k (j = i0) → {!!}
--   ; k (j = i1) → {!!}
--   }) (square' i j)

t2t' : Torus → Torus'
t2t' point = point
t2t' (line1 i) = line1' i
t2t' (line2 i) = line2' i
t2t' (square i j) = from-square i j


cong₂ : ∀ {C : (a : A) → (b : B a) → Type ℓ} →
        (f : (a : A) → (b : B a) → C a b) →
        (p : x ≡ y) →
        {u : B x} {v : B y} (q : PathP (λ i → B (p i)) u v) →
        PathP (λ i → C (p i) (q i)) (f x u) (f y v)
cong₂ f p q i = f (p i) (q i)

-- ap : (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
-- ap f p i = f (p i)

ap2 : {B : Type}
     (f : A → B)
     {x y z w : A}
     {p : x ≡ y} {q : z ≡ w}
     {r : x ≡ z} {s : y ≡ w}
    → Square p q r s
    → Square (ap f p) (ap f q) (ap f r) (ap f s)
ap2 f sq i j = f (sq i j)
-- ap2 f p i j = f (p i j)

-- apdd : {C : (a : A) → Type }
--      (f : (a : A) → C a)
--      {x y z w : A}
--      (p : x ≡ y) (q : z ≡ w)
--      (r : x ≡ z) (s : y ≡ w)
--    → (sq : Square p q r s)
--    → {!square!} -- PathP (λ i → P (p i)) (f x p) (f y)
-- apdd f p q r s sq i j = {!!} -- f (sq i j)
-- apd : (f : (a : A) → P a) {x y : A} → (p : x ≡ y) → PathP (λ i → P (p i)) (f x) (f y)
-- apd f p i = f (p i)

-- tt't-lem : ap2 (λ x → t'2t (t2t' x)) square ≡ square
-- tt't-lem =
--   ap2 (λ x → t'2t (t2t' x)) square ≡⟨⟩
--   ap2 t'2t (ap2 t2t' square) ≡⟨ {!!} ⟩
--   back-to-front line2 line1 (front-to-back line2 line1 square) ≡⟨ front-back-front line2 line1 square ⟩
--   square ∎
-- -- tt't-lem = {!front-back-front line2 line1 square!}

-- tt't : (t : Torus) → t'2t (t2t' t) ≡ t
-- tt't point = refl
-- tt't (line1 i) = refl
-- tt't (line2 i) = refl
-- tt't (square i j) k = tt't-lem k i j


data Torus'' : Type where
  point : Torus''
  line1'' : point ≡ point
  line2'' : point ≡ point
  square'' : (refl ∙∙ line2'' ∙∙ line1'') ≡ (line1'' ∙∙ line2'' ∙∙ refl)
  -- square'' : (line2'' ∙ line1'') ≡ (line1'' ∙∙ line2'' ∙∙ refl)

flipSquare : ∀ {ℓ} {A : Type ℓ}
  {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
  → Square a₀₋ a₁₋ a₋₀ a₋₁
  → Square a₋₀ a₋₁ a₀₋ a₁₋
flipSquare sq i j = sq j i

-- T-rec : {l : Level} {X : Type l} (x : X) (p : x ≡ x) (q : x ≡ x)
--    (s : (refl ∙∙ q ∙∙ p) ≡ (p ∙∙ q ∙∙ refl)) → Torus'' → X
-- T-rec x p q s point = x
-- T-rec x p q s (line1'' i) = p i
-- T-rec x p q s (line2'' i) = q i
-- T-rec x p q s (square'' i j) = {!(s i j)!}

data 𝟘 : Type where

-- T-equals : (a b : Torus'') → Type
-- T-equals  point           point         = ?
-- T-equals  point          (line1'' k)    = {!𝟘!}
-- T-equals  point          (line2'' k)    = {!𝟘!}
-- T-equals  point          (square'' k l) = {!𝟘!}
-- T-equals (line1'' i)      point         = {!𝟘!}
-- T-equals (line1'' i)     (line1'' k)    = {!!}
-- T-equals (line1'' i)     (line2'' k)    = {!𝟘!}
-- T-equals (line1'' i)     (square'' k l) = {!𝟘!}
-- T-equals (line2'' i)      point         = {!𝟘!}
-- T-equals (line2'' i)     (line1'' k)    = {!𝟘!}
-- T-equals (line2'' i)     (line2'' k)    = {!!}
-- T-equals (line2'' i)     (square'' k l) = {!𝟘!}
-- T-equals (square'' i j)   point         = {!𝟘!}
-- T-equals (square'' i j)  (line1'' k)    = {!𝟘!}
-- T-equals (square'' i j)  (line2'' k)    = {!𝟘!}
-- T-equals (square'' i j)  (square'' k l) = {!!}

Cube :
  {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
  {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
  {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
  (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
  {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
  {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
  {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
  (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
  {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
  (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
  {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
  (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
  (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
  (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
  → Type _
Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ =
  PathP (λ i → Square (a₋₀₋ i) (a₋₁₋ i) (a₋₋₀ i) (a₋₋₁ i)) a₀₋₋ a₁₋₋

-- flipSquare :
--   {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
--   {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
--   (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
--   → Square a₀₋ a₁₋ a₋₀ a₋₁
--   → Square a₋₀ a₋₁ a₀₋ a₁₋
-- flipSquare a₀₋ a₁₋ a₋₀ a₋₁ sq i j = sq j i

module _
  {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
  {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
  {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
  (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
  {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
  {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
  {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
  (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
  {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
  (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
  {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
  (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
  (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
  (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
  (cb : Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁)
  where
  flipCube : Cube (flipSquare a₋₀₋)
                  (flipSquare a₋₁₋)
                  (flipSquare a₋₋₀)
                  (flipSquare a₋₋₁)
                  a₀₋₋
                  a₁₋₋
  flipCube i j k = cb k i j
  flipCube2 : Cube (flipSquare a₀₋₋) (flipSquare a₁₋₋) a₋₋₀ a₋₋₁ a₋₀₋ a₋₁₋
  flipCube2 i j k = cb i k j
  flipCube3 : Cube (flipSquare a₀₋₋) (flipSquare a₁₋₋) a₋₋₀ a₋₋₁ a₋₀₋ a₋₁₋
  flipCube3 = {!!}

SquareP :
  (A : I → I → Type ℓ)
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
  {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
  (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
  → Type ℓ
SquareP A a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ i → PathP (λ j → A i j) (a₋₀ i) (a₋₁ i)) a₀₋ a₁₋

doubleCompPath-filler : (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
                      → PathP (λ j → p (~ j) ≡ r j) q (p ∙∙ q ∙∙ r)
doubleCompPath-filler p q r j i =
  hfill (λ j → λ { (i = i0) → p (~ j)
                 ; (i = i1) → r j })
        (inS (q i)) j

compPath-filler : (p : x ≡ y) (q : y ≡ z) → PathP (λ j → x ≡ q j) p (p ∙ q)
compPath-filler p q = doubleCompPath-filler refl p q

compPath-filler-l : (p : x ≡ y) (q : y ≡ z) → PathP (λ j → p (~ j) ≡ z) q (p ∙∙ q ∙∙ refl)
compPath-filler-l p q = doubleCompPath-filler p q refl

compPathP : ∀ {A : I → Type ℓ} {x : A i0} {y : A i1} {B_i1 : Type ℓ} {B : (A i1) ≡ B_i1} {z : B i1}
            → PathP A x y → PathP (λ i → B i) y z → PathP (λ j → ((λ i → A i) ∙ B) j) x z
compPathP {A = A} {x = x} {B = B} p q i =
  comp (λ j → compPath-filler (λ i → A i) B j i)
       (λ j → λ { (i = i0) → x ;
                  (i = i1) → q j })
       (p i)

compPathP'l : {B : A → Type ℓ'} {x' : B x} {y' : B y} {z' : B z} {p : x ≡ y} {q : y ≡ z}
              (P : PathP (λ i → B (p i)) x' y') (Q : PathP (λ i → B (q i)) y' z')
           → PathP (λ i → B ((p ∙∙ q ∙∙ refl) i)) x' z'
compPathP'l {B = B} {z' = z'} {p = p} {q = q} P Q i =
  comp (λ j → B (compPath-filler-l p q j i))
       (λ j → λ { (i = i0) → P (~ j)  ;
                  (i = i1) → z' })
       (Q i)

compPathP' : {B : A → Type ℓ'} {x' : B x} {y' : B y} {z' : B z} {p : x ≡ y} {q : y ≡ z}
             (P : PathP (λ i → B (p i)) x' y') (Q : PathP (λ i → B (q i)) y' z')
          → PathP (λ i → B ((p ∙ q) i)) x' z'
compPathP' {B = B} {x' = x'} {p = p} {q = q} P Q i =
  comp (λ j → B (compPath-filler p q j i))
       (λ j → λ { (i = i0) → x'  ;
                  (i = i1) → Q j })
       (P i)

-- compPathP'-filler : {B : A → Type ℓ'} {x' : B x} {y' : B y} {z' : B z} {p : x ≡ y} {q : y ≡ z}
--   (P : PathP (λ i → B (p i)) x' y') (Q : PathP (λ i → B (q i)) y' z')
--   → PathP (λ j → PathP (λ i → B (compPath-filler p q j i)) x' (Q j)) P (compPathP' {B = B} P Q)
-- compPathP'-filler {B = B} {x' = x'} {p = p} {q = q} P Q j i =
--   fill (λ j → B (compPath-filler p q j i))
--        (λ j → λ { (i = i0) → x'  ;
--                   (i = i1) → Q j })
--        (inS (P i))
--        j

-- transport is a special case of transp
transport : {A B : Type ℓ} → A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a


{-
         q
   x --------------- x
   |                 |
 p |  X (square i j) | p
   |                 |
   x --------------- x
         q
-}

T-rec : {l : Level} {X : Type l}
   (x : X )
   (p : x ≡ x)
   (q : x ≡ x)
   (s : PathP (λ i → (p i) ≡ (p i)) q q)
   → (t : Torus) → X
T-rec x p q s point = x
T-rec x p q s (line1 i) = p i
T-rec x p q s (line2 i) = q i
T-rec x p q s (square i j) = s i j


T-elim : {l : Level} {X : Torus → Type l}
   (x : X point)
   (p : PathP (λ i → X (line1 i)) x x)
   (q : PathP (λ i → X (line2 i)) x x)
   (s : PathP (λ i → PathP (λ j → X (square i j)) (p i) (p i)) q q)
   → (t : Torus) → X t
T-elim x p q s point = x
T-elim x p q s (line1 i) = p i
T-elim x p q s (line2 i) = q i
T-elim x p q s (square i j) = s i j

T-elim' : {l : Level} {X : Torus'' → Type l}
   (x : X point)
   (p : PathP (λ i → X (line1'' i)) x x)
   (q : PathP (λ i → X (line2'' i)) x x)
   (s : SquareP (λ i j → X (square'' i j))
        (compPathP' {B = X} q p)
        (compPathP'l {B = X} p q)
        (refl {x = x})
        (refl {x = x}))
   -- (s : PathP (λ i → PathP (λ j → X (square'' i j)) x x)
   --      (compPathP' {B = X} q p)
   --      (compPathP'l {B = X} p q))
   -- (s : PathP (λ i → {!!}) (refl ∙∙ {!!} ∙∙ {!!}) ({!!} ∙∙ {!!} ∙∙ refl))
   -- (s : PathP (λ i → ?) (refl ∙∙ q ∙∙ p) (p ∙∙ q ∙∙ refl))
   -- (s : (refl ∙∙ q ∙∙ p) ≡ (p ∙∙ q ∙∙ refl))
   → (t : Torus'') → X t
T-elim' x p q s point = x
T-elim' x p q s (line1'' i) = p i
T-elim' x p q s (line2'' i) = q i
T-elim' x p q s (square'' i j) = s i j

module _  (f : Torus'' → Torus'')
          (eqpt : f point ≡ point)
          (eqln1 : PathP (λ i → f (line1'' i) ≡ line1'' i) eqpt eqpt)
          (eqln2 : PathP (λ i → f (line2'' i) ≡ line2'' i) eqpt eqpt)
          (eqsq : PathP
            (λ i → PathP (λ j → f (square'' i j) ≡ square'' i j) eqpt eqpt)
            (compPathP' {B = λ x → f x ≡ x} eqln2 eqln1)
            (compPathP'l {B = λ x → f x ≡ x} eqln1 eqln2)
          )
          -- (eqln1 : Square (ap f line1'') line1'' eqpt eqpt)
          -- (eqln2 : Square (ap f line2'') line2'' eqpt eqpt)
          -- (eqsq  : SquareP (λ i j → f (square'' i j) ≡ square'' i j)
          --          {{!!}} {{!!}} {!eqpt!}
          --          {{!!}} {{!!}} {!!}
          --          {!!} {!!})
  where
  T-equals : (a : Torus'') → f a ≡ a
  T-equals = T-elim' eqpt eqln1 eqln2 eqsq
  -- T-equals point = eqpt
  -- T-equals (line1'' i) k = eqln1 k i
  -- T-equals (line2'' i) k = eqln2 k i
  -- T-equals (square'' i j) k = {!eqsq k i j!} -- eqsq i j

-- T-elim : {l : Level} {X : Torus'' → Type l}
--    (comp-distr :
--      {a b c d : Torus''}
--      {p : a ≡ b}
--      {q : b ≡ c}
--      {r : c ≡ d}
--      {xa : X a}
--      {xb : X b}
--      {xc : X c}
--      {xd : X d}
--      (xp : PathP (λ i → X (p i)) xa xb)
--      (xq : PathP (λ i → X (q i)) xb xc)
--      (xr : PathP (λ i → X (r i)) xc xd)
--      → PathP (λ i → X ((p ∙∙ q ∙∙ r) i)) xa xd
--      )
--    (x : X point)
--    (p : PathP (λ i → X (line1'' i)) x x)
--    (q : PathP (λ i → X (line2'' i)) x x)
--    (s : PathP (λ i → PathP (λ j → X (square'' i j)) x x)
--         (comp-distr (λ _ → x) q p)
--         (comp-distr p q (λ _ → x)))
--    -- (s : PathP (λ i → {!!}) (refl ∙∙ {!!} ∙∙ {!!}) ({!!} ∙∙ {!!} ∙∙ refl))
--    -- (s : PathP (λ i → ?) (refl ∙∙ q ∙∙ p) (p ∙∙ q ∙∙ refl))
--    -- (s : (refl ∙∙ q ∙∙ p) ≡ (p ∙∙ q ∙∙ refl))
--    → (t : Torus'') → X t
-- T-elim cd x p q s point = x
-- T-elim cd x p q s (line1'' i) = p i
-- T-elim cd x p q s (line2'' i) = q i
-- T-elim cd x p q s (square'' i j) = {!s i j!} -- s i j

-- T-elim x p q s point = x
-- T-elim x p q s (line1'' i) = p i
-- T-elim x p q s (line2'' i) = q i
-- T-elim x p q s (square'' i j) = {!(s i j)!}

torus''eq : Torus'' ≃ Torus
torus''eq = isoToEquiv (iso to fro toFro froTo)
  where
  to : Torus'' → Torus
  to point = point
  to (line1'' i) = line1 i
  to (line2'' i) = line2 i
  to (square'' i j) = front-to-back line2 line1 square i j

  fro : Torus → Torus''
  fro point = point
  fro (line1 i) = line1'' i
  fro (line2 i) = line2'' i
  fro (square i j) = back-to-front line2'' line1'' square'' i j

  -- -- goal : (i j : I) → hcomp (λ k o → to (sides line2'' line1'' i j (~ k) o))
  -- --       (front-to-back line2 line1 square i j)
  -- --       ≡ square i j
  -- goal : PathP
  --   (λ i → PathP (λ j → to (fro (square i j)) ≡ square i j) refl refl)
  --   (λ i j → line2 i) (λ i j → line2 i)
  -- goal i j = {!fro (square i j)!}
  -- -- goal1 : (i j : I) → to (fro (square i j)) ≡ square i j
  -- goal1 : (i : I) → apd to (apd fro (square i)) ≡ square i
  -- goal1 = {!square!}

  -- -- goal2 : PathP (λ i → apd to (apd fro (square i)) ≡ square i) refl refl
  -- -- goal2 : PathP (λ i → ap (λ x → to (fro x)) (square i) ≡ square i) refl refl
  -- -- goal2 : PathP (λ i → cong₂ {B = λ a → a ≡ a } (λ a b → {!to (fro b)!}) line1 square i ≡ {!!}) refl refl
  -- goal2 : PathP (λ i → ap2 (λ x → to (fro x)) square i ≡ square i) refl refl
  -- goal2 = {!apd fro (square i)!}

  known : back-to-front line2 line1 (front-to-back line2 line1 square) ≡
            square
  known = front-back-front line2 line1 square

  goal3 : ap2 (λ x → to (fro x)) square ≡ square
  goal3 =
    ap2 (λ x → to (fro x)) square ≡⟨⟩
    -- (λ i j → hcomp (λ k o → to (sides line2'' line1'' i j (~ k) o))
    --                (front-to-back line2 line1 square i j)
    --         ) ≡⟨⟩
    -- (λ i j → hcomp (λ
    --            {k (i = i0) → to (sides line2'' line1'' i j (~ k) 1=1)
    --            ;k (i = i1) → to (sides line2'' line1'' i j (~ k) 1=1)
    --            ;k (j = i0) → to (sides line2'' line1'' i j (~ k) 1=1)
    --            ;k (j = i1) → to (sides line2'' line1'' i j (~ k) 1=1)
    --            }) (front-to-back line2 line1 square i j)
    --         ) ≡⟨⟩
    -- (λ i j → hcomp (λ
    --            {k (i = i0) → to (top-fill line2'' line1'' (~ k) j)
    --            ;k (i = i1) → to (bot-fill line2'' line1'' (~ k) j)
    --            ;k (j = i0) → to (left-side line2'' line1'' (~ k) i)
    --            ;k (j = i1) → to (right-side line2'' line1'' (~ k) i)
    --            }) (front-to-back line2 line1 square i j)
    --         ) ≡⟨⟩
    -- (λ i j → hcomp (λ
    --            {k (i = i0) → to (top-fill line2'' line1'' (~ k) j)
    --            ;k (i = i1) → to (bot-fill line2'' line1'' (~ k) j)
    --            ;k (j = i0) → line1 (i ∧ k)
    --            ;k (j = i1) → line1 (i ∨ ~ k)
    --            }) (front-to-back line2 line1 square i j)
    --         ) ≡⟨⟩
    -- (λ i j → hcomp (λ
    --            {k (i = i0) →
    --              hcomp
    --               (λ { l (j = i0) → to point
    --                  ; l (j = i1) → to (line1'' (~ k ∧ l))
    --                  ; l (k = i1) → to (line2'' j)
    --                  })
    --               (line2 j)
    --            ;k (i = i1) → to (bot-fill line2'' line1'' (~ k) j)
    --            ;k (j = i0) → line1 (i ∧ k)
    --            ;k (j = i1) → line1 (i ∨ ~ k)
    --            }) (front-to-back line2 line1 square i j)
    --         ) ≡⟨ refl ⟩
    back-to-front line2 line1 (front-to-back line2 line1 square) ≡⟨ known ⟩
    square ∎

  toFro : (b : Torus) → to (fro b) ≡ b
  toFro point = refl
  toFro (line1 i) = refl
  toFro (line2 i) = refl
  toFro (square i j) k = front-back-front line2 line1 square k i j
  -- toFro (square i j) k = goal3 k i j
  -- toFro (square i j) = goal1 j i
    -- where
      -- front-back-front line2 line1 square

  -- toFro (square i j) = {!front-back-front line2 line1 square!}
  -- toFro (square i j) = {!back-front-back line2 line1!}
  -- toFro (square i j) = {!front-back-front line1 line2 square i j!}

  known-froTo : front-to-back line2'' line1''
                  (back-to-front line2'' line1'' square'')
                  ≡ square''
  known-froTo = back-front-back line2'' line1'' square''

  goal-froTo : ap2 (λ x → fro (to x)) square'' ≡ square''
  goal-froTo = known-froTo

  postulate
    goal-froTo-sad : PathP
      (λ i → PathP (λ j → fro (to (square'' i j)) ≡ square'' i j) refl refl)
      (λ i → refl)
      (λ i → refl)
  -- goal-froTo-sad = {!!}

    -- goal-froTo-sadder :  PathP
    --   (λ i →
    --      PathP
    --      (λ j →
    --         hcomp (λ i₁ o → fro (sides line2 line1 i j i₁ o))
    --         (back-to-front line2'' line1'' square'' i j)
    --         ≡ square'' i j)
    --      refl refl)
    --   (compPathP' {B = λ s → fro (to s) ≡ s} (λ i → refl) (λ i → refl))
    --   (compPathP'l {B = λ s → fro (to s) ≡ s} (λ i → {!refl!}) (λ i → refl))
  goal-froTo-sadder :  PathP
    (λ i →
        PathP
        (λ j → fro (to (square'' i j)) ≡ square'' i j)
        refl refl)
    (compPathP' {B = λ s → fro (to s) ≡ s} (λ i → refl) (λ i → refl))
    (compPathP'l {B = λ s → fro (to s) ≡ s} (λ i j → line1'' i) (λ i j → line2'' i))
  goal-froTo-sadder = {!!}


  froTo : (s : Torus'') → fro (to s) ≡ s
  -- froTo = T-equals (λ x → fro (to x)) refl (λ i → refl) (λ i  → refl)
  froTo = T-equals (λ x → fro (to x)) refl (λ i j → line1'' i) (λ i j → line2'' i)
                 goal-froTo-sadder
  -- froTo point = refl
  -- froTo (line1'' i) = refl
  -- froTo (line2'' i) = refl
  -- froTo (square'' i j) = {!goal-froTo-sad i j!}
  -- froTo (square'' i j) = goal-froTo-sad i j
  -- froTo (square'' i j) k = goal-froTo k i j
  -- froTo (square'' i j) = {!back-front-back line2'' line1'' square'' k i j!}


torus''-'eq : Torus'' ≃ Torus'
torus''-'eq = isoToEquiv (iso to fro toFro froTo)
  where
  to : Torus'' → Torus'
  to point = point
  to (line1'' i) = line2' i
  to (line2'' i) = line1' i
  to (square'' i j) = (square' ∙ rotate line2' line1') i j

  fro : Torus' → Torus''
  fro point = point
  fro (line1' i) = line2'' i
  fro (line2' i) = line1'' i
  fro (square' i j) = (square'' ∙ sym (rotate line1'' line2'')) i j

  goal3 : ap2 (λ x → to (fro x)) square' ≡ square'
  goal3 = {!!}
    -- ap2 (λ x → to (fro x)) square ≡⟨⟩
    -- back-to-front line2 line1 (front-to-back line2 line1 square) ≡⟨ known ⟩
    -- square ∎

  -- foo : PathP (λ i → line1' i ≡ line1' i) refl refl
  foo : Square refl refl line1' line1'
  foo = flipSquare (refl {x = line1'})
  -- foo i = refl {x = line1' i }
  -- bar : Square line1' line1' refl refl
  bar : line1' ≡ line1'
  bar = flipSquare foo

  -- goal-toFro-sad4 : transp
  --     (λ i →
  --        flipSquare (compPathP' {B = λ x → x ≡ x} (λ i₁ → refl) (λ i₁ → refl)) i ≡
  --        flipSquare (compPathP' {B = λ x → x ≡ x} (λ i₁ j → line2' i₁) (λ i₁ j → line1' i₁))
  --        i)
  --     i0 (ap2 (λ x → to (fro x)) square')
  --     ≡ ap2 (λ x → to (fro x)) square'
  -- goal-toFro-sad4 = {!!}

  goal-toFro-sad3 : Square
    -- {a₀₀ = line1' ∙ line2'}
    -- {line2' ∙ line1'}
    (ap2 (λ x → to (fro x)) square')
    -- {line1' ∙ line2'} {line2' ∙ line1'}
    square'
    (flipSquare (compPathP' {B = λ s → s ≡ s} (λ i → refl) (λ i → refl)))
    (flipSquare (compPathP' {B = λ s → s ≡ s} (λ i j → line2' i) (λ i j → line1' i)))
  goal-toFro-sad3 = toPathP ({!!} ∙ goal3)
  goal-toFro-sad2 : Square
    (flipSquare (compPathP' {B = λ s → to (fro s) ≡ s} (λ i → refl {x = line1' i}) (λ i → refl {x = line2' i})))
    (flipSquare (compPathP' {B = λ s → to (fro s) ≡ s} (λ i j → line2' i) (λ i j → line1' i)))
    (ap2 (λ x → to (fro x)) square')
    square'
  goal-toFro-sad2 = flipSquare goal-toFro-sad3
  -- goal-toFro-sad2 = {!Square!}
  goal-toFro-sad : Cube
    (flipSquare (compPathP' {B = λ s → to (fro s) ≡ s} (λ i → refl) (λ i → refl)))
    (flipSquare (compPathP' {B = λ s → to (fro s) ≡ s} (λ i j → line2' i) (λ i j → line1' i)))
    (ap2 (λ x → to (fro x)) square')
    square'
    refl
    refl
  goal-toFro-sad = goal-toFro-sad2

  -- goal-toFro-sadder : SquareP
  --   (λ i j → to (fro (square' i j)) ≡ square' i j)
  --   (compPathP' {B = λ s → to (fro s) ≡ s} (λ i → refl) (λ i → refl))
  --   (compPathP' {B = λ s → to (fro s) ≡ s} (λ i j → line2' i) (λ i j → line1' i))
  --   refl refl
  -- goal-toFro-sadder :  PathP
  --   (λ i →
  --       Square refl refl
  --       (ap2 (λ x → to (fro x)) square' i)
  --       (square' i))
  --   (compPathP' {B = λ s → to (fro s) ≡ s} (λ i → refl) (λ i → refl))
  --   (compPathP' {B = λ s → to (fro s) ≡ s} (λ i j → line2' i) (λ i j → line1' i))
  goal-toFro-sadder : Cube
    (compPathP' {B = λ s → to (fro s) ≡ s} (λ i → refl) (λ i → refl))
    (compPathP' {B = λ s → to (fro s) ≡ s} (λ i j → line2' i) (λ i j → line1' i))
    (refl {x = refl {x = to (fro (((λ i → line1' i) ∙ (λ i → line2' i)) i0))}})
    (refl {x = refl {x = to (fro (((λ i → line1' i) ∙ (λ i → line2' i)) i1))}})
    (ap2 (λ x → to (fro x)) square')
    square'
  goal-toFro-sadder = flipCube2 _ _ _ _ _ _ goal-toFro-sad
  -- goal-toFro-sadder i j k = {!goal-toFro-sad j i k!}

  -- TODO: Try to rotate the cube to get rid of refl. I think they should be last for that

  toFro : (b : Torus') → to (fro b) ≡ b
  toFro point = refl
  toFro (line1' i) = refl
  toFro (line2' i) = refl
  toFro (square' i j)  = goal-toFro-sadder i j
  -- toFro (square' i j) k = goal3 k i j

  goal-froTo : ap2 (λ x → fro (to x)) square'' ≡ square''
  goal-froTo = {!!}

  goal-froTo-sadder :  PathP
    (λ i →
        PathP
        (λ j → fro (to (square'' i j)) ≡ square'' i j)
        refl refl)
    (compPathP' {B = λ s → fro (to s) ≡ s} (λ i → refl) (λ i → refl))
    (compPathP'l {B = λ s → fro (to s) ≡ s} (λ i j → line1'' i) (λ i j → line2'' i))
  goal-froTo-sadder = {!!}


  froTo : (s : Torus'') → fro (to s) ≡ s
  -- froTo = T-equals (λ x → fro (to x)) refl (λ i → refl) (λ i  → refl)
  froTo = T-equals (λ x → fro (to x)) refl (λ i j → line1'' i) (λ i j → line2'' i)
                 goal-froTo-sadder
  -- froTo point = refl
  -- froTo (line1'' i) = refl
  -- froTo (line2'' i) = refl
  -- froTo (square'' i j) = {!goal-froTo-sad i j!}
  -- froTo (square'' i j) = goal-froTo-sad i j
  -- froTo (square'' i j) k = goal-froTo k i j
  -- froTo (square'' i j) = {!back-front-back line2'' line1'' square'' k i j!}


```
