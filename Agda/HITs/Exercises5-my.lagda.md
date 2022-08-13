
```agda
{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

open import new-prelude
open import Lecture5-notes
open import Solutions4 using (ap-!; to-from-base; to-from-loop; s2c ; b2c ; c2s; susp-func)

module Exercises5-my where
```

# 1 point and 2 point circles are equivalent (⋆)

In lecture, we defined maps between the one point circle (S1) and the
two point circle (Circle2) and checked that the round-trip on Circle2 is
the identity.

Prove that the round-trip on S1 is the identity (use to-from-base
and to-from-loop from the Lecture 4 exercises), and package all of
these items up as an equivalence S1 ≃ Circle2.

```agda

  -- to : S1 → Circle2
  -- to = S1-rec north (east ∙ ! west)

  -- from : Circle2 → S1
  -- from = Circle2-rec base base (refl base) loop

  -- from-to-north : to (from north) ≡ north
  -- from-to-north = refl _

  -- from-to-south : to (from south) ≡ south
  -- from-to-south = west

  -- from-to-west : ap to (ap from west) ∙ from-to-south ≡ west
  -- from-to-west = ap to (ap from west) ∙ west ≡⟨ ap (\ H → ap to H ∙ west) (Circle2-rec-west _ _ _ _) ⟩
  --                 ap to (refl base) ∙ west    ≡⟨ ∙unit-l west ⟩
  --                 west ∎

  -- from-to-east : ap to (ap from east) ∙ from-to-south ≡ east
  -- from-to-east = ap to (ap from east) ∙ west ≡⟨ ap (\ H → ap to H ∙ west) (Circle2-rec-east _ _ _ _) ⟩
  --                ap to loop ∙ west           ≡⟨ ap (\ H → H ∙ west) (S1-rec-loop _ _) ⟩
  --                east ∙ ! west ∙ west        ≡⟨ ! (∙assoc _ (! west) west) ⟩
  --                east ∙ (! west ∙ west)      ≡⟨ ap (\ H → east ∙ H) (!-inv-l west) ⟩
  --                east ∎

from-to-loop : refl _ ∙ ap from (ap to loop) ≡ loop
from-to-loop =
    (refl _) ∙ (ap from (ap to loop))  ≡⟨ ∙unit-l _ ⟩
    ap from (ap to loop)               ≡⟨ ap (ap from) (S1-rec-loop _ _) ⟩
    ap from (east ∙ ! west)            ≡⟨ ap-∙ east (! west) ⟩
    ap from east ∙ ap from (! west)    ≡⟨ ap₂ _∙_
                                        (Circle2-rec-east _ _ _ _)
                                        (ap-! _) ⟩
    loop ∙ ! (ap from west) ≡⟨ ap (λ p → loop ∙ ! p) (Circle2-rec-west _ _ _ _) ⟩
    loop ∎

to-from : (x : S1) → from (to x) ≡ x
to-from = S1-elim (λ z → from (to z) ≡ z) (refl _)
  (PathOver-roundtrip≡ from to loop from-to-loop)

circles-equivalent : S1 ≃ Circle2
circles-equivalent = Equivalence to (Inverse from to-from from from-to)
```

# Reversing the circle (⋆⋆)

Define a map S1 → S1 that "reverses the orientation of the circle",
i.e. sends loop to ! loop.

```agda
rev : S1 → S1
rev = S1-rec base (! loop)
```

Prove that rev is an equivalence.  Hint: you will need to state and prove
one new generalized "path algebra" lemma and to use one of the lemmas from
the "Functions are group homomorphism" section of Lecture 4's exercises.
```agda

-- rev-rev-lemma :
--   {A : Type}
--   {f : A → A}
--   {a b : A}
--   {l : f (f a) ≡ a}
--   {r : f (f b) ≡ b}
--   (p : a ≡ b)→
--   {!ap f (ap f)!} →
--   PathOver (λ s → f (f s) ≡ s) p
--                 l r
-- rev-rev-lemma = {!!}

!! : {A : Type} {a b : A} (p : a ≡ b) → ! (! p) ≡ p
!! (refl _) = refl _

ap-rev-rev : ! (refl (rev (rev base))) ∙
             (ap rev (ap rev loop) ∙ refl (rev (rev base)))
             ≡ loop
ap-rev-rev =
    ! (refl _) ∙
      (ap rev (ap rev loop) ∙ refl (rev (rev base))) ≡⟨ refl _ ⟩
    refl _ ∙ ap rev (ap rev loop) ≡⟨ ∙unit-l _ ⟩
    ap rev (ap rev loop) ≡⟨ ap (ap rev) (S1-rec-loop _ _) ⟩
    ap rev (! loop)      ≡⟨ ap-! _ ⟩
    ! (ap rev (loop))    ≡⟨ ap ! (S1-rec-loop _ _) ⟩
    ! (! (loop))         ≡⟨ !! loop ⟩
    loop ∎

    -- ? ≡⟨ ? ⟩
    -- ? ∎

rev-rev : (s : S1) → rev (rev s) ≡ s
rev-rev = S1-elim (λ s → rev (rev s) ≡ s) (refl _)
  (PathOver-roundtrip≡ rev rev loop ap-rev-rev)
  -- (rev-rev-lemma _ _ loop {!!})

rev-equiv : is-equiv rev
rev-equiv = Inverse rev rev-rev rev rev-rev
```


# Circles to torus (⋆⋆)

In the Lecture 4 exercises, you defined a map from the Torus to S1 × S1.
In this problem, you will define a converse map.  The goal is for these
two maps to be part of an equivalence, but we won't prove that in these
exercises.

You will need to state and prove a lemma characterizing a path over a
path in a path fibration.  Then, to define the map S1 × S1 → Torus, you
will want to curry it and use S1-rec and/or S1-elim on each circle.

```agda
PathOver-path≡ : ∀ {A B : Type} {g : A → B} {f : A → B}
                          {a a' : A} {p : a ≡ a'}
                          {q : (f a) ≡ (g a)}
                          {r : (f a') ≡ (g a')}
                        → ap f p ∙ r ≡ q ∙ ap g p
                        → q ≡ r [ (\ x → (f x) ≡ (g x)) ↓ p ]
PathOver-path≡ {A} {B} {g} {f} {a} {.a} {refl .a} {._} {r} h =
  path-to-pathover (
    _ ≡⟨ ! h ⟩
    refl (f a) ∙ r ≡⟨ ∙unit-l _ ⟩
    r ∎)

sT-lemma : ap (λ z → S1-rec baseT pT z) loop ∙ qT ≡
           qT ∙ ap (λ z → S1-rec baseT pT z) loop
sT-lemma =
    ap (λ z → S1-rec baseT pT z) loop ∙ qT ≡⟨ ap (_∙ qT) (S1-rec-loop _ _) ⟩
    pT ∙ qT ≡⟨ sT ⟩
    qT ∙ pT ≡⟨ ap (qT ∙_) (! (S1-rec-loop _ _)) ⟩
    qT ∙ ap (λ z → S1-rec baseT pT z) loop ∎

circles-to-torus : S1 → (S1 → Torus)
circles-to-torus = S1-rec (S1-rec baseT pT)
   (λ≡ (S1-elim (λ z → S1-rec baseT pT z ≡ S1-rec baseT pT z)
        qT
        ( PathOver-path≡ sT-lemma)))
        -- ( PathOver-path≡ (ap (S1-rec baseT) sT))))

circles-to-torus' : S1 × S1 → Torus
circles-to-torus' (x , y) = circles-to-torus x y
```

**Below are some "extra credit" exercise if you want more to do.  These
are (even more) optional: nothing in the next lecture will depend on you
understanding them.  The next section (H space) is harder code but uses
only the circle, whereas the following sections are a bit easier code
but require understanding the suspension type, which we haven't talked
about too much yet.**

# H space

The multiplication operation on the circle discussed in lecture is part
of what is called an "H space" structure on the circle.  One part of
this structure is that the circle's basepoint is a unit element for
multiplication.

(⋆) Show that base is a left unit.
```agda
mult-unit-l : (y : S1) → mult base y ≡ y
mult-unit-l y = refl _
    -- mult base y ≡⟨ {!S1-rec-base (\ x → x) (λ≡ (S1-elim _ loop (PathOver-path-loop (refl _))))!} ⟩
    -- {!mult !} ≡⟨ refl _ ⟩
    -- y ∎
    -- mult base y ≡⟨ S1-rec-base _ _ ⟩
    -- y ∎
```

(⋆) Because we'll need it in a second, show that ap distributes over
function composition:
```agda
ap-∘ : ∀ {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3}
       (f : A → B) (g : B → C)
       {a a' : A}
       (p : a ≡ a')
     → ap (g ∘ f) p ≡ ap g (ap f p)
ap-∘ f g (refl _) = refl _
```

(⋆⋆) Suppose we have a curried function f : S1 → A → B.  Under the
equivalence between paths in S1 × A and pairs of paths discussed in
Lecture 3, we can then "apply" (the uncurried version of) f to a pair of
paths (p : x ≡ y [ S1 ] , q : z ≡ w [ A ]) to get a path (f x z ≡ f y w
[ B ]).  In the special case where q is reflexivity on a, this
application to p and q can be simplified to ap (\ x → f x a) p : f x a ≡
f y a [ B ].

Now, suppose that f is defined by circle recursion.  We would expect
some kind of reduction for applying f to the pair of paths (loop , q) ---
i.e. we should have reductions for *nested* pattern matching on HITs.
In the case where q is reflexivity, applying f to the pair (loop , refl)
can reduce like this:
```agda
S1-rec-loop-1 : ∀ {A B : Type} {f : A → B} {h : f ≡ f} {a : A}
                     →  ap (\ x → S1-rec f h x a) loop ≡ app≡ h a
S1-rec-loop-1 {A}{B}{f}{h}{a} =
    ap (λ x → S1-rec f h x a) loop                ≡⟨ refl _ ⟩
    ap ((λ f → f a) ∘ λ x → S1-rec f h x) loop    ≡⟨ ap-∘ (λ x → S1-rec f h x) (λ f₁ → f₁ a) loop ⟩
    ap (λ f → f a) (ap (λ x → S1-rec f h x) loop) ≡⟨ refl _  ⟩
    app≡ (ap (λ x → S1-rec f h x) loop) a         ≡⟨ ap (λ p → app≡ p a) (S1-rec-loop _ _) ⟩
    app≡ h a                                      ∎
```
Prove this reduction using ap-∘ and the reduction rule for S1-rec on the loop.

(⋆⋆⋆) Show that base is a right unit for multiplication.  You will need
a slightly different path-over lemma than before.

```agda
PathOver-endo≡ : ∀ {A : Type} {f : A → A}
                 {a a' : A} {p : a ≡ a'}
                 {q : (f a) ≡ a}
                 {r : (f a') ≡ a'}
               → q ∙ p ≡ (ap f p) ∙ r
               → q ≡ r [ (\ x → f x ≡ x) ↓ p ]
PathOver-endo≡ {p = (refl _)} {q = q} {r} h = path-to-pathover (h ∙ (∙unit-l _) )

mult-unit-r-lemma : ap (λ z → mult z base) loop ≡ loop
mult-unit-r-lemma =
    ap (λ z → mult z base) loop  ≡⟨ S1-rec-loop-1 ⟩
    app≡ (λ≡ _) base ≡⟨ app≡ (λ≡βinv _) base ⟩
    S1-elim _ loop (PathOver-path-loop (refl _)) base ≡⟨ refl _ ⟩
    loop ∎

mult-unit-r : (x : S1) → mult x base ≡ x
mult-unit-r = S1-elim (λ z → mult z base ≡ z) (refl _)
   (PathOver-endo≡ (∙unit-l _ ∙ ! mult-unit-r-lemma))
```

# Suspensions and the 2-point circle

(⋆) Postulate the computation rules for the non-dependent susp-rec and
declare rewrites for the reduction rules on the point constructors.
```agda
postulate
  Susp-rec-north : {l : Level} {A : Type} {X : Type l}
                 (n : X) (s : X) (m : A → n ≡ s)
                 → Susp-rec n s m northS ≡ n
  Susp-rec-south : {l : Level} {A : Type} {X : Type l}
                   (n : X) (s : X) (m : A → n ≡ s)
                   → Susp-rec n s m southS ≡ s
{-# REWRITE Susp-rec-north #-}
{-# REWRITE Susp-rec-south #-}
postulate
  Susp-rec-merid : {l : Level} {A : Type} {X : Type l}
                   (n : X) (s : X) (m : A → n ≡ s)
                 → (x : A) → ap (Susp-rec n s m) (merid x) ≡ m x
```

(⋆) Postulate the dependent elimination rule for suspensions:

```agda
postulate
  Susp-elim : {l : Level} {A : Type} (P : Susp A → Type l)
            → (n : P northS)
            → (s : P southS)
            → (m : (a : A) → n ≡ s [ P ↓ merid a ])
            → (x : Susp A) → P x
```

(⋆⋆) Show that the maps s2c and c2s from the Lecture 4 exercises are mutually inverse:

```agda
c2s2c-west : ap s2c (ap c2s west) ≡ west
c2s2c-west =
    ap s2c (ap c2s west) ≡⟨ ap (ap s2c) (Circle2-rec-west _ _ _ _) ⟩
    ap s2c (merid true) ≡⟨ Susp-rec-merid _ _ _ true ⟩
    west ∎


c2s2c-east : ap s2c (ap c2s east) ≡ east
c2s2c-east =
    ap s2c (ap c2s east) ≡⟨ ap (ap s2c) (Circle2-rec-east _ _ _ _) ⟩
    ap s2c (merid false) ≡⟨ Susp-rec-merid _ _ _ false ⟩
    east ∎

c2s2c : (x : Circle2) → s2c (c2s x) ≡ x
c2s2c = Circle2-elim _ (refl _) (refl _)
  (PathOver-roundtrip≡ s2c c2s west ((∙unit-l _) ∙ c2s2c-west))
  (PathOver-roundtrip≡ s2c c2s east ((∙unit-l _) ∙ c2s2c-east))

b2c2s : ∀ a → ap c2s (b2c a) ≡ merid a
b2c2s true = Circle2-rec-west _ _ _ _
b2c2s false = Circle2-rec-east _ _ _ _

s2c2s-merid : ∀ a → ap c2s (ap s2c (merid a)) ≡ merid a
s2c2s-merid a =
    ap c2s (ap s2c (merid a)) ≡⟨ ap (ap c2s) (Susp-rec-merid _ _ _ _) ⟩
    ap c2s (b2c a) ≡⟨ b2c2s a ⟩
    merid a ∎

s2c2s : (x : Susp Bool) → c2s (s2c x) ≡ x
s2c2s = Susp-elim (λ z → c2s (s2c z) ≡ z) (refl _) (refl _)
  (λ a → PathOver-roundtrip≡ c2s s2c (merid a) ((∙unit-l _) ∙ s2c2s-merid a))
```

(⋆) Conclude that Circle2 is equivalent to Susp Bool:

```agda
Circle2-Susp-Bool : Circle2 ≃ Susp Bool
Circle2-Susp-Bool = Equivalence c2s (Inverse s2c c2s2c s2c s2c2s)
```

# Functoriality of suspension (⋆⋆)

In the Lecture 4 exercises, we defined functoriality for the suspension
type, which given a function X → Y gives a function Σ X → Σ Y.  Show
that this operation is functorial, meaning that it preserves identity
and composition of functions:
```agda
susp-func-id-merid : ∀ {X} (a : X) → ap (λ z → susp-func id z) (merid a) ≡ merid a
susp-func-id-merid = Susp-rec-merid _ _ _

susp-func-id : ∀ {X : Type} → susp-func {X} id ∼ id
susp-func-id = Susp-elim (λ z → susp-func id z ≡ z) (refl _) (refl _)
    λ a → PathOver-endo≡ (∙unit-l _ ∙ ! (susp-func-id-merid a))


susp-func-∘-north : ∀ {X} {Y} {Z} (f : X → Y) (g : Y → Z) →
                    susp-func (g ∘ f) northS ≡ (susp-func g ∘ susp-func f) northS
susp-func-∘-north f g =
    susp-func (g ∘ f) northS         ≡⟨ refl _ ⟩ -- Susp-rec-north _ _ _
    northS                           ≡⟨ refl _ ⟩ -- ! (Susp-rec-north _ _ _)
    susp-func g northS               ≡⟨ refl _ ⟩ -- ! (ap (susp-func g) (Susp-rec-north _ _ _))
    susp-func g (susp-func f northS) ∎

susp-func-∘-south : ∀ {X} {Y} {Z} (f : X → Y) (g : Y → Z) →
                    susp-func (g ∘ f) southS ≡ (susp-func g ∘ susp-func f) southS
susp-func-∘-south f g =
    susp-func (g ∘ f) southS ≡⟨ refl _ ⟩ -- Thanks to the rewrite rule, this is just refl
    (susp-func g ∘ susp-func f) southS ∎

susp-func-∘-merid : ∀ {X} {Y} {Z} (f : X → Y) (g : Y → Z) (a : X) →
                    PathOver
                    (λ z → susp-func (g ∘ f) z ≡ (susp-func g ∘ susp-func f) z)
                    (merid a) (susp-func-∘-north f g) (susp-func-∘-south f g)
susp-func-∘-merid f g a = PathOver-path≡ (
    ap (λ z → susp-func (g ∘ f) z) (merid a) ∙ susp-func-∘-south f g ≡⟨ refl _ ⟩
    ap (susp-func (g ∘ f)) (merid a)               ≡⟨ Susp-rec-merid _ _ _ a ⟩
    merid (g (f a))                                ≡⟨ ! (Susp-rec-merid _ _ _ (f a)) ⟩
    ap (susp-func g) (merid (f a))                 ≡⟨ ap (ap (susp-func g)) (! (Susp-rec-merid _ _ _ a)) ⟩
    ap (susp-func g) (ap (susp-func f) (merid a))  ≡⟨ ! (ap-∘ (susp-func f) (susp-func g) (merid a)) ⟩
    ap (susp-func g ∘ susp-func f) (merid a)       ≡⟨ ! (∙unit-l _) ⟩
    susp-func-∘-north f g ∙ ap (λ z → (susp-func g ∘ susp-func f) z) (merid a) ∎
  )

susp-func-∘ : ∀ {X Y Z : Type} (f : X → Y) (g : Y → Z)
            → susp-func {X} (g ∘ f) ∼ susp-func g ∘ susp-func f
susp-func-∘ f g = Susp-elim (λ z → susp-func (g ∘ f) z ≡ (susp-func g ∘ susp-func f) z)
  (susp-func-∘-north f g)
  (susp-func-∘-south f g)
  (susp-func-∘-merid f g)
```



    ? ≡⟨ ? ⟩
    ? ∎
