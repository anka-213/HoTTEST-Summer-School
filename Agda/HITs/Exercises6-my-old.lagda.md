
```agda

{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

open import new-prelude

open import Lecture6-notes
open import Lecture5-notes

module Exercises6-my-old where
```

In this problem set, you will look at a variation on the circle, a
higher inductive type for a "bowtie", i.e. two loops at a point.
(Unscaffolded harder exercise: do these problems for a "wedge of k
circles" for any natural number k.)

# HIT recursion from induction

In general, the dependent elimination rule for a higher inductive type
implies the simple/non-dependent elimination rule.  In this problem, you
will show this for the bowtie.  We could have done this for the circles
in the past lectures, but I wanted to introduce the non-dependent
elimination rule first, and then left both as postulates.

Note that this problem has a bit of a "metamathematical" flavor (showing
that a set of axioms is implied by a shorter set).  If you prefer to
jump right to the more "mathematical" problem of characterizing the loop
space of the bowtie below, I recommend turning Bowtie-rec and its
associated reductions into postulates like we have done for previous
higher inductive types, and adding a rewrite for the reduction on the
base point.  This will make Agda display things in a more easy to read
way (otherwise, it will display Bowtie-rec as a meta-variable).

Here is the definition of the bowtie and its dependent elimination rule:

```agda
postulate
  Bowtie : Set
  baseB : Bowtie
  loop1 : baseB ≡ baseB
  loop2 : baseB ≡ baseB
  Bowtie-elim : {l : Level} (X : Bowtie → Type l)
                (x : X baseB)
                (p : x ≡ x [ X ↓ loop1 ])
                (q : x ≡ x [ X ↓ loop2 ])
                → (x : Bowtie) → X x
  Bowtie-elim-base : {l : Level} (X : Bowtie → Type l)
                     (x : X baseB)
                     (p : x ≡ x [ X ↓ loop1 ])
                     (q : x ≡ x [ X ↓ loop2 ])
                  → Bowtie-elim X x p q baseB ≡ x
{-# REWRITE Bowtie-elim-base #-}

postulate
  Bowtie-elim-loop1 : {l : Level} (X : Bowtie → Type l)
                      (x : X baseB)
                      (p : x ≡ x [ X ↓ loop1 ])
                      (q : x ≡ x [ X ↓ loop2 ])
                    → apd (Bowtie-elim X x p q) loop1 ≡ p
  Bowtie-elim-loop2 : {l : Level} (X : Bowtie → Type l)
                      (x : X baseB)
                      (p : x ≡ x [ X ↓ loop1 ])
                      (q : x ≡ x [ X ↓ loop2 ])
                    → apd (Bowtie-elim X x p q) loop2 ≡ q
```

Next, we will prove the non-dependent elim/"recursion principle" from
these.  First, we need some lemmas.

(⋆) Paths over a path in a constant fibration are equivalent to paths.
It is simple to prove this by path induction.

```agda
PathOver-constant : {l1 l2 : Level} {A : Type l1} {B : Type l2}
                  → {a1 a2 : A}
                  → (p : a1 ≡ a2)
                  → {b1 b2 : B}
                  → b1 ≡ b2
                  → b1 ≡ b2 [ (\ _ → B) ↓ p ]
PathOver-constant (refl _) (refl _) = reflo

PathOver-constant-inverse : {l1 l2 : Level} {A : Type l1} {B : Type l2}
                          → {a1 a2 : A}
                          → (p : a1 ≡ a2)
                          → {b1 b2 : B}
                          → b1 ≡ b2 [ (\ _ → B) ↓ p ]
                          → b1 ≡ b2
PathOver-constant-inverse (refl _) reflo = refl _

PathOver-constant-inverse-cancel1 : {l1 l2 : Level} {A : Type l1} {B : Type l2}
                          → {a1 a2 : A}
                          → (p : a1 ≡ a2)
                          → {b1 b2 : B}
                          → (q : b1 ≡ b2)
                          → PathOver-constant-inverse p (PathOver-constant p q) ≡ q
PathOver-constant-inverse-cancel1 (refl _) (refl _) = refl _

PathOver-constant-inverse-cancel2 : {l1 l2 : Level} {A : Type l1} {B : Type l2}
                          → {a1 a2 : A}
                          → (p : a1 ≡ a2)
                          → {b1 b2 : B}
                          → (q : b1 ≡ b2 [ _ ↓ p ])
                          → PathOver-constant p (PathOver-constant-inverse p q) ≡ q
PathOver-constant-inverse-cancel2 (refl _) reflo = refl _

PathOver-constant-equiv : {l1 l2 : Level} {A : Type l1} {B : Type l2}
                          → {a1 a2 : A}
                          → (p : a1 ≡ a2)
                          → {b1 b2 : B}
                          → (b1 ≡ b2) ≃ (b1 ≡ b2 [ (\ _ → B) ↓ p ])
PathOver-constant-equiv p = improve (Isomorphism (PathOver-constant p)
                                    (Inverse (PathOver-constant-inverse p)
                                             (PathOver-constant-inverse-cancel1 p)
                                             (PathOver-constant-inverse-cancel2 p)))

```

(⋆) Next, for a non-dependent function f, there is an annoying mismatch between
ap f and apd f, which we can reconcile as follows:

```agda
ap-apd-constant : {l1 l2 : Level} {A : Type l1} {B : Type l2}
                → {a1 a2 : A}
                → (p : a1 ≡ a2)
                → (f : A → B)
                → ap f p ≡ PathOver-constant-inverse _ (apd f p)
ap-apd-constant (refl _) f = refl _
```

(⋆) Define Bowtie-rec and prove the reduction for base:

```agda
Bowtie-rec : {l : Level} {X : Type l}
             (x : X)
             (p : x ≡ x [ X ])
             (q : x ≡ x [ X ])
           → (Bowtie) → X
Bowtie-rec {_} {X} x p q = Bowtie-elim (λ _ → X) x (PathOver-constant loop1 p) (PathOver-constant loop2 q)

Bowtie-rec-base : {l : Level} {X : Type l}
             (x : X)
             (p : x ≡ x [ X ])
             (q : x ≡ x [ X ])
           → Bowtie-rec x p q baseB ≡ x
Bowtie-rec-base _ _ _ = refl _
```

(⋆⋆) Prove the reductions for loop:

```agda
Bowtie-rec-loop1 : {l : Level} {X : Type l}
               (x : X)
               (p : x ≡ x [ X ])
               (q : x ≡ x [ X ])
             → ap (Bowtie-rec x p q) loop1 ≡ p [ x ≡ x ]
Bowtie-rec-loop1 x p q =
  ap (Bowtie-rec x p q) loop1                                    ≡⟨ ap-apd-constant loop1 (Bowtie-rec x p q) ⟩
  PathOver-constant-inverse loop1 (apd (Bowtie-rec x p q) loop1) ≡⟨ ap (PathOver-constant-inverse loop1) (Bowtie-elim-loop1 _ _ _ _) ⟩
  PathOver-constant-inverse loop1 (PathOver-constant loop1 p)    ≡⟨ PathOver-constant-inverse-cancel1 loop1 p ⟩
  p                                                              ∎

Bowtie-rec-loop2 : {l : Level} {X : Type l}
                   (x : X)
                   (p : x ≡ x [ X ])
                   (q : x ≡ x [ X ])
                 → ap (Bowtie-rec x p q) loop2 ≡ q [ x ≡ x ]
Bowtie-rec-loop2 x p q =
  ap (Bowtie-rec x p q) loop2                                    ≡⟨ ap-apd-constant loop2 (Bowtie-rec x p q) ⟩
  PathOver-constant-inverse loop2 (apd (Bowtie-rec x p q) loop2) ≡⟨ ap (PathOver-constant-inverse loop2) (Bowtie-elim-loop2 _ _ _ _) ⟩
  PathOver-constant-inverse loop2 (PathOver-constant loop2 q)    ≡⟨ PathOver-constant-inverse-cancel1 loop2 q ⟩
  q                                                              ∎
```

# Loop space of the bowtie

In this problem, you will show that the loop space of the bowtie is the
"free group on two generators", which we will write in Agda as F2.  The
point of this problem is mainly for you to read and really understand
the proof that the loop space of the circle is ℤ.  All of the code is
essentially a rearrangement of code from that proof.  I'd suggest
trying the proof yourself, and looking at the analogous bits of the
Circle proof if you get stuck.

## Some lemmas (⋆⋆)

In the Circle proof in lecture, I inlined a couple of things that
can be proved more generally.  You might want to prove these general
versions in advance and use them in your proof, or, if that seems
confusing, you might first do the proof without these lemmas
to motivate them.

```agda
concat-equiv : ∀ {A : Type} (a : A) {a' a'' : A}
                     → (p : a' ≡ a'')
                     → (a ≡ a') ≃ (a ≡ a'')
-- concat-equiv a p = improve (Isomorphism (λ q → q ∙ p) (Inverse (λ q → q ∙ ! p)
--   (λ q → q ∙ p ∙ ! p   ≡⟨ ! (∙assoc q p (! p)) ⟩
--          q ∙ (p ∙ ! p) ≡⟨ ap (q ∙_) (!-inv-r p) ⟩
--          q             ∎)
--   (λ q → q ∙ ! p ∙ p   ≡⟨ ! (∙assoc q (! p) p) ⟩
--          q ∙ (! p ∙ p) ≡⟨ ap (q ∙_) (!-inv-l p) ⟩
--          q             ∎)))
concat-equiv a (refl _) = improve (Isomorphism (λ z → z) (Inverse (λ z → z) refl refl))

concat-equiv-map : ∀ {A : Type} {a a' a'' : A}
                 → (p : a' ≡ a'')
                 → fwd (concat-equiv a p) ≡ \ q → q ∙ p
-- concat-equiv-map p = refl _
concat-equiv-map (refl _) = refl _
```

(Note: you could also write out all of the components, but this was easier.)

```agda
transport-∙ : {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
                  {a1 a2 a3 : A} (p : a1 ≡ a2) (q : a2 ≡ a3)
                → transport B (p ∙ q) ∼ transport B q ∘ transport B p
transport-∙ p (refl _) x = refl _
```
## Calculating the loop space

First, we will assume a type F2 representing the free group on 2
generators.

ℤ is the free group on one generator, with 0 as the neutral element and
succℤ corresponding to "addition" with the one generator.  succℤ is an
equivalence, with the inverse representing "addition" with -1.

For other groups, it is somewhat more common to think of the group
operation as "multiplication" rather than "addition", so we will name
the neutral element as "1" and the action of the elements as
"multiplication".  Thus, we assume a type with an element 1F, and two
equivalences, which we think of as "multiplication with generator 1" and
"multiplication with generator 2".

Unscaffolded hard exercise: You can implement F2 as lists whose
elements are a four-element type g1, g2, g1⁻¹, g2⁻¹ with no adjacent
pairs of inverse elements.  Then the forward directions of mult1/mult2
will be implement by cons'ing g1/g2 on and "reducing" if that creates
two adjacent inverses, the backwards directions by consing g1⁻¹ and g2⁻¹
on and reducing, and the inverse laws will hold because the reduction
cancels the inverses.

For this problem, we will simply assume the nice universal property for
this type: that it maps uniquely into any other type with a point and
two equivalences, and that it is a set.

```agda
module AssumeF2
    (F2 : Type)
    (1F : F2)
    (mult1 : F2 ≃ F2)
    (mult2 : F2 ≃ F2)
    (F2-rec : {X : Type}
              (o : X)
              (m1 : X ≃ X)
              (m2 : X ≃ X)
            → F2 → X)
    (F2-rec-1 : {X : Type}
                (z : X)
                (m1 : X ≃ X)
                (m2 : X ≃ X)
              → F2-rec z m1 m2 1F ≡ z)
    (F2-rec-mult1 : {X : Type}
                    (z : X)
                    (m1 : X ≃ X)
                    (m2 : X ≃ X)
                    (a : F2) → F2-rec z m1 m2 (fwd mult1 a) ≡ fwd m1 (F2-rec z m1 m2 a))
    (F2-rec-mult2 : {X : Type}
                    (z : X)
                    (m1 : X ≃ X)
                    (m2 : X ≃ X)
                    (a : F2) → F2-rec z m1 m2 (fwd mult2 a) ≡ fwd m2 (F2-rec z m1 m2 a))
    (F2-rec-unique : {X : Type}
                    (f : F2 → X)
                    (z : X)
                    (m1 : X ≃ X)
                    (m2 : X ≃ X)
                  → f 1F ≡ z
                  → ((f ∘ fwd mult1) ∼ (fwd m1 ∘ f))
                  → ((f ∘ fwd mult2) ∼ (fwd m2 ∘ f))
                 → (x : F2) → f x ≡ F2-rec z m1 m2 x)
     (hSetF : is-set F2) where
```

(⋆⋆⋆) Prove that the loop space of the Bowtie is F2.  Each bit of the
proof will be analogous to the corresponding part of the Circle proof.

```agda
    Cover : Bowtie → Type
    Cover = Bowtie-rec F2 (ua mult1) (ua mult2)

    encode : (x : Bowtie) → baseB ≡ x → Cover x
    encode x p = transport Cover p 1F

    mult^ : F2 → baseB ≡ baseB
    mult^ = F2-rec (refl _) (concat-equiv baseB loop1) (concat-equiv baseB loop2)

    module _ (loopn : baseB ≡ baseB) (multn : F2 ≃ F2) (ap-Cover-loop : ap Cover loopn ≡ ua multn) where
      transport-Cover-loop-n : ∀  (x : F2) → transport Cover loopn x ≡ fwd multn x
      transport-Cover-loop-n x =
        transport Cover loopn x         ≡⟨ transport-ap-assoc Cover loopn ⟩
        transport id (ap Cover loopn) x ≡⟨ ap (λ H → transport id H x) ap-Cover-loop ⟩
        transport id (ua multn) x       ≡⟨ uaβ multn ⟩
        fwd multn x                     ∎

      decode-loop-n : (mult^-loop : ∀ a → mult^ (fwd multn a) ≡ fwd (concat-equiv baseB loopn) (mult^ a))
                    → PathOver (λ z → Cover z → baseB ≡ z) loopn mult^ mult^
      decode-loop-n mult^-loop = PathOver-→ (λ a → PathOver-path-to (! (decode-loop-n-lem a)))
        where
        decode-loop-n-lem : ∀ a → mult^ (transport (λ z → Cover z) loopn a) ≡ mult^ a ∙ loopn
        decode-loop-n-lem a =
          mult^ (transport (λ z → Cover z) loopn a) ≡⟨ ap mult^ (transport-Cover-loop-n a) ⟩
          mult^ (fwd multn a)                       ≡⟨ mult^-loop a ⟩
          fwd (concat-equiv baseB loopn) (mult^ a)  ≡⟨ app≡ (concat-equiv-map loopn) (mult^ a) ⟩
          mult^ a ∙ loopn                           ∎

    transport-Cover-loop1 : (x : F2) → transport Cover loop1 x ≡ fwd mult1 x
    transport-Cover-loop1 = transport-Cover-loop-n loop1 mult1 (Bowtie-rec-loop1 _ _ _)

    transport-Cover-loop2 : (x : F2) → transport Cover loop2 x ≡ fwd mult2 x
    transport-Cover-loop2 = transport-Cover-loop-n loop2 mult2 (Bowtie-rec-loop2 _ _ _)

    decode-loop1 : PathOver (λ z → Cover z → baseB ≡ z) loop1 mult^ mult^
    decode-loop1 = decode-loop-n loop1 mult1 (Bowtie-rec-loop1 _ _ _) (F2-rec-mult1 _ _ _)

    decode-loop2 : PathOver (λ z → Cover z → baseB ≡ z) loop2 mult^ mult^
    decode-loop2 = decode-loop-n loop2 mult2 (Bowtie-rec-loop2 _ _ _) (F2-rec-mult2 _ _ _)

    decode : (x : Bowtie) → Cover x → baseB ≡ x
    decode = Bowtie-elim _ mult^ decode-loop1 decode-loop2

    -- transport-Cover-loop1 x =
    --   transport Cover loop1 x ≡⟨ transport-ap-assoc Cover loop1 ⟩
    --   transport id (ap Cover loop1) x ≡⟨ ap (λ H → transport id H x) (Bowtie-rec-loop1 _ _ _) ⟩
    --   transport id (ua mult1) x ≡⟨ uaβ mult1 ⟩
    --   fwd mult1 x ∎

    -- decode-loop1 = PathOver-→ (λ a → PathOver-path-to (! (
    --            mult^ (transport (λ z → Cover z) loop1 a) ≡⟨ ap mult^ (transport-Cover-loop1 a) ⟩
    --            mult^ (fwd mult1 a)                       ≡⟨ F2-rec-mult1 _ _ _ a ⟩
    --            fwd (concat-equiv baseB loop1) (mult^ a)  ≡⟨ app≡ (concat-equiv-map loop1) (mult^ a) ⟩
    --            mult^ a ∙ loop1                           ∎)))

    -- decode-loop2 = PathOver-→ (λ a → PathOver-path-to (! (
    --            mult^ (transport (λ z → Cover z) loop2 a) ≡⟨ ap mult^ (transport-Cover-loop2 a) ⟩
    --            mult^ (fwd mult2 a)                       ≡⟨ F2-rec-mult2 _ _ _ a ⟩
    --            fwd (concat-equiv baseB loop2) (mult^ a)  ≡⟨ app≡ (concat-equiv-map loop2) (mult^ a) ⟩
    --            mult^ a ∙ loop2                           ∎)))


    encode-decode : (x : Bowtie) (p : baseB ≡ x) → decode x (encode x p) ≡ p
    encode-decode .baseB (refl .baseB) = F2-rec-1 _ _ _

    endo-F2-is-id : (f : F2 → F2)
                → f 1F ≡ 1F
                → (f ∘ fwd mult1) ∼ (fwd mult1 ∘ f)
                → (f ∘ fwd mult2) ∼ (fwd mult2 ∘ f)
                → f ∼ id
    endo-F2-is-id f f0 fm1 fm2 x =
      f x ≡⟨ F2-rec-unique f 1F mult1 mult2 f0 fm1 fm2 x  ⟩
      F2-rec 1F mult1 mult2 x ≡⟨ ! (F2-rec-unique id 1F mult1 mult2 (refl 1F) (λ _ → refl _) (λ _ → refl _) x) ⟩
      id x ∎

    encode-mult^ : F2 → F2
    encode-mult^ p = encode baseB (mult^ p)

    encode-mult^-1 : encode baseB (mult^ 1F) ≡ 1F
    encode-mult^-1 =
      encode baseB (mult^ 1F)   ≡⟨ ap (encode baseB) (F2-rec-1 _ _ _) ⟩
      encode baseB (refl baseB) ≡⟨ refl _ ⟩
      1F                        ∎

    module _ (loopn : baseB ≡ baseB) (multn : F2 ≃ F2) (ap-Cover-loop : ap Cover loopn ≡ ua multn) where
      transport-Cover-then-loopn : {x : Bowtie} (p : x ≡ baseB) (y : Cover x)
                                → transport Cover (p ∙ loopn) y ≡ fwd multn (transport Cover p y)
      transport-Cover-then-loopn (refl .baseB) y =
        transport Cover (refl baseB ∙ loopn) y     ≡⟨ ap (λ p → transport Cover p y) (∙unit-l loopn) ⟩
        transport Cover loopn y                    ≡⟨ transport-Cover-loop-n loopn multn ap-Cover-loop y ⟩
        fwd multn y                                ≡⟨ refl _ ⟩
        fwd multn (transport Cover (refl baseB) y) ∎

      encode-mult^-multn : (mult^-loop : ∀ a → mult^ (fwd multn a) ≡ fwd (concat-equiv baseB loopn) (mult^ a))
                         → (encode-mult^ ∘ fwd multn) ∼ (fwd multn ∘ encode-mult^)
      encode-mult^-multn mult^-loop x =
        encode baseB (mult^ (fwd multn x)) ≡⟨ ap (encode baseB) (mult^-loop x) ⟩
        encode baseB (fwd (concat-equiv baseB loopn) (mult^ x)) ≡⟨ ap (encode baseB) (app≡ (concat-equiv-map loopn) (mult^ x)) ⟩
        encode baseB (mult^ x ∙ loopn) ≡⟨ transport-Cover-then-loopn (mult^ x) 1F ⟩
        fwd multn (encode baseB (mult^ x)) ∎

    -- transport-Cover-then-loop1 : {x : Bowtie} (p : x ≡ baseB) (y : Cover x)
    --                            → transport Cover (p ∙ loop1) y ≡ fwd mult1 (transport Cover p y)
    -- transport-Cover-then-loop1 = transport-Cover-then-loopn loop1 mult1 (Bowtie-rec-loop1 _ _ _)
    -- transport-Cover-then-loop1 (refl .baseB) y =
    --   transport Cover (refl baseB ∙ loop1) y ≡⟨ ap (λ p → transport Cover p y) (∙unit-l loop1) ⟩
    --   transport Cover loop1 y ≡⟨ transport-Cover-loop1 y ⟩
    --   fwd mult1 y ≡⟨ refl _ ⟩
    --   fwd mult1 (transport Cover (refl baseB) y) ∎

    decode-encode-base : (p : F2) → encode baseB (mult^ p) ≡ p
    decode-encode-base = endo-F2-is-id encode-mult^ encode-mult^-1 encode-mult^-mult1 encode-mult^-mult2
      where
      encode-mult^-mult1 : (encode-mult^ ∘ fwd mult1) ∼ (fwd mult1 ∘ encode-mult^)
      encode-mult^-mult1 = encode-mult^-multn loop1 mult1 (Bowtie-rec-loop1 _ _ _) (F2-rec-mult1 _ _ _)
        -- encode baseB (mult^ (fwd mult1 x)) ≡⟨ ap (encode baseB) (F2-rec-mult1 _ _ _ x) ⟩
        -- encode baseB (fwd (concat-equiv baseB loop1) (mult^ x)) ≡⟨ ap (encode baseB) {!!} ⟩
        -- encode baseB (mult^ x ∙ loop1) ≡⟨ {!transport-Cover-then-loop1!} ⟩
        -- fwd mult1 (encode baseB (mult^ x)) ∎

      encode-mult^-mult2 : (encode-mult^ ∘ fwd mult2) ∼ (fwd mult2 ∘ encode-mult^)
      encode-mult^-mult2 = encode-mult^-multn loop2 mult2 (Bowtie-rec-loop2 _ _ _) (F2-rec-mult2 _ _ _)


    decode-encode : (x : Bowtie) (p : Cover x) → encode x (decode x p) ≡ p
    decode-encode = Bowtie-elim _ decode-encode-base {!!} {!!}

```
