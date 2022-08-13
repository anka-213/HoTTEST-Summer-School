
```agda

{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

open import new-prelude

open import Lecture6-notes
open import Lecture5-notes

module Exercises6-my-general where
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
space of the bowtie below, I recommend turning Wedge-rec and its
associated reductions into postulates like we have done for previous
higher inductive types, and adding a rewrite for the reduction on the
base point.  This will make Agda display things in a more easy to read
way (otherwise, it will display Wedge-rec as a meta-variable).

Here is the definition of the wedge over k-circles and its dependent elimination rule:

```agda
data Fin : ℕ → Type where
  0F : ∀ {n} → Fin (suc n)
  sucF : ∀ {n} → Fin n → Fin (suc n)

module WedgeK (n : ℕ) where
  postulate
    Wedge : Set
    baseB : Wedge
    loops : (k : Fin n) →  baseB ≡ baseB
    Wedge-elim : {l : Level} (X : Wedge → Type l)
                  (x : X baseB)
                  (p : ∀ k → x ≡ x [ X ↓ loops k ])
                  → (x : Wedge) → X x
    Wedge-elim-base : {l : Level} (X : Wedge → Type l)
                       (x : X baseB)
                       (p : ∀ k → x ≡ x [ X ↓ loops k ])
                    → Wedge-elim X x p baseB ≡ x
  {-# REWRITE Wedge-elim-base #-}


  postulate
    Wedge-elim-loop : {l : Level} (X : Wedge → Type l)
                       (x : X baseB)
                       (p : ∀ k → x ≡ x [ X ↓ loops k ])
                       (k : Fin n)
                     → apd (Wedge-elim X x p) (loops k) ≡ p k
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

(⋆) Define Wedge-rec and prove the reduction for base:

```agda
module _ {n : ℕ} where
  open WedgeK n
  Wedge-rec : {l : Level} {X : Type l}
              (x : X)
              (p : (k : Fin n) → x ≡ x [ X ])
            → (Wedge) → X
  Wedge-rec {_} {X} x p = Wedge-elim (λ _ → X) x λ k → PathOver-constant (loops k) (p k)

  Wedge-rec-base : {l : Level} {X : Type l}
              (x : X)
              (p : (k : Fin n) → x ≡ x [ X ])
            → Wedge-rec x p baseB ≡ x
  Wedge-rec-base _ _ = refl _
```

(⋆⋆) Prove the reductions for loop:

```agda
  Wedge-rec-loop : {l : Level} {X : Type l}
                (x : X)
                (p : (k : Fin n) → x ≡ x [ X ])
                (k : Fin n)
              → ap (Wedge-rec x p) (loops k) ≡ p k [ x ≡ x ]
  Wedge-rec-loop x p k =
    ap (Wedge-rec x p) (loops k)                                            ≡⟨ ap-apd-constant (loops k) (Wedge-rec x p) ⟩
    PathOver-constant-inverse (loops k) (apd (Wedge-rec x p) (loops k))     ≡⟨ ap (PathOver-constant-inverse (loops k)) (Wedge-elim-loop _ _ _ _) ⟩
    PathOver-constant-inverse (loops k) (PathOver-constant (loops k) (p k)) ≡⟨ PathOver-constant-inverse-cancel1 (loops k) (p k) ⟩
    p k                                                                     ∎

```

# Loop space of the bowtie

In this problem, you will show that the loop space of the bowtie is the
"free group on two generators", which we will write in Agda as Fk.  The
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

First, we will assume a type Fk representing the free group on 2
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

Unscaffolded hard exercise: You can implement Fk as lists whose
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
module AssumeFk {n : ℕ}
    (Fk : Type)
    (1F : Fk)
    (mult : (k : Fin n) → Fk ≃ Fk)
    (Fk-rec : {X : Type}
              (o : X)
              (m1 : (k : Fin n) → X ≃ X)
            → Fk → X)
    (Fk-rec-1 : {X : Type}
                (z : X)
                (m1 : (k : Fin n) → X ≃ X)
              → Fk-rec z m1 1F ≡ z)
    (Fk-rec-mult : {X : Type}
                    (z : X)
                    (m1 : (k : Fin n) → X ≃ X)
                    (k : Fin n)
                    → Fk-rec z m1 ∘ fwd (mult k) ∼ fwd (m1 k) ∘ Fk-rec z m1)
    (Fk-rec-unique : {X : Type}
                    (f : Fk → X)
                    (z : X)
                    (m1 : (k : Fin n) → X ≃ X)
                  → f 1F ≡ z
                  → ((k : Fin n) → (f ∘ fwd (mult k)) ∼ (fwd (m1 k) ∘ f))
                 → (x : Fk) → f x ≡ Fk-rec z m1 x)
     (hSetF : is-set Fk) where
```

(⋆⋆⋆) Prove that the loop space of the Wedge is Fk.  Each bit of the
proof will be analogous to the corresponding part of the Circle proof.

```agda
    open WedgeK n
    Cover : Wedge → Type
    Cover = Wedge-rec Fk (ua ∘ mult)

    encode : (x : Wedge) → baseB ≡ x → Cover x
    encode x p = transport Cover p 1F

    mult^ : Fk → baseB ≡ baseB
    mult^ = Fk-rec (refl _) (λ k → concat-equiv baseB (loops k))

    endo-Fk-is-id : (f : Fk → Fk)
                → f 1F ≡ 1F
                → (∀ k → (f ∘ fwd (mult k)) ∼ (fwd (mult k) ∘ f))
                → f ∼ id
    endo-Fk-is-id f f0 fm1 x =
      f x ≡⟨ Fk-rec-unique f 1F mult f0 fm1 x  ⟩
      Fk-rec 1F mult x ≡⟨ ! (Fk-rec-unique id 1F mult (refl 1F)  (λ k _ → refl _) x) ⟩
      id x ∎

    encode-mult^ : Fk → Fk
    encode-mult^ p = encode baseB (mult^ p)

    encode-mult^-1 : encode baseB (mult^ 1F) ≡ 1F
    encode-mult^-1 =
      encode baseB (mult^ 1F)   ≡⟨ ap (encode baseB) (Fk-rec-1 _ _) ⟩
      encode baseB (refl baseB) ≡⟨ refl _ ⟩
      1F                        ∎

    -- In order to generalize the proof, we need some common data for each loop
    record LoopMult : Type₁ where
      constructor mkLoopMult
      field
        loopn : baseB ≡ baseB
        multn : Fk ≃ Fk
        ap-Cover-loop : ap Cover loopn ≡ ua multn
        mult^-mult : ∀ a → mult^ (fwd multn a) ≡ fwd (concat-equiv baseB loopn) (mult^ a)

    loop-mult : (k : Fin n) → LoopMult
    loop-mult k = mkLoopMult (loops k) (mult k) (Wedge-rec-loop _ _ k) (Fk-rec-mult _ _ k)

    module _ (lm : LoopMult) where
      open LoopMult lm

      transport-Cover-loop-n : ∀  (x : Fk) → transport Cover loopn x ≡ fwd multn x
      transport-Cover-loop-n x =
        transport Cover loopn x         ≡⟨ transport-ap-assoc Cover loopn ⟩
        transport id (ap Cover loopn) x ≡⟨ ap (λ H → transport id H x) ap-Cover-loop ⟩
        transport id (ua multn) x       ≡⟨ uaβ multn ⟩
        fwd multn x                     ∎

      decode-loop-n : PathOver (λ z → Cover z → baseB ≡ z) loopn mult^ mult^
      decode-loop-n = PathOver-→ (λ a → PathOver-path-to (! (decode-loop-n-lem a)))
        where
        decode-loop-n-lem : ∀ a → mult^ (transport (λ z → Cover z) loopn a) ≡ mult^ a ∙ loopn
        decode-loop-n-lem a =
          mult^ (transport (λ z → Cover z) loopn a) ≡⟨ ap mult^ (transport-Cover-loop-n a) ⟩
          mult^ (fwd multn a)                       ≡⟨ mult^-mult a ⟩
          fwd (concat-equiv baseB loopn) (mult^ a)  ≡⟨ app≡ (concat-equiv-map loopn) (mult^ a) ⟩
          mult^ a ∙ loopn                           ∎

      transport-Cover-then-loopn : {x : Wedge} (p : x ≡ baseB) (y : Cover x)
                                → transport Cover (p ∙ loopn) y ≡ fwd multn (transport Cover p y)
      transport-Cover-then-loopn (refl .baseB) y =
        transport Cover (refl baseB ∙ loopn) y     ≡⟨ ap (λ p → transport Cover p y) (∙unit-l loopn) ⟩
        transport Cover loopn y                    ≡⟨ transport-Cover-loop-n y ⟩
        fwd multn y                                ≡⟨ refl _ ⟩
        fwd multn (transport Cover (refl baseB) y) ∎

      encode-mult^-multn : (encode-mult^ ∘ fwd multn) ∼ (fwd multn ∘ encode-mult^)
      encode-mult^-multn x =
        encode baseB (mult^ (fwd multn x)) ≡⟨ ap (encode baseB) (mult^-mult x) ⟩
        encode baseB (fwd (concat-equiv baseB loopn) (mult^ x)) ≡⟨ ap (encode baseB) (app≡ (concat-equiv-map loopn) (mult^ x)) ⟩
        encode baseB (mult^ x ∙ loopn) ≡⟨ transport-Cover-then-loopn (mult^ x) 1F ⟩
        fwd multn (encode baseB (mult^ x)) ∎


    decode-loops : ∀ k → PathOver (λ z → Cover z → baseB ≡ z) (loops k) mult^ mult^
    decode-loops = decode-loop-n ∘ loop-mult

    decode : (x : Wedge) → Cover x → baseB ≡ x
    decode = Wedge-elim _ mult^ decode-loops

    encode-decode : (x : Wedge) (p : baseB ≡ x) → decode x (encode x p) ≡ p
    encode-decode .baseB (refl .baseB) = Fk-rec-1 _ _

    decode-encode-base : (p : Fk) → encode baseB (mult^ p) ≡ p
    decode-encode-base = endo-Fk-is-id encode-mult^ encode-mult^-1 encode-mult^-mult
      where
      encode-mult^-mult : ∀ k → (encode-mult^ ∘ fwd (mult k)) ∼ (fwd (mult k) ∘ encode-mult^)
      encode-mult^-mult = encode-mult^-multn ∘ loop-mult

    module _ (lm : LoopMult) where
      open LoopMult lm
      decode-encode-loopn : PathOver (λ z → (p : Cover z) → encode z (decode z p) ≡ p) loopn decode-encode-base decode-encode-base
      decode-encode-loopn = PathOver-Π λ q → fwd (transport-to-pathover _ _ _ _) (hSetF _ _ _ _)

    decode-encode : (x : Wedge) (p : Cover x) → encode x (decode x p) ≡ p
    decode-encode = Wedge-elim _ decode-encode-base λ k → decode-encode-loopn (loop-mult k)

    wedge-Cover-equiv : ∀ b → (baseB ≡ b) ≃ Cover b
    wedge-Cover-equiv b = improve (Isomorphism (encode b) (Inverse (decode b) (encode-decode b) (decode-encode b)))

    wedge-Fk-equiv : (baseB ≡ baseB) ≃ Fk
    wedge-Fk-equiv = wedge-Cover-equiv baseB

open ImplementInts
module WedgeInts = AssumeFk {1}
    ℤ 0ℤ (λ _ → succℤ)
    (λ o m1 → ℤ-rec o (m1 0F))
    (λ z m1 → ℤ-rec-0ℤ z (m1 0F))
    (λ {z m1 0F → ℤ-rec-succℤ z (m1 0F)})
    (λ f z m1 f0 fsucc → ℤ-rec-unique f z (m1 0F) f0 (fsucc 0F))
    --  (hSetF : is-set Fk) where
```
