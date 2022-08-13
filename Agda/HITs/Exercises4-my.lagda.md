```agda
{-# OPTIONS --without-K --rewriting --postfix-projections #-}

open import new-prelude
open import Lecture4-notes

module Exercises4-my where
```

# Constructing homotopies between paths

(⋆) Give two "different" path-between-paths/homotopies between (loop ∙ !
loop) ∙ loop and loop.  They should be different in the sense that one
should cancel the !loop with the first loop, and one with the second
loop.  But these aren't really *really* different, in that there will be
a path-between-paths-between-paths between the two!

```agda
homotopy1 : (loop ∙ ! loop) ∙ loop ≡ loop
homotopy1 =
  (loop ∙ ! loop) ∙ loop ≡⟨ ap (_∙ loop) (!-inv-r loop) ⟩
  refl _ ∙ loop          ≡⟨ ∙unit-l loop ⟩
  loop ∎

homotopy2 : (loop ∙ ! loop) ∙ loop ≡ loop
homotopy2 =
  (loop ∙ ! loop) ∙ loop ≡⟨ ! (∙assoc _ _ loop) ⟩
  loop ∙ (! loop ∙ loop) ≡⟨ ap (loop ∙_) (!-inv-l loop) ⟩
  loop ∙ refl _          ≡⟨ refl loop ⟩
  loop ∎
```

(Harder exercise (🌶️): give a path between homotopy1 and
homotopy2! I'd recommend saving this until later though, because there
is a trick to it that we haven't covered in lecture yet.)

```agda
path-between-paths-between-paths : homotopy1 ≡ homotopy2
path-between-paths-between-paths =
  homotopy1          ≡⟨ refl _ ⟩
  ap (λ z → z ∙ loop) (!-inv-r loop) ∙ ∙unit-l loop          ≡⟨ gen loop ⟩
  -- ?          ≡⟨ ? ⟩
  (! (∙assoc loop (! loop) loop)) ∙ (ap (_∙_ loop) (!-inv-l loop))         ≡⟨ refl _ ⟩
  homotopy2 ∎
  where
   gen : ∀ {A : Type} {x y : A} (p : x ≡ y) →
      (ap (λ z → z ∙ p) (!-inv-r p) ∙ ∙unit-l p)  ≡
      (! (∙assoc p (! p) p)) ∙ (ap (_∙_ p) (!-inv-l p))
      [ p ∙ ! p ∙ p ≡ p ]
   gen (refl _) = refl _
```

# Functions are group homomorphism

(⋆⋆) State and prove a general lemma about what ap of a function on the
inverse of a path (! p) does (see ap-∙ for inspiration).

State and prove a general lemma about what ! (p ∙ q) is.

Use them to prove that the double function takes loop-inverse to
loop-inverse concatenated with itself.

```agda
-- ap-∙ : {A B : Type} {f : A → B} {x y z : A} (p : x ≡ y) (q : y ≡ z)
--        → ap f (p ∙ q) ≡ ap f p ∙ ap f q
-- ap-∙ (refl _) (refl _) = refl _

ap-! : {A B : Type} {f : A → B} {x y : A} (p : x ≡ y)
       → ap f (! p) ≡ ! (ap f p)
ap-! (refl _) = refl _

!-∙ : {A : Type} {x y z : A} (p : x ≡ y) (q : y ≡ z)
       → ! (p ∙ q) ≡ ! q ∙ ! p
!-∙ (refl _) (refl _) = refl _

double-!loop : ap double (! loop) ≡ ! loop ∙ ! loop
double-!loop =
  ap double (! loop)  ≡⟨ ap-! loop ⟩
  ! (ap double loop)  ≡⟨ ap ! (S1-rec-loop base (loop ∙ loop)) ⟩
  ! (loop ∙ loop)     ≡⟨ !-∙ loop loop  ⟩
  ! loop ∙ ! loop     ∎
```

(⋆) Define a function invert : S1 → S1 such that (ap invert) inverts a path
on the circle, i.e. sends the n-fold loop to the -n-fold loop.

```agda
invert : S1 → S1
invert = S1-rec base (! loop)
```

# Circles equivalence

See the maps between the 1 point circle and the 2 point circle in the
lecture code.  Check that the composite map S1 → S1
is homotopic to the identity on base and loop:

(⋆)

```agda
to-from-base : from (to base) ≡ base
to-from-base =
  from (to base)       ≡⟨ ap from (S1-rec-base north (east ∙ ! west)) ⟩
  from north           ≡⟨ Circle2-rec-north base base (refl _) loop ⟩
  base ∎
```

(⋆⋆⋆)

```
to-from-loop : ap from (ap to loop) ≡ loop
to-from-loop =
  ap from (ap to loop)            ≡⟨ ap (ap from) (S1-rec-loop north (east ∙ ! west)) ⟩
  ap from (east ∙ ! west)         ≡⟨ ap-∙ east (! west) ⟩
  ap from east ∙ ap from (! west) ≡⟨ ap (ap from east ∙_) (ap-! west) ⟩ -- or use ap₂
  ap from east ∙ ! (ap from west) ≡⟨ ap (λ p → ap from east ∙ ! p) ((Circle2-rec-west base base (refl _) loop )) ⟩
  ap from east ∙ ! (refl _)       ≡⟨ refl _ ⟩
  ap from east                    ≡⟨ Circle2-rec-east base base (refl _) loop ⟩
  loop ∎
```

Note: the problems below here are progressively more optional, so if you
run out of time/energy at some point that is totally fine.

# Torus to circles

The torus is equivalent to the product of two circles S1 × S1.  The idea
for the map from the torus to S1 × S1 that is part of this equivalence
is that one loop on on the torus is sent to to the circle loop in one
copy of S1, and the other loop on the torus to the loop in the other
copy of the circle.  Define this map.

Hint: for the image of the square, you might want a lemma saying how
paths in product types compose (⋆⋆⋆):

```agda
compose-pair≡ : {A B : Type} {x1 x2 x3 : A} {y1 y2 y3 : B}
                (p12 : x1 ≡ x2) (p23 : x2 ≡ x3)
                (q12 : y1 ≡ y2) (q23 : y2 ≡ y3)
              → ((pair≡ p12 q12) ∙ (pair≡ p23 q23)) ≡ pair≡ (p12 ∙ p23) (q12 ∙ q23)
                 [ (x1 , y1) ≡ (x3 , y3) [ A × B ] ]
compose-pair≡ (refl _) (refl _) (refl _) (refl _) = refl _
```

(🌶️)
```
torus-to-circles : Torus → S1 × S1
torus-to-circles = T-rec (base , base) (pair≡ loop (refl _)) (pair≡ (refl _) loop) (
  pair≡ loop (refl _) ∙ pair≡ (refl _) loop      ≡⟨ compose-pair≡ loop (refl _) (refl _) loop ⟩
  pair≡ (loop ∙ refl _) (refl _ ∙ loop)          ≡⟨ ap (pair≡ loop) (∙unit-l _) ⟩
  pair≡ loop            loop                     ≡⟨ ap (λ p → pair≡ p loop) (! (∙unit-l loop)) ⟩
  pair≡ (refl _ ∙ loop) (loop ∙ refl _)          ≡⟨ ! (compose-pair≡ (refl _) loop loop (refl _)) ⟩
  pair≡ (refl base) loop ∙ pair≡ loop (refl base) ∎)
```

# Suspensions (🌶️)

Find a type X such that the two-point circle Circle2 is equivalent to
the suspension Susp X.  Check your answer by defining a logical
equivalence (functions back and forth), since we haven't seen how to
prove that such functions are inverse yet.

```agda
c2s : Circle2 → Susp Bool
c2s = Circle2-rec northS southS (merid false) (merid true)

s2c : Susp Bool → Circle2
s2c = Susp-rec north south (λ b → if b then east else west)
```

Suspension is a functor from types, which means that it acts on
functions as well as types.  Define the action of Susp on functions:

```agda
susp-func : {X Y : Type} → (f : X → Y) → Susp X → Susp Y
susp-func f = Susp-rec northS southS (merid ∘ f)
```

To really prove that Susp is a functor, we should check that this action
on functions preserves the identity function and composition of
functions. But to do that we would need the dependent elimination rule
for suspensions, which we haven't talked about yet.

# Pushouts (🌶️)

Fix a type X.  Find types A,B,C with functions f : C → A and g : C → B
such that the suspension Susp X is equivalent to the Pushout C A B f g.
Check your answer by defining a logical equivalence (functions back and
forth), since we haven't seen how to prove that such functions are
inverse yet.

```agda
SuspFromPush : Type → Type
SuspFromPush A = Pushout A 𝟙 𝟙 (λ _ → ⋆) (λ _ → ⋆)

s2p : (A : Type) → Susp A → SuspFromPush A
s2p A = Susp-rec (inl ⋆) (inr ⋆) glue

p2s : (A : Type) → SuspFromPush A → Susp A
p2s A = Push-rec (λ _ → northS) (λ _ → southS) merid
```

Some of my random crap
```agda
data 𝟛 : Type where
 𝟛-1 : 𝟛
 𝟛-2 : 𝟛
 𝟛-3 : 𝟛

-- Circle with three loops
Circle3 : Type
Circle3 = Susp 𝟛

postulate
  FigureEight : Type
  mid : FigureEight
  westE  : mid ≡ mid
  eastE  : mid ≡ mid
  FigureEight-rec : {X : Type} (m : X) (w : m ≡ m) (e : m ≡ m)
              → FigureEight → X
  FigureEight-rec-mid : {X : Type} (m : X) (w : m ≡ m) (e : m ≡ m)
                    → FigureEight-rec m w e mid ≡ m
{-# REWRITE FigureEight-rec-mid #-}

postulate
  FigureEight-rec-west : {X : Type} (m : X) (w : m ≡ m) (e : m ≡ m)
                   → ap (FigureEight-rec m w e) westE ≡ w
  FigureEight-rec-east : {X : Type} (m : X) (w : m ≡ m) (e : m ≡ m)
                   → ap (FigureEight-rec m w e) eastE ≡ e


circle3-to-figure8 : Circle3 → FigureEight
circle3-to-figure8 = Susp-rec mid mid
   (λ { 𝟛-1 → westE ; 𝟛-2 → refl mid ; 𝟛-3 → eastE})

conv-proof : northS ≡ southS → northS ≡ northS
conv-proof = transport (λ x → northS ≡ x) (! (merid 𝟛-2))

figure8-to-circle3 : FigureEight → Circle3
figure8-to-circle3 = FigureEight-rec northS (conv-proof (merid 𝟛-1)) (conv-proof (merid 𝟛-3))

isContr : ∀ {ℓ} → Type ℓ → Type ℓ
isContr A = Σ x ꞉ A , (∀ y → x ≡ y)

-- Failed attempt at turning a Circle2 into a contractible type via Pushout
flipC2 : Circle2 → Circle2
flipC2 = Circle2-rec north south east west

ContrC2 : Type
ContrC2 = Pushout Circle2 Circle2 Circle2 (λ x → x) flipC2

-- cc2-contr : Σ x ꞉ ContrC2 , ∀ (y : ContrC2) → x ≡ y
cc2-contr : isContr ContrC2
cc2-contr = inl north , λ y → Push-rec
  {!!}
  {!!} {!!} y

-- ContrC2 : Type
-- ContrC2 = Pushout 𝟙 _ _ (λ _ → west) (λ _ → east)

-- CC22unit : ContrC2 → 𝟙
-- CC22unit = Push-rec (λ _ → ⋆) (λ _ → ⋆) λ c → refl ⋆

-- unit2CC2 : 𝟙 → ContrC2
-- unit2CC2 _ = {!!}

-- cc2-contr : Σ x ꞉ ContrC2 , ∀ (y : ContrC2) → x ≡ y
-- cc2-contr = (inl west) , (λ y → Push-rec {!!} {!!} {!!} y)

```

More experiments with Pushouts
agda```

module PushoutOf (C : Type) (A : Type) (B : Type) (f : C → A) (g : C → B) where
  record IsRawPushout (Pout : Type) : Type where
    field
      inlP : A → Pout
      inrP : B → Pout
      commute : (c : C) → inlP (f c) ≡ inrP (g c)
  record IsPushout (Pout : Type) : Type₁ where
    open IsRawPushout
    field
      irp : IsRawPushout Pout
      universal : {X : Type} → IsRawPushout X → Pout → X
      unique : {X : Type} → (rp : IsRawPushout X) → (y : Pout → X) →
               y ∘ inlP irp ∼ inlP rp → y ∘ inrP irp ∼ inrP rp →
               y ∼ universal rp
      leftTri : ∀ {X : Type} (rp : IsRawPushout X) → universal rp ∘ inlP irp ∼ inlP rp
      rightTri : ∀ {X : Type} (rp : IsRawPushout X) → universal rp ∘ inrP irp ∼ inrP rp

      -- universal : {X : Type} → IsRawPushout X → Pout → X
    open IsRawPushout irp public
      -- Push-universal : {X : Type} (l : A → X) (r : B → X) (gl : (c : C) → l (f c) ≡ r (g c))
      --         → Pout → X

  pushout-is-raw-pushout : IsRawPushout (Pushout C A B f g)
  pushout-is-raw-pushout = record { inlP = inl ; inrP = inr ; commute = glue }

  pushout-is-universal : {X : Type} → IsRawPushout X → Pushout C A B f g → X
  -- pushout-is-universal rp = Push-rec (λ x → (inlP rp x) , {!!}) {!!} {!!}
  --   where open IsRawPushout
  pushout-is-universal rp p = Push-rec (inlP rp) (inrP rp) (commute rp) p
    where open IsRawPushout
                            -- , λ y → {!Push-rec-inl!}

  pushout-is-pushout : IsPushout (Pushout C A B f g)
  pushout-is-pushout = record { irp = pushout-is-raw-pushout ; universal = pushout-is-universal
    ; unique = λ { rp y lh rh p → {!!}}
    ; leftTri = {!!}
    ; rightTri = {!!}
    }
    where open IsRawPushout
```

Bonus postulates
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
          → ap (Susp-rec n s m) ∘ merid ∼ m
  Susp-elim : {l : Level} {A : Type} (X : Susp A → Type l)
             (n : X northS) (s : X southS) (m : (a : A) → transport X (merid a) n ≡ s)
          → (susp : Susp A) → X susp

```


The pushout of two constant functions into bool is the three-value type 𝟛
```agda
module _ (A : Type) (point : A) where
  open PushoutOf A Bool Bool (λ _ → false) (λ _ → true)
  simplePushout : IsRawPushout 𝟛
  simplePushout = record
    { inlP = λ { true → 𝟛-1 ; false → 𝟛-2}
    ; inrP = λ { true → 𝟛-2 ; false → 𝟛-3}
    ; commute = λ c → refl 𝟛-2 }
  open IsRawPushout
  simplePushoutUniversal : {X : Type} → IsRawPushout X → 𝟛 → X
  simplePushoutUniversal xrp 𝟛-1 = inlP xrp true
  simplePushoutUniversal xrp 𝟛-2 = inlP xrp false
  simplePushoutUniversal xrp 𝟛-3 = inrP xrp false
    -- where open IsRawPushout xrp
  simpleFullPushout : IsPushout 𝟛
  simpleFullPushout = record
    { irp = simplePushout
    ; universal = simplePushoutUniversal
    ; unique = λ rp y lh rh → λ { 𝟛-1 → lh true ; 𝟛-2 → lh false ; 𝟛-3 → rh false}
    ; leftTri = λ rp → λ { true → refl _ ; false → refl _ }
    ; rightTri = λ rp → λ { true → commute rp point ; false → refl _ }
    }
```

Proof that susp is a pushout out of 𝟙
```agda
-- SuspFromPush A = Pushout A 𝟙 𝟙 (λ _ → ⋆) (λ _ → ⋆)

module _ (A : Type) where
  open PushoutOf A 𝟙 𝟙 (λ _ → ⋆) (λ _ → ⋆)
  open IsRawPushout
  susp-is-raw-push : IsRawPushout (Susp A)
  susp-is-raw-push = record { inlP = λ x → northS ; inrP = λ _ → southS ; commute = merid }
  susp-is-universal-push : ∀ {X} → IsRawPushout X → Susp A → X
  susp-is-universal-push rp = Susp-rec (inlP rp ⋆) (inrP rp ⋆) (commute rp)
  susp-is-pushout : IsPushout (Susp A)
  susp-is-pushout = record
    { irp = susp-is-raw-push
    ; universal = susp-is-universal-push
    ; unique = λ rp y yn ys →
                              Susp-elim ( λ sus → y sus ≡ susp-is-universal-push rp sus)
                              -- (yn ⋆ ∙ ! (Susp-rec-north (inlP rp ⋆) (inrP rp ⋆) (commute rp)))
                              -- (ys ⋆ ∙ ! (Susp-rec-south (inlP rp ⋆) (inrP rp ⋆) (commute rp)))
                              (yn ⋆) (ys ⋆)
                              λ a → {!helper (Susp-rec-merid (inlP rp ⋆) (inrP rp ⋆) (commute rp) a)!}
                              -- λ a → {!Susp-rec-merid (inlP rp ⋆) (inrP rp ⋆) (commute rp) a!}
    ; leftTri = λ rp _ → Susp-rec-north (inlP rp ⋆) (inrP rp ⋆) (commute rp)
    ; rightTri = λ rp _ → Susp-rec-south (inlP rp ⋆) (inrP rp ⋆) (commute rp)
    }
  -- hehelper : ∀ {A} {X}
  --          {rp : PushoutOf.IsRawPushout A 𝟙 𝟙 (λ _ → ⋆) (λ _ → ⋆) X}
  --          {y : Susp A → X}
  --          {yn
  --           : (y ∘ PushoutOf.IsRawPushout.inlP susp-is-raw-push) ∼
  --             PushoutOf.IsRawPushout.inlP rp}
  --          {ys
  --           : (y ∘ PushoutOf.IsRawPushout.inrP susp-is-raw-push) ∼
  --             PushoutOf.IsRawPushout.inrP rp}
  --          {a : A} →
  --        ap
  --        (Susp-rec (PushoutOf.IsRawPushout.inlP rp ⋆)
  --         (PushoutOf.IsRawPushout.inrP rp ⋆)
  --         (PushoutOf.IsRawPushout.commute rp))
  --        (merid a)
  --        ≡ PushoutOf.IsRawPushout.commute rp a →
  --        transport
  --        (λ sus →
  --           y sus ≡
  --           Susp-rec (PushoutOf.IsRawPushout.inlP rp ⋆)
  --           (PushoutOf.IsRawPushout.inrP rp ⋆)
  --           (PushoutOf.IsRawPushout.commute rp) sus)
  --        (merid a) (yn ⋆)
  --        ≡ ys ⋆
  helper : ∀ {X}
           {rp : PushoutOf.IsRawPushout A 𝟙 𝟙 (λ _ → ⋆) (λ _ → ⋆) X}
           {y : Susp A → X}
           {sirpl sirpr : 𝟙 → Susp A}
           {sirpmid : (c : A) → sirpl ⋆ ≡ sirpr ⋆}
           {yn
            : (y ∘ sirpl) ∼
              PushoutOf.IsRawPushout.inlP rp}
           {ys
            : (y ∘ sirpr) ∼
              PushoutOf.IsRawPushout.inrP rp}
           {a : A}  →
         transport (λ sus → y sus ≡ susp-is-universal-push rp sus) (sirpmid a)
         {!yn ⋆!}
         ≡ {!!}
  helper {yn = yn} = {!yn ⋆!}
```

```agda
-- _↯ = 𝟘-nondep-elim
```

  Pushout : (C : Type) (A : Type) (B : Type) (f : C → A) (g : C → B) → Type

module _  {C : Type} {A : Type} {B : Type} {f : C → A} {g : C → B} where

  postulate
    inl : A → Pushout C A B f g
    inr : B → Pushout C A B f g
    glue : (c : C) → inl (f c) ≡ inr (g c)
    Push-rec : {X : Type} (l : A → X) (r : B → X) (gl : (c : C) → l (f c) ≡ r (g c))
             → Pushout C A B f g → X
