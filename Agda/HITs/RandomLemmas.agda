{-# OPTIONS --rewriting --without-K --allow-unsolved-metas --postfix-projections #-}

open import new-prelude

open import Lecture6-notes
open import Lecture5-notes
open import Lecture4-notes
open import HoTT-WS9

module RandomLemmas where

private
  variable
    ℓ l1 l2 l3 : Level
    A B C P Q : Type

fib' : ∀ {A : Type l1} {B : Type l2} (f : A → B) → B → Type (l1 ⊔ l2)
fib' {A = A} f y = Σ x ꞉ A , f x ≡ y

is-equiv' : {A : Type l1} {B : Type l2} (f : A → B) → Type (l1 ⊔ l2)
is-equiv' {B = B} f = (y : B) → is-contr (fib' f y)

record _≃'_ (A : Type l1) (B : Type l2) : Type (l1 ⊔ l2) where
  constructor
    Equivalence'
  field
    map : A → B
    is-equivalence : is-equiv' map

-- pair≡d-simple

fib'-compose : {f : A → B} {g : B → C}
    → (∀ b → fib' f b) → (∀ c → fib' g c) → ∀ c → fib' (g ∘ f) c
fib'-compose {g = g} f-fib-b g-fib-c c = f-inv b , ap g (f-fib-b b .pr₂) ∙ gb=c
  where
    b = g-fib-c c .pr₁
    gb=c = g-fib-c c .pr₂
    -- f-inv : B → A
    f-inv = λ b → f-fib-b b .pr₁

is-equiv'-comp : {f : A → B} {g : B → C}
    → is-equiv' f → is-equiv' g → is-equiv' (g ∘ f)
is-equiv'-comp {A} {B} {C} {f = f} {g} f-equiv g-equiv c =
      (a , ap g (pr₂ f-fib-b) ∙ pr₂ g-fib-c)
    , uniqueness -- λ alt-fib → {!f-equiv (f (alt-fib .pr₁))!}
    -- , {!g-fib-ctr .pr₂!}
  where
    f-fib : (b : B) → fib' f b
    f-fib b = f-equiv b .pr₁
    f-inv : B → A
    f-inv b = f-fib b .pr₁
    f-fib-uniq : (b : B) (y : fib' f b) → f-fib b ≡ y
    f-fib-uniq b = f-equiv b .pr₂

    f-on-fib : fib' g c → fib' (g ∘ f) c
    f-on-fib (bb , gbb=c) = (f-inv bb) , ap g (f-equiv bb .pr₁ .pr₂) ∙ gbb=c
    g-fib : (c : C) → fib' g c
    g-fib c = g-equiv c .pr₁
    g-inv : C → B
    g-inv c = g-equiv c .pr₁ .pr₁
    g-fib-ctr : is-contr (fib' g c)
    g-fib-ctr = g-equiv c
    g-fib-c : fib' g c
    g-fib-c = pr₁ g-fib-ctr
    g-fib-uniq : (y : fib' g c) → g-fib-c ≡ y
    g-fib-uniq = pr₂ g-fib-ctr
    b : B
    b = pr₁ g-fib-c
    gb=c : g b ≡ c
    gb=c = g-fib-c .pr₂
    f-fib-ctr = f-equiv b
    f-fib-b = pr₁ f-fib-ctr
    a = pr₁ f-fib-b
    fa=b = f-fib-b .pr₂
    gfa=c : g (f a) ≡ c
    gfa=c = ap g fa=b ∙ gb=c
    uniqueness : (alt-fib : fib' (g ∘ f) c) → (a , gfa=c) ≡ alt-fib
    -- uniqueness (a' , refl .((g ∘ f) a')) = {!g (f a')!}
    -- uniqueness alt-fib =
    uniqueness (a' , gfa'=c) =
      (a , gfa=c)                          ≡⟨⟩
      (f-inv b , gfa=c)                    ≡⟨⟩
      (f-inv (g-inv c) , gfa=c)            ≡⟨⟩
      (f-inv (g-inv c) , ap g fa=b ∙ gb=c) ≡⟨⟩
      f-on-fib (g-inv c , gb=c)            ≡⟨⟩
      f-on-fib g-fib-c                     ≡⟨ ap f-on-fib alt-g-eq ⟩
      f-on-fib alt-g-fib                   ≡⟨⟩
      (f-inv (f a') , ap g (f-fib-b' .pr₂) ∙ gfa'=c)  ≡⟨⟩
      g-on-fib f-fib-b'                    ≡⟨ ap g-on-fib alt-f-fib'-eq ⟩
      g-on-fib (a' , refl _)               ≡⟨⟩
      (a' , ap g (refl (f a')) ∙ gfa'=c)   ≡⟨⟩
      (a' , refl (g (f a')) ∙ gfa'=c)      ≡⟨ ap (a' ,_) (∙unit-l _) ⟩
      -- (f a' , gfa'=c) ≡ (b , gb=c) -- g-fib-c
      (a' , gfa'=c)                        ≡⟨⟩
      alt-fib                              ∎
      where
      g-on-fib : fib' f (f a') → fib' (g ∘ f) c
      g-on-fib (aa , faa=fa') = aa , ap g (faa=fa') ∙ gfa'=c
      -- g-on-fib (bb , gbb=c) = (f-inv bb) , ap g (f-equiv bb .pr₁ .pr₂) ∙ gbb=c
      alt-fib : fib' (g ∘ f) c
      alt-fib = a' , gfa'=c
      -- a' = alt-fib .pr₁
      -- gfa'=c : g (f a') ≡ c
      -- gfa'=c = alt-fib .pr₂
      alt-f-fib-c = f-equiv (f a')
      alt-f-fib = alt-f-fib-c .pr₁
      a'' = alt-f-fib .pr₁
      fa'=b' : f a'' ≡ f a'
      fa'=b' = alt-f-fib .pr₂

      alt-g-fib : fib' g c
      alt-g-fib = f a' , gfa'=c
      f-fib-b' : fib' f (f a')
      f-fib-b' = f-fib (f a')
      alt-f-fib'-eq : f-fib (f a') ≡ (a' , refl _)
      alt-f-fib'-eq = f-fib-uniq (f a') (a' , refl _)

      -- (b , gb=c) ≡ (f a' , gfa'=c)
      alt-g-eq : g-fib-c ≡ alt-g-fib
      alt-g-eq = g-fib-uniq alt-g-fib


equiv'-comp : B ≃' C → A ≃' B → A ≃' C
equiv'-comp (Equivalence' g g-eq) (Equivalence' f f-eq) =
            Equivalence' (g ∘ f) (is-equiv'-comp f-eq g-eq)

conv-is-equiv : ∀  {map : A → B} → is-equiv map → is-equiv' map
conv-is-equiv = {!!}

conv-is-equiv-bwd : ∀  {map : A → B} → is-equiv' map → is-equiv map
conv-is-equiv-bwd = {!!}

conv-equiv : A ≃ B → A ≃' B
conv-equiv (Equivalence map is-equivalence) = Equivalence' map (conv-is-equiv is-equivalence)

conv-equiv-back : A ≃' B → A ≃ B
conv-equiv-back (Equivalence' map is-equivalence) = Equivalence map (conv-is-equiv-bwd is-equivalence)
