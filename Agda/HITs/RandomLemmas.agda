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
    A B C D P Q : Type

map-∔ : (f : A → B) (g : C → D) → (A ∔ C) → (B ∔ D)
map-∔ f g (inl+ x) = inl+ (f x)
map-∔ f g (inr+ x) = inr+ (g x)

map-× : (f : A → B) (g : C → D) → (A × C) → (B × D)
map-× f g (a , b) = f a , g b

-- Regarding equality of pairs

pair≡d-refl : {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
         {a : A}
         {b : B a} {b' : B a} (q : b ≡ b' [ B a ])
       → (a , b) ≡ (a , b') [ Σ B ]
pair≡d-refl (refl _) = refl _

pair≡d-prop : {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
         {a a' : A} (p : a ≡ a')
         {b : B a} {b' : B a'} (q : ∀ a → is-prop (B a))
       → (a , b) ≡ (a' , b') [ Σ B ]
pair≡d-prop {a = a} (refl _) ip = ap (a ,_) (ip a _ _)

pair≡d-prop-pr₁ : {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
         {a a' : A} {p : a ≡ a'}
         {b : B a} {b' : B a'} {q : ∀ a → is-prop (B a)}
       → ap pr₁ (pair≡d-prop p {b} {b'} q) ≡ p
pair≡d-prop-pr₁ {B = B} {a = a} {p = refl _} {b} {b'} {q}
  = lem (q a b b')
  where
  lem : ∀ (w : b ≡ b') → ap pr₁ (ap (_,_ {B = B} a) w) ≡ refl a
  lem (refl .b) = refl _

record is-functor (F : Type → Type) : Type₁ where
  field
    Fmap : (A → B) → F A → F B
    Fid : Fmap {A} id ∼ id
    F∘ : (f : B → C) (g : A → B) → Fmap (f ∘ g) ∼ Fmap f ∘ Fmap g

ap≃ : (F : Type → Type) → is-functor F → A ≃ B → F A ≃ F B
ap≃ F F-fun (Equivalence map (Inverse post-inverse₁ is-post-inverse₁ pre-inverse₁ is-pre-inverse₁))
  = Equivalence (Fmap map) (Inverse (Fmap post-inverse₁)
                (λ x → ! (F∘ post-inverse₁ map x) ∙ (app≡ (ap Fmap (λ≡ (λ x₁ → is-post-inverse₁ x₁))) x ∙ Fid x))
                (Fmap pre-inverse₁) λ x →
                  Fmap map (Fmap pre-inverse₁ x) ≡⟨ ! (F∘ _ _ _) ⟩
                  Fmap (map ∘ pre-inverse₁) x ≡⟨ app≡ (ap Fmap (λ≡ is-pre-inverse₁)) x ⟩
                  Fmap id x ≡⟨ Fid _ ⟩
                  id x ∎)
  where open is-functor F-fun

ap≃-∔ : A ≃ B → C ≃ D → (A ∔ C) ≃ (B ∔ D)
ap≃-∔
  (Equivalence map₁ (Inverse post-inverse₁ is-post-inverse₁ pre-inverse₁ is-pre-inverse₁))
  (Equivalence map₂ (Inverse post-inverse₂ is-post-inverse₂ pre-inverse₂ is-pre-inverse₂))
  = Equivalence (map-∔ map₁ map₂)
       (Inverse (map-∔ post-inverse₁ post-inverse₂)
                (λ where
                  (inl+ x) → ap inl+ (is-post-inverse₁ _)
                  (inr+ x) → ap inr+ (is-post-inverse₂ _))
                (map-∔ pre-inverse₁ pre-inverse₂)
                (λ where
                  (inl+ x) → ap inl+ (is-pre-inverse₁ _)
                  (inr+ x) → ap inr+ (is-pre-inverse₂ _)))

_∙≃_ : A ≃ B → B ≃ C → A ≃ C
Equivalence map₁ (Inverse post-inverse₁ is-post-inverse₁ pre-inverse₁ is-pre-inverse₁)
  ∙≃ Equivalence map₂ (Inverse post-inverse₂ is-post-inverse₂ pre-inverse₂ is-pre-inverse₂)
  = Equivalence (map₂ ∘ map₁)
    (Inverse (post-inverse₁ ∘ post-inverse₂) (λ x → ap post-inverse₁ (is-post-inverse₂ (map₁ x)) ∙ is-post-inverse₁ x)
             (pre-inverse₁ ∘ pre-inverse₂) (λ x → ap map₂ (is-pre-inverse₁ (pre-inverse₂ x)) ∙ is-pre-inverse₂ x))

infixl 7 _∙≃_

J : {x : A} (P : (y : A) → x ≡ y → Type)
    (d : P x (refl x)) {y : A} (p : x ≡ y) → P y p
J P d (refl _) = d

ap≃-× : A ≃ B → C ≃ D → (A × C) ≃ (B × D)
ap≃-×
  (Equivalence map₁ (Inverse post-inverse₁ is-post-inverse₁ pre-inverse₁ is-pre-inverse₁))
  (Equivalence map₂ (Inverse post-inverse₂ is-post-inverse₂ pre-inverse₂ is-pre-inverse₂))
  = Equivalence (map-× map₁ map₂)
    (Inverse
      (map-× post-inverse₁ post-inverse₂)
      (λ x → ap₂ _,_ (is-post-inverse₁ _) (is-post-inverse₂ _))
      (map-× pre-inverse₁ pre-inverse₂)
      (λ x → ap₂ _,_ (is-pre-inverse₁ _) (is-pre-inverse₂ _))
    )


mkEquiv : ∀ {l1 l2 : Level} {A : Type l1} {B : Type l2}
          (f : A → B)
          (g : B → A)
          (fg : (g ∘ f) ∼ id)
          (gf : (f ∘ g) ∼ id)
        → A ≃ B
mkEquiv f g fg gf = improve (Isomorphism f (Inverse g fg gf))

mkIso : ∀ {l1 l2 : Level} {A : Type l1} {B : Type l2}
          (f : A → B)
          (g : B → A)
          (fg : (g ∘ f) ∼ id)
          (gf : (f ∘ g) ∼ id)
        → A ≅ B
mkIso f g fg gf = Isomorphism f (Inverse g fg gf)
