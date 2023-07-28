{-# OPTIONS --cubical --guarded --rewriting -W ignore #-}

-- module DistHIT where

import Agda.Builtin.Equality as R
import Agda.Builtin.Equality.Rewrite as R

open import Agda.Primitive
open import Clocked.Primitives
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (Lift)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open Iso
open import Cubical.HITs.ListedFiniteSet
open import Cubical.Foundations.HLevels
open import Cubical.HITs.Rationals.QuoQ
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import RationalsExtra

-- Finite distribution HIT

data Dfin {ℓ} (A : Type ℓ) : Type ℓ where
  η     : (a : A) → Dfin A
  choose : (x y : Dfin A) (q : ℚ) → Dfin A
  comm : ∀ x y q → choose x y q ≡ choose y x (1ℚ - q)
  idem : ∀ x q → choose x x q ≡ x
  assoc : ∀ x y z p q r
    → (eq : r · (1ℚ - (p · q)) ≡ q · (1ℚ - p))
    → choose (choose x y p) z q ≡ choose x (choose y z r) (p · q)
  trunc : isSet (Dfin A)

-- Uniform distribution
uniform : ∀ {ℓ} {A : Type ℓ} → Dfin A → Dfin A → Dfin A
uniform x y = choose x y ½ 


-- Action on functions
mapDfin : ∀{ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → Dfin A → Dfin B
mapDfin f (η a) = η (f a)
mapDfin f (choose a b q) = choose (mapDfin f a) (mapDfin f b) q
mapDfin f (comm x y q i) =
  comm (mapDfin f x) (mapDfin f y) q i
mapDfin f (idem x q i) =
  idem (mapDfin f x) q i
mapDfin f (assoc x y z p q r eq i) =
  assoc (mapDfin f x) (mapDfin f y) (mapDfin f z) p q r eq i
mapDfin f (trunc x y p q i j) =
  trunc (mapDfin f x) (mapDfin f y) (cong (mapDfin f) p) (cong (mapDfin f) q) i j

-- Elimination under clocks for Dfin
module _ {ℓ} {ℓ'}
  {A : Cl → Type ℓ}
  {B : (∀ κ → Dfin (A κ)) → Type ℓ'}
  (setB : ∀ x → isSet (B x))
  (η* : (x : ∀ κ → A κ) → B (λ κ → η (x κ)))
  (choose* : {x y : ∀ κ → Dfin (A κ)} (x* : B x) (y* : B y) (q : ℚ)
    → B (λ κ → choose (x κ) (y κ) q))
  (comm* : {x y : ∀ κ → Dfin (A κ)} (x* : B x) (y* : B y) (q : ℚ)
    → PathP (λ i → B (λ κ → comm (x κ) (y κ) q i))
             (choose* x* y* q)
             (choose* y* x* (1ℚ - q)))
  (idem* : {x : ∀ κ → Dfin (A κ)} (x* : B x) (q : ℚ)
    → PathP (λ i → B (λ κ → idem (x κ) q i))
             (choose* x* x* q)
             x*)
  (assoc* : {x y z : ∀ κ → Dfin (A κ)} (x* : B x) (y* : B y) (z* : B z) (p q r : ℚ)
    → (eq : r · (1ℚ - (p · q)) ≡ q · (1ℚ - p))
    → PathP (λ i → B (λ κ → assoc (x κ) (y κ) (z κ) p q r eq i))
             (choose* (choose* x* y* p) z* q)
             (choose* x* (choose* y* z* r) (p · q)))
  where

  postulate
    elimDfin∀ : ∀ x → B x

    elimDfin∀-η : (x : ∀ κ → A κ) → elimDfin∀ (λ κ → η (x κ)) R.≡ η* x
    elimDfin∀-choose : (x y : ∀ κ → Dfin (A κ)) {q : ℚ}
      → elimDfin∀ (λ κ → choose (x κ) (y κ) q)
             R.≡ choose* (elimDfin∀ x) (elimDfin∀ y) q

  {-# REWRITE elimDfin∀-η elimDfin∀-choose #-}

-- Recursion under clocks for Dfin
module _ {ℓ} {ℓ'}
  {A : Cl → Type ℓ}
  {B : Type ℓ'}
  (setB : isSet B)
  (η* : (∀ κ → A κ) → B)
  (choose* : (x* y* : B) (q : ℚ) → B)
  (comm* : (x* y* : B) (q : ℚ) → choose* x* y* q ≡ choose* y* x* (1ℚ - q))
  (idem* : (x* : B) (q : ℚ) → choose* x* x* q ≡ x*)
  (assoc* : (x* y* z* : B) (p q r : ℚ)
    → (eq : r · (1ℚ - (p · q)) ≡ q · (1ℚ - p))
    → choose* (choose* x* y* p) z* q  ≡ choose* x* (choose* y* z* r) (p · q))
  where

  recDfin∀ : (∀ κ → Dfin (A κ)) → B
  recDfin∀ = elimDfin∀ {B = λ _ → B} (λ _ → setB) η* choose* comm* idem* assoc*

-- Elimination under clocks into a proposition for Dfin
module _ {ℓ} {ℓ'}
  {A : Cl → Type ℓ}
  {B : (∀ κ → Dfin (A κ)) → Type ℓ'}
  (propB : ∀ x → isProp (B x))
  (η* : (x : ∀ κ → A κ) → B (λ κ → η (x κ)))
  (choose* : {x y : ∀ κ → Dfin (A κ)} (x* : B x) (y* : B y) (q : ℚ)
    → B (λ κ → choose (x κ) (y κ) q))
  where

  elimDfin∀Prop : ∀ x → B x
  elimDfin∀Prop =
    elimDfin∀ (λ _ → isProp→isSet (propB _)) η* choose*
      (λ _ _ _ → isProp→PathP (λ i → propB _) _ _)
      (λ _ _ → isProp→PathP (λ i → propB _) _ _)
      (λ _ _ _ _ _ _ _ → isProp→PathP (λ i → propB _) _ _)

-- Usual elimination and recursion principles for Dfin
module _ {ℓ} {ℓ'}
  {A : Type ℓ}
  {B : Dfin A → Type ℓ'}
  (setB : ∀ x → isSet (B x))
  (η* : (x : A) → B (η x))
  (choose* : {x y : Dfin A} (x* : B x) (y* : B y) (q : ℚ) → B (choose x y q))
  (comm* : {x y : Dfin A} (x* : B x) (y* : B y) (q : ℚ)
    → PathP (λ i → B (comm x y q i))
             (choose* x* y* q)
             (choose* y* x* (1ℚ - q)))
  (idem* : {x : Dfin A} (x* : B x) (q : ℚ)
    → PathP (λ i → B (idem x q i))
             (choose* x* x* q)
             x*)
  (assoc* : {x y z : Dfin A} (x* : B x) (y* : B y) (z* : B z) (p q r : ℚ)
    → (eq : r · (1ℚ - (p · q)) ≡ q · (1ℚ - p))
    → PathP (λ i → B (assoc x y z p q r eq i))
             (choose* (choose* x* y* p) z* q)
             (choose* x* (choose* y* z* r) (p · q)))
  where

  elimDfin : ∀ x → B x
  elimDfin (η a) = η* a
  elimDfin (choose x y q) = choose* (elimDfin x) (elimDfin y) q
  elimDfin (comm x y q i) = comm* (elimDfin x) (elimDfin y) q i
  elimDfin (idem x q i) = idem* (elimDfin x) q i
  elimDfin (assoc x y z p q r eq i) = assoc* (elimDfin x) (elimDfin y) (elimDfin z) p q r eq i
  elimDfin (trunc x y e f i j) =
    isOfHLevel→isOfHLevelDep 2 setB
      (elimDfin x) (elimDfin y)
      (cong elimDfin e) (cong elimDfin f) (trunc x y e f) i j

module _ {ℓ} {ℓ'}
  {A : Type ℓ} {B : Type ℓ'}
  (setB : isSet B)
  (η* : A → B)
  (choose* : (x* y* : B) (q : ℚ) → B)
  (comm* : (x* y* : B) (q : ℚ) → choose* x* y* q ≡ choose* y* x* (1ℚ - q))
  (idem* : (x* : B) (q : ℚ) → choose* x* x* q ≡ x*)
  (assoc* : (x* y* z* : B) (p q r : ℚ)
    → (eq : r · (1ℚ - (p · q)) ≡ q · (1ℚ - p))
    → choose* (choose* x* y* p) z* q  ≡ choose* x* (choose* y* z* r) (p · q))
  where

  recDfin : Dfin A → B
  recDfin = elimDfin {B = λ _ → B} (λ _ → setB) η* choose* comm* idem* assoc* 

module _ {ℓ} {ℓ'}
  {A : Type ℓ}
  {B : Dfin A → Type ℓ'}
  (propB : ∀ x → isProp (B x))
  (η* : (x : A) → B (η x))
  (choose* : {x y : Dfin A} (x* : B x) (y* : B y) (q : ℚ) → B (choose x y q))
  where

  elimDfinProp : ∀ x → B x
  elimDfinProp =
    elimDfin (λ x → isProp→isSet (propB x)) η* choose*
      (λ _ _ _ → isProp→PathP (λ i → propB _) _ _)
      (λ _ _ → isProp→PathP (λ i → propB _) _ _)
      (λ _ _ _ _ _ _ _ → isProp→PathP (λ i → propB _) _ _)

-- Dfin commutes with ∀ κ
dist∀Dfin : ∀ {ℓ} {A : Cl → Type ℓ} → (∀ κ → Dfin (A κ)) → Dfin (∀ κ → A κ)
dist∀Dfin = recDfin∀ trunc η choose comm idem assoc

iso∀Dfin : ∀ {ℓ} {A : Cl → Type ℓ} → Iso (∀ κ → Dfin (A κ)) (Dfin (∀ κ → A κ))
fun iso∀Dfin = dist∀Dfin
inv iso∀Dfin x κ = mapDfin (λ g → g κ) x
rightInv iso∀Dfin =
  elimDfinProp (λ _ → trunc _ _)
    (λ _ → refl)
    (λ ih1 ih2 q i → choose (ih1 i) (ih2 i) q)
leftInv iso∀Dfin =
  elimDfin∀Prop (λ _ p q i j κ → trunc _ _ (λ i → p i κ) (λ i → q i κ) i j)
    (λ _ → refl)
    (λ ih1 ih2 q i κ → choose (ih1 i κ) (ih2 i κ) q)

-- Kleisli lifing
liftDfin : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (A → Dfin B) → Dfin A → Dfin B
liftDfin f = recDfin trunc f choose comm idem assoc

-- The Dfin-algebra on ℚ
probLift : ∀ {ℓ} {A : Type ℓ} (f : A → ℚ) → Dfin A → ℚ
probLift f = recDfin isSetℚ f line line-comm line-idem line-assoc

probEvent : ∀ {ℓ} {A : Type ℓ} (E : A → Bool) → Dfin A → ℚ
probEvent E = probLift (λ a → if E a then 1ℚ else 0ℚ)

probLiftTotal : ∀ {ℓ} {A : Type ℓ} (x : Dfin A) → probLift (λ _ → 1ℚ) x ≡ 1ℚ
probLiftTotal =
  elimDfinProp (λ _ → isSetℚ _ _) (λ _ → refl)
    (λ {x = x}{y} eq eq' q →
      line (probLift (λ _ → 1ℚ) x) (probLift (λ _ → 1ℚ) y) q
        ≡⟨ cong₂ (λ a b → line a b q) eq eq' ⟩
      line 1ℚ 1ℚ q
        ≡⟨ line-idem 1ℚ q ⟩
      1ℚ
        ∎)

-- functor laws
mapDfin-id : ∀{ℓ} {A : Type ℓ} (x : Dfin A) → mapDfin (λ a → a) x ≡ x
mapDfin-id =
  elimDfinProp (λ _ → trunc _ _)
    (λ _ → refl)
    (λ eqx eqy q i → choose (eqx i) (eqy i) q)

mapDfin-comp : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  → (g : B → C) (f : A → B) (x : Dfin A)
  → mapDfin (λ a → g (f a)) x ≡ mapDfin g (mapDfin f x)
mapDfin-comp g f =
  elimDfinProp (λ _ → trunc _ _)
    (λ _ → refl)
    (λ eqx eqy q i → choose (eqx i) (eqy i) q)

mapDfin-iso : ∀{ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → Iso A B → Iso (Dfin A) (Dfin B)
fun (mapDfin-iso f) = mapDfin (f .fun)
inv (mapDfin-iso f) = mapDfin (f .inv)
rightInv (mapDfin-iso f) y =
  sym (mapDfin-comp (f .fun) (f .inv) y)
  ∙ cong (λ g → mapDfin g y) (funExt (f .rightInv))
  ∙ mapDfin-id y
leftInv (mapDfin-iso f) x =
  sym (mapDfin-comp (f .inv) (f .fun) x)
  ∙ cong (λ g → mapDfin g x) (funExt (f .leftInv))
  ∙ mapDfin-id x

mapDfin-≃ : ∀{ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → A ≃ B → Dfin A ≃ Dfin B
mapDfin-≃ f = isoToEquiv (mapDfin-iso (equivToIso f))  
