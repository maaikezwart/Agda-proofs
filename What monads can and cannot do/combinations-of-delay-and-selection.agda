{-# OPTIONS --cubical --guarded -W ignore #-}
module combinations-of-delay-and-selection where

open import Clocked.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Prod

--*****************************************************************--
--*****************************************************************--
-- Combining the monads Delay and Selection via a distributive law --
--*****************************************************************--
--*****************************************************************--

-- In this document we combine the Delay monad and the Selection monad via a distributive law.
-- In order to do so, we will first define the the Selection monad, and check that it is indeed a monad.
-- Then we define the Delay monad, and check that it is indeed a monad.
-- Finally, we define the distributive law, prove that it is indeed a distributive law

--*********************--
-- The Selection monad --
--*********************--

Selection : Set → Set → Set
Selection S A = (A → S) → A

unitS : {A S : Set} → A → Selection S A
unitS a = λ g → a

multS : {A S : Set} → Selection S (Selection S A) → Selection S A
multS H = λ g → H (λ H' → g (H' g)) g

mapS : {A B S : Set} → (A → B) → Selection S A → Selection S B
mapS f h = λ g → f (h (λ a → g (f a)))

-- Proving that Selection forms a monad

-- multS (unitS f) = f
Selection-unitlaw1 : {A S : Set} → ∀(f : Selection S A) → multS (unitS f) ≡ f
Selection-unitlaw1 f = refl

-- multS (mapS unitS f) = f
Selection-unitlaw2 : {A S : Set} → ∀(f : Selection S A) → multS (mapS unitS f) ≡ f
Selection-unitlaw2 f = refl

-- multS (multS f) = multS (mapS MultS f) 
Selection-multlaw : {A S : Set} → ∀(f : Selection S (Selection S (Selection S A))) →  multS (multS f) ≡ multS (mapS multS f)
Selection-multlaw f = refl

-- the unit is a natural transformation:
nattrans-unitS : {A B S : Set} → ∀(h : A → B) → ∀(a : A) → mapS {A}{B}{S} h (unitS a) ≡ unitS (h a)
nattrans-unitS h a = refl

-- the multiplication is a natural transformation:
nattrans-multS : {A B S : Set} → ∀(h : A → B) → ∀(f : Selection S (Selection S A)) → mapS h (multS f) ≡ multS (mapS (mapS h) f)
nattrans-multS h f = refl



--******************--
--  The Delay monad --
--******************--

-- Defining the monad Delay.
-- (note that the return/unit is just x → nowD x)

data Delay (A : Set) (κ : Cl) : Set where
 nowD : A → (Delay A κ)
 stepD : ▹ κ (Delay A κ) → (Delay A κ) 

mapD : {A B : Set} (κ : Cl) → (A → B) → (Delay A κ) → (Delay B κ)
mapD κ f (nowD x) = nowD (f x)
mapD κ f (stepD x) = stepD (\ α →  mapD κ f (x α))

identity : {A : Set} → A → A
identity x = x

mapD-identity : {A : Set} {κ : Cl} → ∀ (x : Delay A κ) → mapD κ (λ y → y) x ≡ x
mapD-identity (nowD x) = refl
mapD-identity (stepD x) = cong stepD (later-ext λ α → mapD-identity (x α))

bindD : {A B : Set} (κ : Cl) → (A → (Delay B κ)) → Delay A κ → Delay B κ
bindD κ f (nowD a) = f a
bindD κ f (stepD x) = stepD \(α) → bindD κ f (x α)

MultD : {A : Set} (κ : Cl) → (Delay (Delay A κ) κ) → (Delay A κ)
MultD κ = bindD κ identity

-- Proving that Delay forms a monad

-- unit is a left-identity for bind: bind (f, return) = f
-- satisfied by definition of bind.

-- unit is a right-identity for bind: bind (return, x) = x
Delay-unitlaw2 : {A : Set}(κ : Cl) → ∀(x : (Delay A κ)) → (bindD {A} κ nowD x) ≡ x
Delay-unitlaw2 κ (nowD x) = refl
Delay-unitlaw2 κ (stepD x) = cong stepD (later-ext (\ α → Delay-unitlaw2 κ (x α)))

-- bind is associative: bind (\x ­> bind (g, f(x)), x) = bind(g,bind(f, x))
Delay-bindlaw : {A B C : Set}(κ : Cl) → ∀(f : A → (Delay B κ)) → ∀ (g : B → (Delay C κ)) →
                                                ∀ (y : (Delay A κ)) → (bindD κ (\ x → (bindD κ g (f x))) y) ≡ (bindD κ g (bindD κ f y))
Delay-bindlaw κ f g (nowD x) = refl
Delay-bindlaw κ f g (stepD x) = cong stepD (((later-ext (\ α → Delay-bindlaw κ f g (x α)))))



--*****************************************************--
-- Composing Selection and Delay via a distributive law --
--*****************************************************--

--We now define a composite monad of the Selection and Delay monads, formed via a distributive law.
ScD : (A S : Set) → (κ : Cl) → Set
ScD S A κ = Selection S (Delay A κ)

-- the unit of this monad is simply the composit of the units for Selection (unitS), and Lift (nowD)
unitScD : {A S : Set} {κ : Cl} → A → (ScD S A κ) 
unitScD a = unitS (nowD a)

-- ScD is a monad via a distributive law, distributing Lift over Selection.
-- Here is the distributive law:
distlawScD : {A S : Set} {κ : Cl} → Delay (Selection S A) κ → (ScD S A κ)
distlawScD (nowD h) = λ g → nowD (h (λ a → g (nowD a)))
distlawScD (stepD x) = λ g → stepD (λ α → (distlawScD (x α)) g)

--proof that distlawLcT is indeed a distributive law:
--unit laws:
unitlawScD1 : {A S : Set} {κ : Cl} → ∀(f : Selection S A) → (distlawScD {A}{S}{κ} (nowD f)) ≡  mapS (nowD) f
unitlawScD1 f = refl 

unitlawScD2 : {A S : Set} {κ : Cl} → ∀(x : Delay A κ) → (distlawScD {A}{S}{κ} (mapD κ unitS x)) ≡ unitS x
unitlawScD2 (nowD x) = refl
unitlawScD2 {A}{S}{κ}(stepD x) = (λ i → λ s → stepD (λ α → unitlawScD2 {A}{S}{κ} (x α) i s))

--multiplication laws:
multlawScD1 : {A S : Set} {κ : Cl} → ∀(x : Delay (Delay (Selection S A) κ) κ) →
                                     distlawScD {A}{S}{κ} (MultD κ x) ≡ mapS (MultD κ) (distlawScD (mapD κ (distlawScD) x))
multlawScD1 (nowD x) = refl
multlawScD1 (stepD x) = λ i → λ s → stepD (λ α → multlawScD1 (x α) i s)

multlawLcT2 : {A S : Set} {κ : Cl} → ∀(x : Delay (Selection S (Selection S A)) κ) →
                                      distlawScD (mapD κ multS x) ≡ multS (mapS distlawScD (distlawScD x))
multlawLcT2 (nowD x) = refl
multlawLcT2 (stepD x) = λ i → λ s → stepD (λ α → multlawLcT2 (x α) i s)

-- this yields a multiplication for ScD:
multScD : {A S : Set} {κ : Cl} → ScD S (ScD S A κ) κ → ScD S A κ
multScD {A}{S}{κ} ff = mapS (MultD κ) (multS (mapS distlawScD ff))
