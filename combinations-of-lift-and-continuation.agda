{-# OPTIONS --cubical --guarded -W ignore #-}
module combinations-of-lift-and-continuation where

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
open import combinations-of-lift-and-list

--**********************************************************--
--**********************************************************--
-- Combining the monads Lift and Continuation via Selection --
--**********************************************************--
--**********************************************************--

-- In this document I want to the Lift monad and the Continuation monad via a distributive law and the Selection monad.
-- In order to do so, I will first define the the Selection and Continuation monads, and check that they are indeed a monads.

-- The Lift monad has aleady been defined in my earlier work, combinations-of-lift-and-list.
-- In the same file I check that lift is indeed a monad, and define various usefull functions, such as a map function for Lift.


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


--************************--
-- The Continuation monad --
--************************--

Continuation : Set → Set → Set
Continuation S A = (A → S) → S

unitC : {A S : Set} → A → Continuation S A
unitC a = λ g → g a

multC : {A S : Set} → Continuation S (Continuation S A) → Continuation S A
multC H = λ g → H (λ H' → H' g)

mapC : {A B S : Set} → (A → B) → Continuation S A → Continuation S B
mapC f h = λ g → h (λ a → g (f a))

-- Proving that Continuation forms a monad

-- multC (unitC f) = f
Continuation-unitlaw1 : {A S : Set} → ∀(f : Continuation S A) → multC (unitC f) ≡ f
Continuation-unitlaw1 f = refl

-- multC (mapC unitC f) = f
Continuation-unitlaw2 : {A S : Set} → ∀(f : Continuation S A) → multC (mapC unitC f) ≡ f
Continuation-unitlaw2 f = refl

-- multC (multC f) = multC (mapC MultC f) 
Continuation-multlaw : {A S : Set} → ∀(f : Continuation S (Continuation S (Continuation S A))) →  multC (multC f) ≡ multC (mapC multC f)
Continuation-multlaw f = refl

-- the unit is a natural transformation:
nattrans-unitC : {A B S : Set} → ∀(h : A → B) → ∀(a : A) → mapC {A}{B}{S} h (unitC a) ≡ unitC (h a)
nattrans-unitC h a = refl

-- the multiplication is a natural transformation:
nattrans-multC : {A B S : Set} → ∀(h : A → B) → ∀(f : Continuation S (Continuation S A)) → mapC h (multC f) ≡ multC (mapC (mapC h) f)
nattrans-multC h f = refl



--*****************************************************--
-- Composing Selection and Lift via a distributive law --
--*****************************************************--

--We now define a composite monad of the Selection and Lift monads, formed via a distributive law.
ScL : (A S : Set) → (κ : Cl) → Set
ScL S A κ = Selection S (myLift A κ)

-- the unit of this monad is simply the composit of the units for Selection (unitS), and Lift (nowL)
unitScL : {A S : Set} {κ : Cl} → A → (ScL S A κ) 
unitScL a = unitS (nowL a)

-- ScL is a monad via a distributive law, distributing Lift over Selection.
-- Here is the distributive law:
distlawScL : {A S : Set} {κ : Cl} → myLift (Selection S A) κ → (ScL S A κ)
distlawScL (nowL h) = λ g → nowL (h (λ a → g (nowL a)))
distlawScL (stepL x) = λ g → stepL (λ α → (distlawScL (x α)) g)

--or:
--distlawScL' : {A S : Set} {κ : Cl} → myLift (Selection S A) κ → (ScL S A κ)
--distlawScL' (nowL h) = λ g → nowL (h (λ a → g (nowL a)))
--distlawScL' (stepL x) = λ g → stepL (λ α → (distlawScL (x α)) (gstep g))
--                           where gstep : {A S : Set}{κ : Cl} → (myLift A κ → S) → (myLift A κ → S) 
--                                gstep g da = g (stepL (λ α → da))
--This seemed better on paper, but it does not satisfy the axioms of a distributive law. Only the first unitlaw, none of the others.

--proof that distlawLcT is indeed a distributive law:
--unit laws:
unitlawScL1 : {A S : Set} {κ : Cl} → ∀(f : Selection S A) → (distlawScL {A}{S}{κ} (nowL f)) ≡  mapS (nowL) f
unitlawScL1 f = refl 

unitlawScL2 : {A S : Set} {κ : Cl} → ∀(x : myLift A κ) → (distlawScL {A}{S}{κ} (mapL κ unitS x)) ≡ unitS x
unitlawScL2 (nowL x) = refl
unitlawScL2 {A}{S}{κ}(stepL x) = (λ i → λ s → stepL (λ α → unitlawScL2 {A}{S}{κ} (x α) i s))

--multiplication laws:
multlawScL1 : {A S : Set} {κ : Cl} → ∀(x : myLift (myLift (Selection S A) κ) κ) →
                                     distlawScL {A}{S}{κ} (MultL κ x) ≡ mapS (MultL κ) (distlawScL (mapL κ (distlawScL) x))
multlawScL1 (nowL x) = refl
multlawScL1 (stepL x) = λ i → λ s → stepL (λ α → multlawScL1 (x α) i s)

multlawLcT2 : {A S : Set} {κ : Cl} → ∀(x : myLift (Selection S (Selection S A)) κ) →
                                      distlawScL (mapL κ multS x) ≡ multS (mapS distlawScL (distlawScL x))
multlawLcT2 (nowL x) = refl
multlawLcT2 (stepL x) = λ i → λ s → stepL (λ α → multlawLcT2 (x α) i s)

-- this yields a multiplication for ScL:
multScL : {A S : Set} {κ : Cl} → ScL S (ScL S A κ) κ → ScL S A κ
multScL {A}{S}{κ} ff = mapS (MultL κ) (multS (mapS distlawScL ff))



--*****************************************--
-- Combining Continuation and Lift via ScL --
--*****************************************--

--There is a monad morphism from the selection monad to the continuation monad, which is defined as follows:
--(Citation: Nlab)

S→C : {A S : Set} → Selection S A → Continuation S A
S→C h = λ g → g (h g)

--Using this morhpism, we can define a combination of the Lift monad with the continuation monad, which might be a distributive law?

CcL : (A S : Set) → (κ : Cl) → Set
CcL S A κ = Continuation S (myLift A κ)

unitCcL : {A S : Set} {κ : Cl} → A → (CcL S A κ) 
unitCcL a = unitC (nowL a)

--distlawCcL : {A S : Set} {κ : Cl} → myLift (Continuation S A) κ → (CcL S A κ)
--distlawCcL (nowL h) = S→C (distlawScL (nowL (λ g → {!!})))
--distlawCcL (stepL x) = {!!}

-- --proof that distlawLcT is indeed a distributive law:
-- --unit laws:
-- unitlawScL1 : {A S : Set} {κ : Cl} → ∀(f : Selection S A) → (distlawScL {A}{S}{κ} (nowL f)) ≡  mapS (nowL) f
-- unitlawScL1 f = refl 

-- unitlawScL2 : {A S : Set} {κ : Cl} → ∀(x : myLift A κ) → (distlawScL {A}{S}{κ} (mapL κ unitS x)) ≡ unitS x
-- unitlawScL2 (nowL x) = refl
-- unitlawScL2 {A}{S}{κ}(stepL x) = (λ i → λ s → stepL (λ α → unitlawScL2 {A}{S}{κ} (x α) i s))

-- --multiplication laws:
-- multlawScL1 : {A S : Set} {κ : Cl} → ∀(x : myLift (myLift (Selection S A) κ) κ) →
--                                      distlawScL {A}{S}{κ} (MultL κ x) ≡ mapS (MultL κ) (distlawScL (mapL κ (distlawScL) x))
-- multlawScL1 (nowL x) = refl
-- multlawScL1 (stepL x) = λ i → λ s → stepL (λ α → multlawScL1 (x α) i s)

-- multlawLcT2 : {A S : Set} {κ : Cl} → ∀(x : myLift (Selection S (Selection S A)) κ) →
--                                       distlawScL (mapL κ multS x) ≡ multS (mapS distlawScL (distlawScL x))
-- multlawLcT2 (nowL x) = refl
-- multlawLcT2 (stepL x) = λ i → λ s → stepL (λ α → multlawLcT2 (x α) i s)

-- -- this yields a multiplication for ScL:
-- multScL : {A S : Set} {κ : Cl} → ScL S (ScL S A κ) κ → ScL S A κ
-- multScL {A}{S}{κ} ff = mapS (MultL κ) (multS (mapS distlawScL ff))

