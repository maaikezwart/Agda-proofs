{-# OPTIONS --cubical --guarded -W ignore #-}
module combinations-of-delay-and-exception where

open import Clocked.Primitives
open import Cubical.Foundations.Everything
open import Cubical.Data.List as List
open import Cubical.Data.List.Properties
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import combinations-of-lift-and-list

--****************************************************************************--
--****************************************************************************--
-- Combining the monads Delay and Exception freely and via a distributive law --
--****************************************************************************--
--****************************************************************************--

-- In this document I want to define a monad, called ExceptDelay, that is the free combination of the Delay monad and the Exception monad.
-- In order to do so, I will first define the the Exception monad, and check that it is indeed a monad.
-- 
-- Then I define the ExceptLift monad, check that it is a monad.
-- Finally, I also compose the two monads via a distributive law:
-- LcE : A → Lift(Except A), via DistEL : Except (Lift A) → Lift (Except A).

-- The Lift monad has aleady been defined in my earlier work, combinations-of-lift-and-list.
-- In the same file I check that lift is indeed a monad, and define various usefull functions, such as a map function for Lift.

--*********************--
-- The Exception monad --
--*********************--

Exception : (A E : Set) → Set
Exception A E = A ⊎ E

-- map function for Exception
mapE : {A B E : Set} → (A → B) → Exception A E → Exception B E
mapE f (inl a) = inl (f a)
mapE f (inr e) = inr e

-- unit and multiplication functions for Exception
unitE : {A E : Set} → A → Exception A E
unitE a = inl a

multE : {A E : Set} → Exception (Exception A E) E → Exception A E
multE (inl x) = x
multE (inr e) = inr e

-- Proving that the Exception forms a monad

-- multE (unitE x) = x
Exception-unitlaw1 : {A E : Set} → ∀(x : Exception A E) → multE (unitE x) ≡ x
Exception-unitlaw1 x = refl

-- multE (mapE unitE x) = x
Exception-unitlaw2 : {A E : Set} → ∀(x : Exception A E) → multE (mapE unitE x) ≡ x
Exception-unitlaw2 (inl a) = refl
Exception-unitlaw2 (inr e) = refl 
 
-- multE (multE x) = multE (mapE multE x) 
Exception-multlaw : {A E : Set} → ∀(x : Exception (Exception (Exception A E) E) E) →  multE (multE x) ≡ multE (mapE multE x)
Exception-multlaw (inl x) = refl
Exception-multlaw (inr e) = refl

-- the unit is a natural transformation:
nattrans-unitE : {A B E : Set} → ∀(f : A → B) → ∀(a : A) → mapE {A}{B}{E} f (unitE a) ≡ unitE (f a)
nattrans-unitE f a = refl

-- the multiplication is a natural transformation:
nattrans-MultE : {A B E : Set} → ∀(f : A → B) → ∀(x : Exception (Exception A E) E) → mapE f (multE x) ≡ multE (mapE (mapE f) x)
nattrans-MultE f (inl x) = refl
nattrans-MultE f (inr e) = refl

--***********************--
-- The ExceptDelay monad --
--***********************--

--Now that we have a Exception monad and a Lift monad, we want to show that the following combination of the two is again a monad:
--ExceptLift : (A E : Set) → (κ : Cl) → Set
--ExceptLift A E κ = Exception (A ⊎ (▹ κ (ExceptLift A κ))) E

data ExceptLift (A E : Set) (κ : Cl) : Set where
  conEL : Exception (A ⊎ (▹ κ (ExceptLift A E κ))) E -> ExceptLift A E κ

--***algebraic structure for ExceptLift***--

--nowEL and stepEL turn ExceptLift into a delay algebra structure:
nowEL : {A E : Set} {κ : Cl} → A → (ExceptLift A E κ)
nowEL a = conEL (unitE (inl a))

stepEL : {A E : Set} {κ : Cl} → ▹ κ (ExceptLift A E κ) → (ExceptLift A E κ)
stepEL a = conEL (unitE (inr a))

--***monadic structure for ExceptLift***--

--a map function to turn ExceptLift into a functor
mapEL : {A B E : Set}{κ : Cl} → (f : A → B) → (ExceptLift A E κ) → (ExceptLift B E κ)
mapEL f (conEL (inl (inl a))) = conEL (inl (inl (f a)))
mapEL f (conEL (inl (inr x))) = stepEL (λ α → mapEL f (x α))
mapEL f (conEL (inr e)) = conEL (inr e)

--a bind operator to make ExceptLift into a monad
bindEL : {A B E : Set}{κ : Cl} → (A → (ExceptLift B E κ)) → ExceptLift A E κ → ExceptLift B E κ
bindEL f (conEL (inl (inl a))) = f a
bindEL f (conEL (inl (inr x))) = stepEL (λ α → bindEL f (x α))
bindEL f (conEL (inr e)) = conEL (inr e)

--***proof that ExceptLift is a monad***--

--bindEL and nowEL need to be natural transformations
nattrans-nowEL : {A B E : Set}{κ : Cl} → ∀(f : A → B) → ∀(a : A) → mapEL {A}{B}{E}{κ} f (nowEL a) ≡ nowEL (f a)
nattrans-nowEL f a = refl

-- -- TODO: bindML

-- bindEL and nowEL also need to satisfy three monad laws:
-- unit is a left-identity for bind
unitlawEL1 : {A B E : Set}{κ : Cl} → ∀ (f : A → (ExceptLift B E κ)) → ∀ (a : A) → (bindEL {A}{B}{E}{κ} f (nowEL a)) ≡ f a
unitlawEL1 f a = refl

-- unit is a right-identity for bind
unitlawEL2 : {A E : Set}{κ : Cl} → ∀(x : (ExceptLift A E κ)) → (bindEL nowEL x) ≡ x
unitlawEL2 (conEL (inl (inl a))) = refl
unitlawEL2 (conEL (inl (inr x))) = cong stepEL (later-ext (λ α → unitlawEL2 (x α)))
unitlawEL2 (conEL (inr e)) = refl

-- bind is associative
assoclawEL : {A B C E : Set}{κ : Cl} → ∀(f : A → (ExceptLift B E κ)) → ∀ (g : B → (ExceptLift C E κ)) → ∀ (x : (ExceptLift A E κ))
                                     → (bindEL (\ y → (bindEL g (f y))) x) ≡ (bindEL g (bindEL f x))
assoclawEL {A}{B}{C}{E}{κ} f g (conEL (inl (inl a))) = refl
assoclawEL {A}{B}{C}{E}{κ} f g (conEL (inl (inr x))) = cong stepEL (later-ext (λ α → assoclawEL f g (x α)))
assoclawEL {A}{B}{C}{E}{κ} f g (conEL (inr e)) = refl


--****************************************************--
-- Composing Lift and Exception via a distributive law --
--****************************************************--

--We now define a composite monad of the Exception and Lift monads, formed via a distributive law.
LcE : (A E : Set) → (κ : Cl) → Set
LcE A E κ = myLift (Exception A E) κ

-- the unit of this monad is simply the composit of the units for Lift (nowL x) and Exception (unitM)
unitLcE : {A E : Set} {κ : Cl} → A → (LcE A E κ) 
unitLcE a = nowL (unitE a)

-- LcM is a monad via a distributive law, distributing Exception over Lift.
-- Here is the distributive law (it is a very stupid one):
distlawLcE : {A E : Set} {κ : Cl} → Exception (myLift A κ) E → (LcE A E κ)
distlawLcE (inl (nowL a)) = nowL (inl a)
distlawLcE (inl (stepL x)) = stepL (λ α → distlawLcE (inl (x α)))
distlawLcE (inr e) = nowL (inr e)

--proof that distlawLcM is indeed a distributive law:
--unit laws:
unitlawLcE1 : {A E : Set} {κ : Cl} → ∀(x : myLift A κ) → (distlawLcE{A}{E} (unitE x)) ≡  mapL κ unitE x
unitlawLcE1 (nowL x) = refl
unitlawLcE1 (stepL x) = cong stepL (later-ext λ α → unitlawLcE1 (x α))

unitlawLcE2 : {A E : Set} {κ : Cl} → ∀(x : Exception A E) → (distlawLcE {A}{E}{κ} (mapE nowL x)) ≡ nowL x
unitlawLcE2 (inl a) = refl
unitlawLcE2 (inr e) = refl

--multiplication laws:
multlawLcE1 : {A E : Set}{κ : Cl} → ∀(x : Exception (Exception (myLift A κ) E) E) → distlawLcE (multE x) ≡
                                                                                    mapL κ multE (distlawLcE (mapE distlawLcE x))
multlawLcE1 (inl (inl (nowL a))) = refl
multlawLcE1 (inl (inl (stepL x))) = cong stepL (later-ext (λ α → multlawLcE1 (inl (inl (x α)))))
multlawLcE1 (inl (inr e)) = refl
multlawLcE1 (inr e) = refl

multlawLcE2 : {A E : Set} {κ : Cl} → ∀(x : Exception (myLift (myLift A κ) κ) E) →
                                     distlawLcE (mapE (MultL κ) x) ≡ MultL κ (mapL κ distlawLcE (distlawLcE x))
multlawLcE2 (inl (nowL (nowL x))) = refl
multlawLcE2 (inl (nowL (stepL x))) = refl
multlawLcE2 (inl (stepL x)) = cong stepL (later-ext (λ α → multlawLcE2 (inl (x α))))
multlawLcE2 (inr e) = refl
