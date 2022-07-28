{-# OPTIONS --cubical --guarded -W ignore #-}
module combinations-of-lift-and-reader where

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

--*************************************************************--
--*************************************************************--
-- Combining the monads Lift and Reader via a distributive law --
--*************************************************************--
--*************************************************************--

-- In this document I want to the Lift monad and the Reader monad via a distributive law.
-- In order to do so, I will first define the the Reader monad, and check that it is indeed a monad.
-- I characterize its EM category by showing that each EM algebra is the same as an algebra with the operator lookup.
-- Then I define the distributive law, prove that it is a distributive law, and characterize the algebras by
-- showing that the resulting monad is the free monad of an algebraic theory in which time steps interact with lookups.

-- The Lift monad has aleady been defined in my earlier work, combinations-of-lift-and-list.
-- In the same file I check that lift is indeed a monad, and define various usefull functions, such as a map function for Lift.


--******************--
-- The Reader monad --
--******************--

Reader : Set → Set → Set
Reader S A = S → A

unitR : {A S : Set} → A → Reader S A
unitR a = λ s → a

multR : {A S : Set} → Reader S (Reader S A) → Reader S A
multR f = λ s → f s s

mapR : {A B S : Set} → (A → B) → Reader S A → Reader S B
mapR h f = λ s → h (f s)

-- Proving that Reader forms a monad

-- multR (unitR f) = f
Reader-unitlaw1 : {A S : Set} → ∀(f : Reader S A) → multR (unitR f) ≡ f
Reader-unitlaw1 f = refl

-- multR (mapR unitR f) = f
Reader-unitlaw2 : {A S : Set} → ∀(f : Reader S A) → multR (mapR unitR f) ≡ f
Reader-unitlaw2 f = refl

-- multR (multR f) = multR (mapR MultR f) 
Reader-multlaw : {A S : Set} → ∀(f : Reader S (Reader S (Reader S A))) →  multR (multR f) ≡ multR (mapR multR f)
Reader-multlaw f = refl

-- the unit is a natural transformation:
nattrans-unitR : {A B S : Set} → ∀(h : A → B) → ∀(a : A) → mapR {A}{B}{S} h (unitR a) ≡ unitR (h a)
nattrans-unitR h a = refl

-- the multiplication is a natural transformation:
nattrans-multR : {A B S : Set} → ∀(h : A → B) → ∀(f : Reader S (Reader S A)) → mapR h (multR f) ≡ multR (mapR (mapR h) f)
nattrans-multR h f = refl


--proving that reader is the free alg of lookup:

record IsLookup-alg {A S : Set} (lookupG : (S → A) → A) : Set where
  constructor isLookup-alg

  field
    lookup-const  : (a : A) → lookupG (λ s → a) ≡ a
    lookup-diag   : (g : S → S → A) → lookupG (mapR lookupG g) ≡ lookupG (λ s → g s s)

--showing that these are precisely the EM-algebras of the Reader monad:

record IsEM-algR {A S : Set} (h : (Reader S A) → A) : Set where
  constructor isemalg

  field
    id-compatibility   : (a : A) → h (unitR a) ≡ a
    mult-compatibility : (g : Reader S (Reader S A)) → h (multR g) ≡ h (mapR h g) 


EM-alg-is-lookupAlg : {A S : Set} → ∀(h : (Reader S A) → A) → IsEM-algR h → IsLookup-alg h 
IsLookup-alg.lookup-const (EM-alg-is-lookupAlg h isEMh) a = IsEM-algR.id-compatibility isEMh a
IsLookup-alg.lookup-diag (EM-alg-is-lookupAlg h isEMh) g = sym (IsEM-algR.mult-compatibility isEMh g)

lookupAlg-is-EM-alg : {A S : Set} → ∀(h : (Reader S A) → A) → IsLookup-alg h → IsEM-algR h
IsEM-algR.id-compatibility (lookupAlg-is-EM-alg h isLA) = IsLookup-alg.lookup-const isLA
IsEM-algR.mult-compatibility (lookupAlg-is-EM-alg h isLA) g = sym (IsLookup-alg.lookup-diag isLA g)


--****************************************************--
-- Composing Reader and Lift via a distributive law --
--****************************************************--

--We now define a composite monad of the Reader and Lift monads, formed via a distributive law.
RcL : (A S : Set) → (κ : Cl) → Set
RcL S A κ = Reader S (myLift A κ)

-- the unit of this monad is simply the composit of the units for Reader (unitR), and Lift (nowL)
unitRcL : {A S : Set} {κ : Cl} → A → (RcL S A κ) 
unitRcL a = unitR (nowL a)

-- RcL is a monad via a distributive law, distributing Lift over Reader.
-- Here is the distributive law:
distlawRcL : {A S : Set} {κ : Cl} → myLift (Reader S A) κ → (RcL S A κ)
distlawRcL (nowL f) = λ s → nowL (f s)
distlawRcL (stepL x) = λ s → stepL (λ α → distlawRcL (x α) s) 

--proof that distlawLcT is indeed a distributive law:
--unit laws:
unitlawRcL1 : {A S : Set} {κ : Cl} → ∀(f : Reader S A) → (distlawRcL {A}{S}{κ} (nowL f)) ≡  mapR (nowL) f
unitlawRcL1 f = refl 

unitlawRcL2 : {A S : Set} {κ : Cl} → ∀(x : myLift A κ) → (distlawRcL {A}{S}{κ} (mapL κ unitR x)) ≡ unitR x
unitlawRcL2 (nowL x) = refl
unitlawRcL2 {A}{S}{κ}(stepL x) = (λ i → λ s → stepL (λ α → unitlawRcL2 {A}{S}{κ} (x α) i s))

--multiplication laws:
multlawRcL1 : {A S : Set} {κ : Cl} → ∀(x : myLift (myLift (Reader S A) κ) κ) →
                                     distlawRcL {A}{S}{κ} (MultL κ x) ≡ mapR (MultL κ) (distlawRcL (mapL κ (distlawRcL) x))
multlawRcL1 (nowL x) = refl
multlawRcL1 (stepL x) = λ i → λ s → stepL (λ α → multlawRcL1 (x α) i s)

multlawLcT2 : {A S : Set} {κ : Cl} → ∀(x : myLift (Reader S (Reader S A)) κ) →
                                      distlawRcL (mapL κ multR x) ≡ multR (mapR distlawRcL (distlawRcL x))
multlawLcT2 (nowL x) = refl
multlawLcT2 (stepL x) = λ i → λ s → stepL (λ α → multlawLcT2 (x α) i s)

-- this yields a multiplication for RcL:
multRcL : {A S : Set} {κ : Cl} → RcL S (RcL S A κ) κ → RcL S A κ
multRcL {A}{S}{κ} ff = mapR (MultL κ) (multR (mapR distlawRcL ff))


--**************************--
-- Algebraic version of RcL --
--**************************--

-- defining the operators and equations for a "RcL algebra"
record RcL-alg-Data (A S : Set) (κ : Cl) : Set where
  constructor rclalgdata
  field
    lookupA : (S → A) → A
    stepA : ▹ κ A → A

record IsRcL-alg {A S : Set} {κ : Cl} (dm : RcL-alg-Data A S κ) : Set where
  constructor isRcL-alg

  open RcL-alg-Data dm
  field
    lookup-const  : (x : A) → lookupA (λ s → x) ≡ x
    lookup-diag   : (g : S → S → A) → lookupA (mapR lookupA g) ≡ lookupA (λ s → g s s)
    interact-sl   : (df : ▹ κ (S → A)) → stepA ((map▹ lookupA) df) ≡ lookupA (λ s → (stepA (λ α → (df α) s)))


-- RcL is an RcL algebra, with the following operations:
lookupRcL : {A S : Set} {κ : Cl} → (S → (RcL S A κ)) → (RcL S A κ) 
lookupRcL f = multRcL (λ s → nowL (f s))

stepRcL : {A S : Set} {κ : Cl} → ▹ κ (RcL S A κ) → RcL S A κ
stepRcL df = λ s → stepL (λ α → (df α) s)

RcLIsRcL-alg : {A S : Set} {κ : Cl} → IsRcL-alg {(RcL S A κ)}{S}{κ} (rclalgdata lookupRcL stepRcL)
IsRcL-alg.lookup-const RcLIsRcL-alg x = refl
IsRcL-alg.lookup-diag RcLIsRcL-alg g = refl
IsRcL-alg.interact-sl RcLIsRcL-alg df = refl

-- We want to show that RcL is the free such algebra.
-- We need to define what it means for a function to preserve the algebraic structure
-- and what it means for a function to extend a given function.

record IsPreservingRcL-alg {A B S : Set}{κ : Cl} (dmA : RcL-alg-Data A S κ) (dmB : RcL-alg-Data B S κ) (h : A → B) : Set where
  constructor ispreservingRcL-alg

  open RcL-alg-Data dmA
  open RcL-alg-Data dmB renaming (lookupA to lookupB; stepA to stepB)
  field
    lookup-preserve : (g : S → A) → h(lookupA g) ≡ lookupB (λ s → h (g s)) 
    step-preserve : (dx : ▹ κ A) → h (stepA dx) ≡ stepB (λ α → h (dx α))
    
record IsExtendingtoRcL {A B S : Set}{κ : Cl} (f : A → B) (h : (RcL S A κ) → B) : Set where
  constructor isextendingtoRcL

  field
    extendstoRcL : (x : A) → h (unitRcL x) ≡ (f x)

-- foldRcL defines the function we are after
fold-helper : {A B S : Set} {κ : Cl} → (dm : RcL-alg-Data B S κ) → IsRcL-alg dm → (A → B) → myLift A κ → B
fold-helper (rclalgdata lookupB stepB) isDMB f (nowL a) = f a
fold-helper (rclalgdata lookupB stepB) isDMB f (stepL x) = stepB (λ α → fold-helper ((rclalgdata lookupB stepB)) isDMB f (x α))

foldRcL : {A B S : Set}{κ : Cl} → isSet A → isSet B → (dm : RcL-alg-Data B S κ) → IsRcL-alg dm → (A → B) → (RcL S A κ) → B
foldRcL setA setB (rclalgdata lookupB stepB) isDMB f x = lookupB (λ s → fold-helper (rclalgdata lookupB stepB) isDMB f (x s))


--fold extends the function f : A → B
foldRcL-extends : {A B S : Set}{κ : Cl} → ∀(setA : isSet A) → ∀(setB : isSet B) → ∀(dm : RcL-alg-Data B S κ) → ∀(isDMB : IsRcL-alg dm) →
                   ∀ (f : A → B) → IsExtendingtoRcL f (foldRcL setA setB dm isDMB f)
IsExtendingtoRcL.extendstoRcL (foldRcL-extends setA setB dm isDMB f) x = IsRcL-alg.lookup-const isDMB (f x)


--foldRcL preseves the RcL algebra structure
module _ {A B S : Set}{κ : Cl} (setA : isSet A) (setB : isSet B) (dm : RcL-alg-Data B S κ) (isDMB : IsRcL-alg dm)
         (f : A → B)
 where
  open IsPreservingRcL-alg
  open RcL-alg-Data dm renaming (lookupA to lookupB; stepA to stepB)

  foldRcL-preserves : IsPreservingRcL-alg {(RcL S A κ)}{B}{S}{κ} (rclalgdata lookupRcL stepRcL) dm (foldRcL setA setB dm isDMB f)
  lookup-preserve foldRcL-preserves g = lookupB (λ s → fold-helper (rclalgdata lookupB stepB) isDMB f (g s s))
                                         ≡⟨ sym ( IsRcL-alg.lookup-diag isDMB ((λ s → (λ s₁ → fold-helper (rclalgdata lookupB stepB) isDMB f (g s s₁))))) ⟩
                                         lookupB (mapR lookupB (λ s → (λ s₁ → fold-helper (rclalgdata lookupB stepB) isDMB f (g s s₁))))
                                         ≡⟨ refl ⟩
                                         lookupB (λ s → lookupB (λ s₁ → fold-helper (rclalgdata lookupB stepB) isDMB f (g s s₁))) ∎
  step-preserve foldRcL-preserves dx = lookupB (λ s → stepB (λ α → fold-helper (rclalgdata lookupB stepB) isDMB f (dx α s)))
                                        ≡⟨ sym (IsRcL-alg.interact-sl isDMB ((λ α → (λ s → fold-helper (rclalgdata lookupB stepB) isDMB f (dx α s))))) ⟩
                                        stepB ((map▹ lookupB) (λ α → (λ s → fold-helper (rclalgdata lookupB stepB) isDMB f (dx α s)))) 
                                        ≡⟨ refl ⟩
                                        stepB (λ α → lookupB (λ s → fold-helper (rclalgdata lookupB stepB) isDMB f (dx α s))) ∎

-- and fold is unique in doing so. That is, for any function h that both preserves the algebra structure and extends the function f : A → B,
-- h is equivalent to fold.
  
-- First, I show that every x in RcL is of form lookupRcL followed by some StepRcL-s

transform-helper : {A S : Set} {κ : Cl} → myLift A κ → RcL S A κ
transform-helper (nowL a) = unitRcL a
transform-helper (stepL y) = stepRcL (λ α → transform-helper (y α))

transform : {A S : Set} {κ : Cl} → RcL S A κ → RcL S A κ
transform x = lookupRcL (λ s → transform-helper (x s))

lemma-transform-helper : {A S : Set} {κ : Cl} → ∀(y : myLift A κ) → ∀(s : S) → (transform-helper y) s ≡ (unitR y) s 
lemma-transform-helper (nowL y) s = refl
lemma-transform-helper (stepL y) s = cong stepL (later-ext(λ α → lemma-transform-helper (y α) s))

transform-x-is-x : {A S : Set} {κ : Cl} → ∀(x : RcL S A κ) → transform x ≡ x
transform-x-is-x x = funExt (λ s → lemma-transform-helper (x s) s)

-- Then I can show uniqueness
module _ {A B S : Set} {κ : Cl} (setA : isSet A) (setB : isSet B) (dm : RcL-alg-Data B S κ) (isDMB : IsRcL-alg dm)
                       (f : A → B) (h : RcL S A κ → B)
                       (isPDM : IsPreservingRcL-alg {RcL S A κ}{B}{S}{κ} (rclalgdata (lookupRcL) (stepRcL)) dm h)
                       (isExt : IsExtendingtoRcL f h) where

  open RcL-alg-Data dm renaming (lookupA to lookupB; stepA to stepB)

  fold-uniqueness-lemma : ∀(y : myLift A κ) → h(transform-helper y) ≡ fold-helper(rclalgdata lookupB stepB) isDMB f y
  fold-uniqueness-lemma (nowL y) = IsExtendingtoRcL.extendstoRcL isExt y
  fold-uniqueness-lemma (stepL y) =  h (stepRcL (λ α → transform-helper (y α)))
                                      ≡⟨ IsPreservingRcL-alg.step-preserve isPDM (λ α → transform-helper (y α)) ⟩
                                      stepB (λ α → h(transform-helper (y α)))
                                      ≡⟨ cong stepB (later-ext (λ α → fold-uniqueness-lemma (y α))) ⟩
                                      stepB (λ α → fold-helper (rclalgdata lookupB stepB) isDMB f (y α)) ∎

  fold-uniquenessRcL : ∀(x : (RcL S A κ)) → h x ≡ (foldRcL setA setB dm isDMB f x)
  fold-uniquenessRcL x = h x
                          ≡⟨ cong h (sym (transform-x-is-x x)) ⟩
                          h (transform x)
                          ≡⟨ refl ⟩
                          h(lookupRcL (λ s → transform-helper (x s)))
                          ≡⟨ IsPreservingRcL-alg.lookup-preserve isPDM (λ s → transform-helper (x s)) ⟩
                          lookupB (λ s → h(transform-helper (x s)))
                          ≡⟨ cong lookupB (funExt (λ s → fold-uniqueness-lemma (x s))) ⟩
                          lookupB (λ s → fold-helper (rclalgdata lookupB stepB) isDMB f (x s)) ∎


