{-# OPTIONS --cubical --guarded -W ignore #-}
module combinations-of-delay-and-reader where

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

--**************************************************************--
--**************************************************************--
-- Combining the monads Delay and Reader via a distributive law --
--**************************************************************--
--**************************************************************--

-- In this document we combine the Delay monad and the Reader monad via a distributive law.
-- In order to do so, we will first define the the Reader monad, and check that it is indeed a monad.
-- We characterize its EM category by showing that each EM algebra is the same as an algebra with the operator lookup.
-- Then we define the Delay monad, and check that it is indeed a monad.
-- Finally we define the distributive law, prove that it is a distributive law, and characterize the algebras by
-- showing that the resulting monad is the free monad of an algebraic theory in which steps interact with lookups.


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


--proving that reader is the free algebra of lookup:

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



--***************************************************--
-- Composing Reader and Delay via a distributive law --
--***************************************************--

--We now define a composite monad of the Reader and Delay monads, formed via a distributive law.
RcD : (A S : Set) → (κ : Cl) → Set
RcD S A κ = Reader S (Delay A κ)

-- the unit of this monad is simply the composit of the units for Reader (unitR), and Delay (nowD)
unitRcD : {A S : Set} {κ : Cl} → A → (RcD S A κ) 
unitRcD a = unitR (nowD a)

-- RcD is a monad via a distributive law, distributing Reader over Delay.
-- Here is the distributive law:
distlawRcD : {A S : Set} {κ : Cl} → Delay (Reader S A) κ → (RcD S A κ)
distlawRcD (nowD f) = λ s → nowD (f s)
distlawRcD (stepD x) = λ s → stepD (λ α → distlawRcD (x α) s) 

--proof that distlawRcD is indeed a distributive law:
--unit laws:
unitlawRcD1 : {A S : Set} {κ : Cl} → ∀(f : Reader S A) → (distlawRcD {A}{S}{κ} (nowD f)) ≡  mapR (nowD) f
unitlawRcD1 f = refl 

unitlawRcD2 : {A S : Set} {κ : Cl} → ∀(x : Delay A κ) → (distlawRcD {A}{S}{κ} (mapD κ unitR x)) ≡ unitR x
unitlawRcD2 (nowD x) = refl
unitlawRcD2 {A}{S}{κ}(stepD x) = (λ i → λ s → stepD (λ α → unitlawRcD2 {A}{S}{κ} (x α) i s))

--multiplication laws:
multlawRcD1 : {A S : Set} {κ : Cl} → ∀(x : Delay (Delay (Reader S A) κ) κ) →
                                     distlawRcD {A}{S}{κ} (MultD κ x) ≡ mapR (MultD κ) (distlawRcD (mapD κ (distlawRcD) x))
multlawRcD1 (nowD x) = refl
multlawRcD1 (stepD x) = λ i → λ s → stepD (λ α → multlawRcD1 (x α) i s)

multlawLcT2 : {A S : Set} {κ : Cl} → ∀(x : Delay (Reader S (Reader S A)) κ) →
                                      distlawRcD (mapD κ multR x) ≡ multR (mapR distlawRcD (distlawRcD x))
multlawLcT2 (nowD x) = refl
multlawLcT2 (stepD x) = λ i → λ s → stepD (λ α → multlawLcT2 (x α) i s)

-- this yields a multiplication for RcD:
multRcD : {A S : Set} {κ : Cl} → RcD S (RcD S A κ) κ → RcD S A κ
multRcD {A}{S}{κ} ff = mapR (MultD κ) (multR (mapR distlawRcD ff))


--**************************--
-- Algebraic version of RcD --
--**************************--

-- defining the operators and equations for an "RcD algebra"
record RcD-alg-Data (A S : Set) (κ : Cl) : Set where
  constructor rcdalgdata
  field
    lookupA : (S → A) → A
    stepA : ▹ κ A → A

record IsRcD-alg {A S : Set} {κ : Cl} (dm : RcD-alg-Data A S κ) : Set where
  constructor isRcD-alg

  open RcD-alg-Data dm
  field
    lookup-const  : (x : A) → lookupA (λ s → x) ≡ x
    lookup-diag   : (g : S → S → A) → lookupA (mapR lookupA g) ≡ lookupA (λ s → g s s)
    interact-sl   : (df : ▹ κ (S → A)) → stepA ((map▹ lookupA) df) ≡ lookupA (λ s → (stepA (λ α → (df α) s)))


-- RcD is an RcD algebra, with the following operations:
lookupRcD : {A S : Set} {κ : Cl} → (S → (RcD S A κ)) → (RcD S A κ) 
lookupRcD f = multRcD (λ s → nowD (f s))

stepRcD : {A S : Set} {κ : Cl} → ▹ κ (RcD S A κ) → RcD S A κ
stepRcD df = λ s → stepD (λ α → (df α) s)

RcDIsRcD-alg : {A S : Set} {κ : Cl} → IsRcD-alg {(RcD S A κ)}{S}{κ} (rcdalgdata lookupRcD stepRcD)
IsRcD-alg.lookup-const RcDIsRcD-alg x = refl
IsRcD-alg.lookup-diag RcDIsRcD-alg g = refl
IsRcD-alg.interact-sl RcDIsRcD-alg df = refl

-- We want to show that RcD is the free such algebra.
-- We need to define what it means for a function to preserve the algebraic structure
-- and what it means for a function to extend a given function.

record IsPreservingRcD-alg {A B S : Set}{κ : Cl} (dmA : RcD-alg-Data A S κ) (dmB : RcD-alg-Data B S κ) (h : A → B) : Set where
  constructor ispreservingRcD-alg

  open RcD-alg-Data dmA
  open RcD-alg-Data dmB renaming (lookupA to lookupB; stepA to stepB)
  field
    lookup-preserve : (g : S → A) → h(lookupA g) ≡ lookupB (λ s → h (g s)) 
    step-preserve : (dx : ▹ κ A) → h (stepA dx) ≡ stepB (λ α → h (dx α))
    
record IsExtendingtoRcD {A B S : Set}{κ : Cl} (f : A → B) (h : (RcD S A κ) → B) : Set where
  constructor isextendingtoRcD

  field
    extendstoRcD : (x : A) → h (unitRcD x) ≡ (f x)

-- foldRcD defines the function we are after
fold-helper : {A B S : Set} {κ : Cl} → (dm : RcD-alg-Data B S κ) → IsRcD-alg dm → (A → B) → Delay A κ → B
fold-helper (rcdalgdata lookupB stepB) isDMB f (nowD a) = f a
fold-helper (rcdalgdata lookupB stepB) isDMB f (stepD x) = stepB (λ α → fold-helper ((rcdalgdata lookupB stepB)) isDMB f (x α))

foldRcD : {A B S : Set}{κ : Cl} → isSet A → isSet B → (dm : RcD-alg-Data B S κ) → IsRcD-alg dm → (A → B) → (RcD S A κ) → B
foldRcD setA setB (rcdalgdata lookupB stepB) isDMB f x = lookupB (λ s → fold-helper (rcdalgdata lookupB stepB) isDMB f (x s))


--foldRcD f extends the function f : A → B
foldRcD-extends : {A B S : Set}{κ : Cl} → ∀(setA : isSet A) → ∀(setB : isSet B) → ∀(dm : RcD-alg-Data B S κ) → ∀(isDMB : IsRcD-alg dm) →
                   ∀ (f : A → B) → IsExtendingtoRcD f (foldRcD setA setB dm isDMB f)
IsExtendingtoRcD.extendstoRcD (foldRcD-extends setA setB dm isDMB f) x = IsRcD-alg.lookup-const isDMB (f x)


--foldRcD preseves the RcD algebra structure
module _ {A B S : Set}{κ : Cl} (setA : isSet A) (setB : isSet B) (dm : RcD-alg-Data B S κ) (isDMB : IsRcD-alg dm)
         (f : A → B)
 where
  open IsPreservingRcD-alg
  open RcD-alg-Data dm renaming (lookupA to lookupB; stepA to stepB)

  foldRcD-preserves : IsPreservingRcD-alg {(RcD S A κ)}{B}{S}{κ} (rcdalgdata lookupRcD stepRcD) dm (foldRcD setA setB dm isDMB f)
  lookup-preserve foldRcD-preserves g = lookupB (λ s → fold-helper (rcdalgdata lookupB stepB) isDMB f (g s s))
                                         ≡⟨ sym ( IsRcD-alg.lookup-diag isDMB ((λ s → (λ s₁ → fold-helper (rcdalgdata lookupB stepB) isDMB f (g s s₁))))) ⟩
                                         lookupB (mapR lookupB (λ s → (λ s₁ → fold-helper (rcdalgdata lookupB stepB) isDMB f (g s s₁))))
                                         ≡⟨ refl ⟩
                                         lookupB (λ s → lookupB (λ s₁ → fold-helper (rcdalgdata lookupB stepB) isDMB f (g s s₁))) ∎
  step-preserve foldRcD-preserves dx = lookupB (λ s → stepB (λ α → fold-helper (rcdalgdata lookupB stepB) isDMB f (dx α s)))
                                        ≡⟨ sym (IsRcD-alg.interact-sl isDMB ((λ α → (λ s → fold-helper (rcdalgdata lookupB stepB) isDMB f (dx α s))))) ⟩
                                        stepB ((map▹ lookupB) (λ α → (λ s → fold-helper (rcdalgdata lookupB stepB) isDMB f (dx α s)))) 
                                        ≡⟨ refl ⟩
                                        stepB (λ α → lookupB (λ s → fold-helper (rcdalgdata lookupB stepB) isDMB f (dx α s))) ∎

-- and finally, foldRcD is unique in doing so. That is, for any function h that both preserves the algebra structure and extends the function f : A → B,
-- h is equivalent to fold.
  
-- First, we show that every x in RcD is of form lookupRcD followed by some StepRcD-s

transform-helper : {A S : Set} {κ : Cl} → Delay A κ → RcD S A κ
transform-helper (nowD a) = unitRcD a
transform-helper (stepD y) = stepRcD (λ α → transform-helper (y α))

transform : {A S : Set} {κ : Cl} → RcD S A κ → RcD S A κ
transform x = lookupRcD (λ s → transform-helper (x s))

lemma-transform-helper : {A S : Set} {κ : Cl} → ∀(y : Delay A κ) → ∀(s : S) → (transform-helper y) s ≡ (unitR y) s 
lemma-transform-helper (nowD y) s = refl
lemma-transform-helper (stepD y) s = cong stepD (later-ext(λ α → lemma-transform-helper (y α) s))

transform-x-is-x : {A S : Set} {κ : Cl} → ∀(x : RcD S A κ) → transform x ≡ x
transform-x-is-x x = funExt (λ s → lemma-transform-helper (x s) s)

-- Then we can show uniqueness
module _ {A B S : Set} {κ : Cl} (setA : isSet A) (setB : isSet B) (dm : RcD-alg-Data B S κ) (isDMB : IsRcD-alg dm)
                       (f : A → B) (h : RcD S A κ → B)
                       (isPDM : IsPreservingRcD-alg {RcD S A κ}{B}{S}{κ} (rcdalgdata (lookupRcD) (stepRcD)) dm h)
                       (isExt : IsExtendingtoRcD f h) where

  open RcD-alg-Data dm renaming (lookupA to lookupB; stepA to stepB)

  fold-uniqueness-lemma : ∀(y : Delay A κ) → h(transform-helper y) ≡ fold-helper(rcdalgdata lookupB stepB) isDMB f y
  fold-uniqueness-lemma (nowD y) = IsExtendingtoRcD.extendstoRcD isExt y
  fold-uniqueness-lemma (stepD y) =  h (stepRcD (λ α → transform-helper (y α)))
                                      ≡⟨ IsPreservingRcD-alg.step-preserve isPDM (λ α → transform-helper (y α)) ⟩
                                      stepB (λ α → h(transform-helper (y α)))
                                      ≡⟨ cong stepB (later-ext (λ α → fold-uniqueness-lemma (y α))) ⟩
                                      stepB (λ α → fold-helper (rcdalgdata lookupB stepB) isDMB f (y α)) ∎

  fold-uniquenessRcD : ∀(x : (RcD S A κ)) → h x ≡ (foldRcD setA setB dm isDMB f x)
  fold-uniquenessRcD x = h x
                          ≡⟨ cong h (sym (transform-x-is-x x)) ⟩
                          h (transform x)
                          ≡⟨ refl ⟩
                          h(lookupRcD (λ s → transform-helper (x s)))
                          ≡⟨ IsPreservingRcD-alg.lookup-preserve isPDM (λ s → transform-helper (x s)) ⟩
                          lookupB (λ s → h(transform-helper (x s)))
                          ≡⟨ cong lookupB (funExt (λ s → fold-uniqueness-lemma (x s))) ⟩
                          lookupB (λ s → fold-helper (rcdalgdata lookupB stepB) isDMB f (x s)) ∎


