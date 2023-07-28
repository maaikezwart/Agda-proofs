{-# OPTIONS --cubical --guarded -W ignore #-}
module combinations-of-lift-and-globalstate where

open import Clocked.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Prod
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool
open import Cubical.Data.FinData
open import combinations-of-lift-and-list
open import Cubical.Relation.Nullary

--*************************************************************************--
--*************************************************************************--
-- Combining the monads Lift and State, where State has multiple locations --
--*************************************************************************--
--*************************************************************************--

-- In this document I want to define a monad that is the a combination of the Lift monad and the State monad,
-- where the state monad has multiple locations.
-- In order to do so, I will first define the the State monad, and check that it is indeed a monad.
-- Then I define a monad that combines this state monad with the Lift monad, and prove that it is a monad.
-- Finally, I show its equational theory, which has interaction between time steps and lookup/update functions from state.

-- The set of locations will be a finite set of natural numbers.
-- set the number of locations here:
number_of_locs : ℕ
number_of_locs = 3

-- The rest of the code will use the set Loc as the set of locations:
Loc : Set
Loc = Fin number_of_locs


--*********************--
-- Global State Monad  --
--*********************--

GlobalState : Set → Set → Set
GlobalState V A = (Loc → V) → ((Loc → V) × A)

unitGS : {V A : Set} → A → GlobalState V A
unitGS a = λ s → (s , a)

multGS : {V A : Set} → GlobalState V (GlobalState V A) → GlobalState V A
multGS f = λ s → (proj₂ (f s)) (proj₁(f s))

mapGS : {V A B : Set} → (A → B) → GlobalState V A → GlobalState V B
mapGS h f = λ s → ((proj₁ (f s)) , h (proj₂ (f s)))

-- Proving that GlobalState forms a monad

-- multGS (unitS f) = f
GlobalState-unitlaw1 : {V A : Set} → ∀(f : GlobalState V A) → multGS (unitGS f) ≡ f
GlobalState-unitlaw1 f = refl

-- multGS (mapGS unitGS f) = f
GlobalState-unitlaw2 : {V A : Set} → ∀(f : GlobalState V A) → multGS (mapGS unitGS f) ≡ f
GlobalState-unitlaw2 f = funExt (λ s → sym (×-η (f s)))

-- multGS (multGS f) = multGS (mapGS multGS f) 
GlobalState-multlaw : {V A : Set} → ∀(f : GlobalState V (GlobalState V (GlobalState V A))) →  multGS (multGS f) ≡ multGS (mapGS multGS f)
GlobalState-multlaw f = refl

-- the unit is a natural transformation:
nattrans-unitGS : {V A B : Set} → ∀(h : A → B) → ∀(a : A) → mapGS {V}{A}{B} h (unitGS a) ≡ unitGS (h a)
nattrans-unitGS h a = refl

-- the multiplication is a natural transformation:
nattrans-multGS : {V A B : Set} → ∀(h : A → B) → ∀(f : GlobalState V (GlobalState V A)) → mapGS h (multGS f) ≡ multGS (mapGS (mapGS h) f)
nattrans-multGS h f = refl

--***************************************--
-- A combination of GlobalState and Lift --
--***************************************--

GlobalStateDelay : Set → Set → Cl → Set
GlobalStateDelay V A κ = (Loc → V) → (myLift ((Loc → V) × A) κ)

unitGSD : {V A : Set} {κ : Cl} → A → GlobalStateDelay V A κ
unitGSD a = λ s → nowL (s , a)

multGSD-helper : {V A : Set} {κ : Cl} → (myLift ((Loc → V) × GlobalStateDelay V A κ) κ) → (myLift ((Loc → V) × A) κ)  
multGSD-helper (nowL (s , g)) = g s
multGSD-helper (stepL x) = stepL (λ α → multGSD-helper (x α))

multGSD : {V A : Set} {κ : Cl} → GlobalStateDelay V (GlobalStateDelay V A κ) κ → GlobalStateDelay V A κ
multGSD f = λ s → multGSD-helper (f s)

mapGSD : {V A B : Set} {κ : Cl} → (A → B) → GlobalStateDelay V A κ → GlobalStateDelay V B κ
mapGSD {V}{A}{B}{κ} h f = λ s → mapL κ (λ w → (proj₁ w , h (proj₂ w))) (f s)

-- Proving that StateDelay forms a monad

-- multGSD (unitSD f) = f
GlobalStateDelay-unitlaw1 : {V A : Set} {κ : Cl} → ∀(f : GlobalStateDelay V A κ) → multGSD (unitGSD f) ≡ f
GlobalStateDelay-unitlaw1 f = refl

-- multGSD (mapGSD unitGSD f) = f
GlobalStateDelay-unitlaw2-helper : {V A : Set} {κ : Cl} → ∀(x : (myLift ((Loc → V) × A) κ)) → multGSD-helper (mapL κ (λ w → proj₁ w , (λ s₁ → nowL (s₁ , proj₂ w))) x) ≡ x
GlobalStateDelay-unitlaw2-helper (nowL x) = cong nowL (sym (×-η x))
GlobalStateDelay-unitlaw2-helper (stepL x) = cong stepL (later-ext (λ α → GlobalStateDelay-unitlaw2-helper (x α)))

GlobalStateDelay-unitlaw2 : {V A : Set} {κ : Cl} → ∀(f : GlobalStateDelay V A κ) → multGSD (mapGSD unitGSD f) ≡ f
GlobalStateDelay-unitlaw2 f = funExt (λ x → GlobalStateDelay-unitlaw2-helper (f x))

-- multGSD (multGSD f) = multGSD (mapGSD multGSD f)
GlobalStateDelay-multlaw-helper : {V A : Set} {κ : Cl} → ∀(x : myLift ((Loc → V) × GlobalStateDelay V (GlobalStateDelay V A κ) κ) κ) →
                                                     multGSD-helper (multGSD-helper x) ≡
                                                     multGSD-helper (mapL κ (λ w → proj₁ w , (λ s₁ → multGSD-helper (proj₂ w s₁))) x)  
GlobalStateDelay-multlaw-helper (nowL (s , g)) = refl
GlobalStateDelay-multlaw-helper (stepL x) = cong stepL (later-ext (λ α → GlobalStateDelay-multlaw-helper (x α)))

GlobalStateDelay-multlaw : {V A : Set} {κ : Cl} → ∀(f : GlobalStateDelay V (GlobalStateDelay V (GlobalStateDelay V A κ) κ) κ) →
                                                    multGSD (multGSD f) ≡ multGSD (mapGSD multGSD f)
GlobalStateDelay-multlaw f = funExt λ s → GlobalStateDelay-multlaw-helper (f s)

-- the unit is a natural transformation:
nattrans-unitGSD : {V A B : Set} {κ : Cl} → ∀(h : A → B) → ∀(a : A) → mapGSD {V}{A}{B}{κ} h (unitGSD a) ≡ unitGSD (h a)
nattrans-unitGSD h a = refl

-- the multiplication is a natural transformation:
nattrans-multGSD-helper : {V A B : Set} {κ : Cl} → ∀(h : A → B) → ∀(x : myLift ((Loc → V) × GlobalStateDelay V A κ) κ) →
                                                 mapL κ (λ w → proj₁ w , h (proj₂ w)) (multGSD-helper x) ≡
                                                 multGSD-helper (mapL κ (λ w → proj₁ w , (λ s₁ → mapL κ (λ w₁ → proj₁ w₁ , h (proj₂ w₁)) (proj₂ w s₁))) x)
nattrans-multGSD-helper h (nowL (s , g)) = refl
nattrans-multGSD-helper h (stepL x) = cong stepL (later-ext (λ α → nattrans-multGSD-helper h (x α)))

nattrans-multGSD : {V A B : Set} {κ : Cl} → ∀(h : A → B) → ∀(f : GlobalStateDelay V (GlobalStateDelay V A κ) κ) →
                                                            mapGSD h (multGSD f) ≡ multGSD (mapGSD (mapGSD h) f)
nattrans-multGSD h f = funExt λ s → nattrans-multGSD-helper h (f s)

-- We now want to write the equational theory of this monad, and prove that the monad is indeed the free monad of that equational theory.
-- We define three functions: lookupSD, updateSD, and stepSD:

-- useful function for step, transforming a delayed (S → A) into a function from S to a delayed A:
just-delay-a : {L V A : Set} {κ : Cl} → ▹ κ ((L → V) → A) → (L → V) → ▹ κ A
just-delay-a df = λ s → map▹ (λ f → f s) df

-- the actual functions lookup, update and step:
lookupGSD : {V A : Set} {κ : Cl} → (V → (GlobalStateDelay V A κ)) → (Loc → (GlobalStateDelay V A κ)) 
lookupGSD f = λ l → (λ g → f ((g l)) g)

--updateGSD-helper : {V : Set} → Loc → V → (Loc → V) → (Loc → V)
--updateGSD-helper {V} l v f l' with (discreteFin l l')
--...                             | yes p = v
--...                             | no ¬p = (f l')

updateGSD-helper : {V : Set} → Loc → V → (Loc → V) → (Loc → V)
updateGSD-helper {V} l v f l' = case (discreteFin l l') of 
                                  λ {(yes p) → v ; (no ¬p) → (f l')}

updateGSD : {V A : Set} {κ : Cl} → (GlobalStateDelay V A κ) → (Loc → V → (GlobalStateDelay V A κ))
updateGSD gsd l v = λ f → gsd (updateGSD-helper l v f)
-- from Plotkin and Power: Given an element of A together with a location l and a value v,
-- the update operation updates the state by insisting that l take value v,
-- and then allowing the computation to run. 

stepGSD : {V A : Set} {κ : Cl} → ▹ κ (GlobalStateDelay V A κ) → GlobalStateDelay V A κ
stepGSD dsd = λ s → stepL ((just-delay-a dsd) s)


-- Here is an algebraic theory of "Delayed Mnemoids" with locations Loc:

record DelayedMnemoidData (V A : Set) (κ : Cl) : Set where
  constructor delaymnemoiddata
  field
    lookupA : (V → A) → (Loc → A)
    updateA : A → (Loc → V → A)
    stepA : ▹ κ A → A

record IsDelayedMnemoid {V A : Set} {κ : Cl} (dm : DelayedMnemoidData V A κ) : Set where
  constructor isdelayedmnemoid

  open DelayedMnemoidData dm
  field
    interact-lu  : (x : A) → (l : Loc) → lookupA (updateA x l) l ≡ x
    interact-ll  : (g : (V → V → A)) → (l l' : Loc) → case (discreteFin l l') of
                                                        λ {(yes p) → lookupA (λ v → lookupA (g v) l) l ≡ lookupA (λ v → g v v) l ;
                                                           (no ¬p) → lookupA (λ v → lookupA (g v) l') l ≡ lookupA (λ v → lookupA (g v) l) l'
                                                           }
    interact-ul  : (f : V → A) → (l l' : Loc) → (v : V) → case (discreteFin l l') of
                                                            λ {(yes p) → updateA (lookupA f l) l v ≡ updateA (f v) l v ;
                                                               (no ¬p) → updateA (lookupA f l') l v ≡ lookupA (λ v' → updateA (f v') l v) l'
                                                               }
    interact-uu  : (x : A) → (l l' : Loc) → (v v' : V) → case (discreteFin l l') of
                                                            λ {(yes p) → updateA ((updateA x l) v) l v' ≡ updateA x l v ;
                                                               (no ¬p) → updateA ((updateA x l) v) l' v' ≡ updateA ((updateA x l') v') l v
                                                               }
    interact-us  : (dx : ▹ κ A) → (l : Loc) → (v : V) → updateA (stepA dx) l v ≡ stepA (λ α → map▹ updateA dx α l v) 
    interact-sl  : (df : ▹ κ (V → A)) → (l : Loc) → stepA (λ α → map▹ lookupA df α l) ≡ lookupA (λ v → (stepA (λ α → df α v))) l

-- proof that lookupSD, updateSD and stepSD form a DelayedMnemoid:

lemmaLoc : ∀(l : Loc) → discreteFin l l ≡ yes refl
lemmaLoc l with discreteFin l l
...                  | (yes p) = cong yes (isSetFin l l p refl)
...                  | (no ¬p) = ⊥.rec (¬p refl)

lemma-lu : {V : Set} → ∀(l l' : Loc) → ∀(s : Loc → V) → updateGSD-helper l (s l) s l' ≡ s l'
lemma-lu l l' s with discreteFin l l'
...               | (yes p) = cong s p
...               | (no ¬p) = refl

lemma-ul : {V : Set} → ∀(l : Loc) → ∀(s : Loc → V) → ∀(v : V) → updateGSD-helper l v s l ≡ v
lemma-ul l s v with discreteFin l l
...              | (yes p) = refl
...              | (no ¬p) = ⊥.rec (¬p refl)

lemma-ul2 : {V : Set} → ∀(l l' : Loc) → (¬p : l ≡ l' → ⊥) → ∀(s : Loc → V) → ∀(v : V) → updateGSD-helper l v s l' ≡ s l'
lemma-ul2 l l' ¬p s v with discreteFin l l'
...                    | (yes q) = ⊥.rec (¬p q)
...                    | (no ¬q) = refl

updateupdateGSD-helper : {V : Set} → Loc → V → (Loc → V) → (Loc → V)
updateupdateGSD-helper {V} l v f l' = case (discreteFin l l') of 
                                  λ {(yes p) → v ; (no ¬p) → updateGSD-helper l v f l'}

lemma-uu : {V : Set} → ∀(l l' : Loc) → ∀(s : Loc → V) → ∀(v : V) → updateupdateGSD-helper l v s l' ≡ updateGSD-helper l v s l'
lemma-uu l l' s v with discreteFin l l'
...                    | (yes p) = refl
...                    | (no ¬p) with discreteFin l l'
...                                | (yes q) = ⊥.rec (¬p q) 
...                                | (no ¬q) = refl

GlobalStateDelayIsDelayedMnemoid : {V A : Set} {κ : Cl} → IsDelayedMnemoid {V}{(GlobalStateDelay V A κ)}{κ} (delaymnemoiddata lookupGSD updateGSD stepGSD)
IsDelayedMnemoid.interact-lu  GlobalStateDelayIsDelayedMnemoid x l = funExt (λ s → cong x (funExt (λ l' →  lemma-lu l l' s )))
IsDelayedMnemoid.interact-ll  GlobalStateDelayIsDelayedMnemoid g l l' with discreteFin l l'
...                                                                     | (yes p) = refl
...                                                                     | (no ¬p) = funExt (λ s → {!!})
IsDelayedMnemoid.interact-ul  GlobalStateDelayIsDelayedMnemoid f l l' v with discreteFin l l'
...                                                                     | (yes p) = funExt (λ s → cong₂ f (lemma-ul l s v) refl)
...                                                                     | (no ¬p) = funExt (λ s → cong₂ f (lemma-ul2 l l' ¬p s v) refl)
IsDelayedMnemoid.interact-uu  GlobalStateDelayIsDelayedMnemoid x l l' v v' with discreteFin l l'
...                                                                     | (yes p) = funExt (λ s → cong x (funExt (λ l'' → {!lemma-uu l l'' s v !})))
...                                                                     | (no ¬p) = funExt (λ s → cong x (funExt (λ l'' → {!!} )))
IsDelayedMnemoid.interact-us  GlobalStateDelayIsDelayedMnemoid dx l v = refl
IsDelayedMnemoid.interact-sl  GlobalStateDelayIsDelayedMnemoid dx l = refl

-- I show that every x in StateDelay is stored in some location, specified by lookupSD followed by some StepSDs, followed by an updateSD

--transform-helperGSD : {V A : Set} {κ : Cl} → (myLift ((Loc → V) × A) κ) → GlobalStateDelay V A κ
--transform-helperGSD l (nowL (f , a)) = (updateGSD (unitGSD a) l (f l))
--transform-helperGSD l (stepL y) = stepGSD (λ α → transform-helperGSD l (y α))

--transformGSD : {V A : Set} {κ : Cl} → Loc → GlobalStateDelay V A κ → GlobalStateDelay V A κ
--transformGSD l x = lookupGSD (λ v → transform-helperGSD l (x (λ l → v)))

--lemma-transform-helperGSD : {V A : Set} {κ : Cl} → ∀(y : myLift ((Loc → V) × A) κ) → ∀(v : V) → Σ[ l ∈ ℕ ] (((transform-helperGSD l y) (λ l → v)) ≡ y) 
--lemma-transform-helperGSD (nowL (f , a)) v = {!refl!}
--lemma-transform-helperGSD (stepL y) v = {!!}

--transformSD-x-is-x : {A S : Set} {κ : Cl} → ∀(x : StateDelay S A κ) → transformSD x ≡ x
--transformSD-x-is-x x = funExt (λ s → lemma-transform-helperSD (x s) s)


-- preparing to show that StateDelay is the free such algebra. We need to define what it means for a function to preserve the algebraic structure
-- and what it means for a function to extend a given function.

record IsPreservingDelayedMnemoid {V A B : Set}(κ : Cl) (dmA : DelayedMnemoidData V A κ) (dmB : DelayedMnemoidData V B κ) (f : A → B) : Set where
  constructor ispreservingDelayedMnemoid

  open DelayedMnemoidData dmA
  open DelayedMnemoidData dmB renaming (lookupA to lookupB; updateA to updateB; stepA to stepB)
  field
    lookup-preserve : (g : V → A) (l : Loc) → f(lookupA g l) ≡ lookupB (λ v → f (g v)) l 
    update-preserve : (x : A) → (l : Loc) → (v : V) → f((updateA x) l v) ≡ updateB (f x) l v  --application to l and v to make my life easier later on.
    step-preserve   : (dx : ▹ κ A) → f (stepA dx) ≡ stepB (λ α → f (dx α))
    
record IsExtendingtoGlobalStateDelay {V A B : Set}{κ : Cl} (f : A → B) (h : (GlobalStateDelay V A κ) → B) : Set where
  constructor isextendingtoGlobalStateDelay

  field
    extendstoGSD : (x : A) → h (unitGSD x) ≡ (f x)

-- foldGSD defines the unique preserving extension we are after.
-- to define it, we follow Plotkin and Power - Notions of Computation Determine Monads - Theorem 1.

--First we define a funtion from (Loc → V) × A) to (Loc → (Loc → V) × A)

structmap1 : {V A : Set} → ((Loc → V) × A) → ((Loc → (Loc × V)) × A)
structmap1 (f , a) = ((λ l → l , f l) , a)

-- Then we define an update function that has type ((Loc → (Loc × V)) × A) → A,
-- applying the normal update function number-of-locs times.

--I need two functions on Fin - flast and restriction
flast : (n : ℕ) → Fin (suc n)
flast zero = zero
flast (suc n) = suc (flast n)

restrict-n : {V : Set} → (n : ℕ) → (Fin (suc n) → Loc × V) → Fin n → Loc × V
restrict-n n f x = f (weakenFin x) 

-- building up to the new update function, first uncurry 
update' : {V A : Set}{κ : Cl} → (dm : DelayedMnemoidData V A κ) → A → (Loc × V) → A
update' (delaymnemoiddata lookupA updateA stepA) a (l , v) = updateA a l v

--then apply recursively
updateRec : {V A : Set}{κ : Cl} → (dm : DelayedMnemoidData V A κ) → (n : ℕ) → A → ((Fin n) → (Loc × V)) → A
updateRec dm zero a = λ f → a
updateRec dm (suc zero) a = λ f → update' dm a (f zero)
updateRec dm (suc (suc n)) a = λ f → update' dm (updateRec dm (suc n) a (restrict-n (suc n) f)) (f (flast  (suc n)))

--we need to apply update number_of_locs times
updateN : {V A : Set}{κ : Cl} → (dm : DelayedMnemoidData V A κ) → A → ((Loc → (Loc × V)) → A)
updateN dm a = updateRec dm number_of_locs a

--finally the update function of the right type:
updateL : {V A : Set}{κ : Cl} → (dm : DelayedMnemoidData V A κ) → ((Loc → (Loc × V)) × A) → A
updateL dm (p , a) = (updateN dm a) p


-- after applying update number-of-locs times, we also need to apply lookup number-of-locs times.

--normal lookup : (V → A) → (Loc → A)
  

-- lookup lookup V → (V → A) → L → (L → A)

lookupHelp1 : {V : Set} → (n : ℕ) → V → (Fin n → V) → Fin (suc n) → V
lookupHelp1 n v g zero = v
lookupHelp1 n v g (suc l) = g l

lookupRec : {V A : Set}{κ : Cl} → (dm : DelayedMnemoidData V A κ) → (n : ℕ) → (((Fin n) → V) → A) → ((Fin n) → Loc) → A 
lookupRec (delaymnemoiddata lookupA updateA stepA) zero f g = lookupA (λ v → f (const v)) (zero) --nonsense because I want the induction to start at 1. This might come back to bite me.
lookupRec (delaymnemoiddata lookupA updateA stepA) (suc zero) f = λ g → lookupA (λ v → f (const v)) (g zero) 
lookupRec (delaymnemoiddata lookupA updateA stepA) (suc (suc n)) f = λ g → lookupA (λ v → lookupRec ((delaymnemoiddata lookupA updateA stepA)) (suc n) (λ f' → f (lookupHelp1 (suc n) v f'))
                                                                                               (λ m → g (weakenFin m))) (g (flast (suc n)))

lookupL : {V A : Set}{κ : Cl} → (dm : DelayedMnemoidData V A κ) → ((Loc → V) → A) → ((Loc → Loc) → A)
lookupL dm = lookupRec dm number_of_locs

-- Then, defining fold :
Id : {A : Set} → A → A
Id a = a

foldGSD-helper : {V A B : Set} {κ : Cl} → (dm : DelayedMnemoidData V B κ) → IsDelayedMnemoid dm → (A → B) → myLift ((Loc → V) × A) κ → B
foldGSD-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (nowL (g , a)) = (updateL (delaymnemoiddata lookupB updateB stepB) (structmap1 ((g , f a))) ) 
foldGSD-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (stepL x) = stepB (λ α → foldGSD-helper ((delaymnemoiddata lookupB updateB stepB)) isDMB f (x α))

foldGSD : {V A B : Set}{κ : Cl} → isSet A → isSet B → (dm : DelayedMnemoidData V B κ) → IsDelayedMnemoid dm → (A → B) → (GlobalStateDelay V A κ) → B
foldGSD {V}{A}{B}{κ} setA setB (delaymnemoiddata lookupB updateB stepB) isDMB f x = lookupL {V}{B}{κ} ((delaymnemoiddata lookupB updateB stepB))
                                                                                      ((λ g → foldGSD-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x g)))
                                                                                    Id 
--fold extends the function f : A → B
foldGSD-extends : {V A B : Set}{κ : Cl} → ∀(setA : isSet A) → ∀(setB : isSet B) → ∀(dm : DelayedMnemoidData V B κ) → ∀(isDMB : IsDelayedMnemoid dm) →
                   ∀ (f : A → B) → IsExtendingtoGlobalStateDelay f (foldGSD setA setB dm isDMB f)
IsExtendingtoGlobalStateDelay.extendstoGSD (foldGSD-extends setA setB dm isDMB f) x = {!!} --IsDelayedMnemoid.interact-lu isDMB (f x)

-- --foldDM preseves the DelayedMnemoid structure
-- module _ {A B S : Set}{κ : Cl} (setA : isSet A) (setB : isSet B) (dm : DelayedMnemoidData B S κ) (isDMB : IsDelayedMnemoid dm)
--          (f : A → B)
--  where
--   open IsPreservingDelayedMnemoid
--   open DelayedMnemoidData dm renaming (lookupA to lookupB; updateA to updateB; stepA to stepB)

--   lemma1 : ∀(y : myLift(S × A) κ) → ∀(s : S) → lookupB (λ s₁ → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f y) ≡
--                                      updateB (fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f y) s
--   lemma1 (nowL (t , x)) s = lookupB (λ s₁ → updateB (f x) t)
--                              ≡⟨ cong lookupB (funExt λ s₁ → sym (IsDelayedMnemoid.interact-uu isDMB (f x) t s₁)) ⟩
--                              lookupB (λ s₁ → updateB (updateB (f x) t) s₁)
--                              ≡⟨ cong lookupB refl ⟩
--                              lookupB (updateB (updateB (f x) t))
--                              ≡⟨ IsDelayedMnemoid.interact-lu isDMB ((updateB (f x) t)) ⟩
--                              updateB (f x) t
--                              ≡⟨ sym (IsDelayedMnemoid.interact-uu isDMB (f x) t s) ⟩
--                              updateB (updateB (f x) t) s ∎
--   lemma1 (stepL x) s = lookupB (λ s₁ → stepB (λ α → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x α)))
--                         ≡⟨ refl ⟩
--                         lookupB (λ s → (stepB ((just-delay-a (λ α → (λ t → (fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x α))))) s )))
--                         ≡⟨ sym (IsDelayedMnemoid.interact-sl isDMB ((λ α → (λ t → (fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x α)))))) ⟩
--                         stepB ((map▹ lookupB) (λ α → (λ t → (fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x α)))))
--                         ≡⟨ refl ⟩
--                         stepB (λ α → lookupB (λ t → (fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x α))))
--                         ≡⟨ cong stepB (later-ext (λ α → lemma1 ((x α)) s)) ⟩
--                         stepB (λ α → updateB (fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x α)) s)
--                         ≡⟨ refl ⟩
--                         stepB (just-delay-a (λ α → updateB (fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x α))) s)
--                         ≡⟨ refl ⟩
--                         stepB (just-delay-a (map▹ updateB (λ α → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x α))) s)
--                         ≡⟨ sym (IsDelayedMnemoid.interact-us isDMB ((λ α → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x α))) s) ⟩
--                         updateB (stepB (λ α → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x α))) s ∎

--   foldDM-preserves : IsPreservingDelayedMnemoid {(StateDelay S A κ)}{B}{S} κ (delaymnemoiddata lookupSD updateSD stepSD) dm (foldSD setA setB dm isDMB f)
--   lookup-preserve foldDM-preserves g = sym (IsDelayedMnemoid.interact-ll isDMB
--                                            (λ s t → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (g s t))) 
--   update-preserve foldDM-preserves x s = lookupB (λ s₁ → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x s))
--                                           ≡⟨ lemma1 (x s) s ⟩
--                                           updateB (fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x s)) s 
--                                           ≡⟨ sym (IsDelayedMnemoid.interact-ul isDMB (λ s₁ → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x s₁)) s) ⟩
--                                           updateB (lookupB (λ s₁ → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x s₁))) s ∎
--   step-preserve foldDM-preserves dx = lookupB (λ s → stepB (λ α → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (dx α s)))
--                                        ≡⟨ refl ⟩
--                                        lookupB (λ t → (stepB ((just-delay-a (λ α → (λ s → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (dx α s)))) t)))
--                                        ≡⟨ sym (IsDelayedMnemoid.interact-sl isDMB ((λ α → (λ s → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (dx α s))))) ⟩
--                                        stepB ((map▹ lookupB) (λ α → (λ s → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (dx α s)))) 
--                                        ≡⟨ refl ⟩
--                                        stepB (λ α → lookupB (λ s → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (dx α s))) ∎

-- --and fold is unique in doing so. That is, for any function h that both preserves the algebra structure and extends the function f : A → B,
-- -- h is equivalent to fold.

-- module _ {A B S : Set} {κ : Cl} (setA : isSet A) (setB : isSet B) (dm : DelayedMnemoidData B S κ) (isDMB : IsDelayedMnemoid dm)
--                        (f : A → B) (h : StateDelay S A κ → B)
--                        (isPDM : IsPreservingDelayedMnemoid {StateDelay S A κ}{B} κ (delaymnemoiddata (lookupSD) (updateSD) (stepSD)) dm h)
--                        (isExt :  IsExtendingtoStateDelay f h) where

--   open DelayedMnemoidData dm renaming (lookupA to lookupB; updateA to updateB; stepA to stepB)

--   fold-uniqueness-lemmaSD : ∀(y : myLift (S × A) κ) → h(transform-helperSD y) ≡ fold-helper(delaymnemoiddata lookupB updateB stepB) isDMB f y
--   fold-uniqueness-lemmaSD (nowL (s , a)) = h (updateSD (unitSD a) s)
--                                             ≡⟨ IsPreservingDelayedMnemoid.update-preserve isPDM (unitSD a) s ⟩
--                                             updateB (h (unitSD a)) s  
--                                             ≡⟨ cong₂ updateB (IsExtendingtoStateDelay.extendstoSD isExt a) refl ⟩
--                                             updateB (f a) s ∎
--   fold-uniqueness-lemmaSD (stepL y) =  h (stepSD (λ α → transform-helperSD (y α)))
--                                       ≡⟨ IsPreservingDelayedMnemoid.step-preserve isPDM (λ α → transform-helperSD (y α)) ⟩
--                                       stepB (λ α → h(transform-helperSD (y α)))
--                                       ≡⟨ cong stepB (later-ext (λ α → fold-uniqueness-lemmaSD (y α))) ⟩
--                                       stepB (λ α → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (y α)) ∎

--   fold-uniquenessSD : ∀(x : (StateDelay S A κ)) → h x ≡ (foldSD setA setB dm isDMB f x)
--   fold-uniquenessSD x = h x
--                           ≡⟨ cong h (sym (transformSD-x-is-x x)) ⟩
--                           h (transformSD x)
--                           ≡⟨ refl ⟩
--                           h(lookupSD (λ s → transform-helperSD (x s)))
--                           ≡⟨ IsPreservingDelayedMnemoid.lookup-preserve isPDM (λ s → transform-helperSD (x s)) ⟩
--                           lookupB (λ s → h(transform-helperSD (x s)))
--                           ≡⟨ cong lookupB (funExt (λ s → fold-uniqueness-lemmaSD (x s))) ⟩
--                           lookupB (λ s → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x s)) ∎

