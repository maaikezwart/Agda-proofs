{-# OPTIONS --cubical --guarded -W ignore #-}
module combinations-of-delay-and-state where

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

--**************************************--
--**************************************--
-- Combining the monads Delay and State --
--**************************************--
--**************************************--

-- In this document we define a monad that is the a combination of the Delay monad and the State monad.
-- In order to do so, we will first define the State monad, and check that it is indeed a monad.
-- Then we define the Delay monad, and check that it is indeed a monad.
-- Finally, we define the desired combination, which puts the delays in between the reading and writing action
-- of the State monad. We prove that the result is again a monad, namely the free model monad of an equational theory,
-- which has interaction between time steps and the lookup/update functions from State.

--******************--
-- The State Monad  --
--******************--

State : Set → Set → Set
State S A = S → (S × A)

unitS : {A S : Set} → A → State S A
unitS a = λ s → (s , a)

multS : {A S : Set} → State S (State S A) → State S A
multS f = λ s → (proj₂ (f s)) (proj₁(f s))

mapS : {A B S : Set} → (A → B) → State S A → State S B
mapS h f = λ s → ((proj₁ (f s)) , h (proj₂ (f s)))

-- Proving that State forms a monad

-- multS (unitS f) = f
State-unitlaw1 : {A S : Set} → ∀(f : State S A) → multS (unitS f) ≡ f
State-unitlaw1 f = refl

-- multS (mapS unitS f) = f
State-unitlaw2 : {A S : Set} → ∀(f : State S A) → multS (mapS unitS f) ≡ f
State-unitlaw2 f = funExt (λ s → sym (×-η (f s)))

-- multS (multS f) = multS (mapS multS f) 
State-multlaw : {A S : Set} → ∀(f : State S (State S (State S A))) →  multS (multS f) ≡ multS (mapS multS f)
State-multlaw f = refl

-- the unit is a natural transformation:
nattrans-unitS : {A B S : Set} → ∀(h : A → B) → ∀(a : A) → mapS {A}{B}{S} h (unitS a) ≡ unitS (h a)
nattrans-unitS h a = refl

-- the multiplication is a natural transformation:
nattrans-multS : {A B S : Set} → ∀(h : A → B) → ∀(f : State S (State S A)) → mapS h (multS f) ≡ multS (mapS (mapS h) f)
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



--************************************--
-- The combination of State and Delay --
--************************************--

StateDelay : Set → Set → Cl → Set
StateDelay S A κ = S → (Delay (S × A) κ)

unitSD : {A S : Set} {κ : Cl} → A → StateDelay S A κ
unitSD a = λ s → nowD (s , a)

multSD-helper : {A S : Set} {κ : Cl} → (Delay (S × StateDelay S A κ) κ) → (Delay (S × A) κ)  
multSD-helper (nowD (s , g)) = g s
multSD-helper (stepD x) = stepD (λ α → multSD-helper (x α))

multSD : {A S : Set} {κ : Cl} → StateDelay S (StateDelay S A κ) κ → StateDelay S A κ
multSD f = λ s → multSD-helper (f s)

mapSD : {A B S : Set} {κ : Cl} → (A → B) → StateDelay S A κ → StateDelay S B κ
mapSD {A}{B}{S}{κ} h f = λ s → mapD κ (λ w → (proj₁ w , h (proj₂ w))) (f s)

-- Proving that StateDelay forms a monad

-- multSD (unitSD f) = f
StateDelay-unitlaw1 : {A S : Set} {κ : Cl} → ∀(f : StateDelay S A κ) → multSD (unitSD f) ≡ f
StateDelay-unitlaw1 f = refl

-- multSD (mapSD unitSD f) = f
StateDelay-unitlaw2-helper : {A S : Set} {κ : Cl} → ∀(x : (Delay (S × A) κ)) → multSD-helper (mapD κ (λ w → proj₁ w , (λ s₁ → nowD (s₁ , proj₂ w))) x) ≡ x
StateDelay-unitlaw2-helper (nowD x) = cong nowD (sym (×-η x))
StateDelay-unitlaw2-helper (stepD x) = cong stepD (later-ext (λ α → StateDelay-unitlaw2-helper (x α)))

StateDelay-unitlaw2 : {A S : Set} {κ : Cl} → ∀(f : StateDelay S A κ) → multSD (mapSD unitSD f) ≡ f
StateDelay-unitlaw2 f = funExt (λ x → StateDelay-unitlaw2-helper (f x))

-- multSD (multSD f) = multSD (mapSD multSD f)
StateDelay-multlaw-helper : {A S : Set} {κ : Cl} → ∀(x : Delay (S × StateDelay S (StateDelay S A κ) κ) κ) →
                                                     multSD-helper (multSD-helper x) ≡
                                                     multSD-helper (mapD κ (λ w → proj₁ w , (λ s₁ → multSD-helper (proj₂ w s₁))) x)  
StateDelay-multlaw-helper (nowD (s , g)) = refl
StateDelay-multlaw-helper (stepD x) = cong stepD (later-ext (λ α → StateDelay-multlaw-helper (x α)))

StateDelay-multlaw : {A S : Set} {κ : Cl} → ∀(f : StateDelay S (StateDelay S (StateDelay S A κ) κ) κ) →  multSD (multSD f) ≡ multSD (mapSD multSD f)
StateDelay-multlaw f = funExt λ s → StateDelay-multlaw-helper (f s)

-- the unit is a natural transformation:
nattrans-unitSD : {A B S : Set} {κ : Cl} → ∀(h : A → B) → ∀(a : A) → mapSD {A}{B}{S}{κ} h (unitSD a) ≡ unitSD (h a)
nattrans-unitSD h a = refl

-- the multiplication is a natural transformation:
nattrans-multSD-helper : {A B S : Set} {κ : Cl} → ∀(h : A → B) → ∀(x : Delay (S × StateDelay S A κ) κ) →
                                                 mapD κ (λ w → proj₁ w , h (proj₂ w)) (multSD-helper x) ≡
                                                 multSD-helper (mapD κ (λ w → proj₁ w , (λ s₁ → mapD κ (λ w₁ → proj₁ w₁ , h (proj₂ w₁)) (proj₂ w s₁))) x)
nattrans-multSD-helper h (nowD (s , g)) = refl
nattrans-multSD-helper h (stepD x) = cong stepD (later-ext (λ α → nattrans-multSD-helper h (x α)))

nattrans-multSD : {A B S : Set} {κ : Cl} → ∀(h : A → B) → ∀(f : StateDelay S (StateDelay S A κ) κ) → mapSD h (multSD f) ≡ multSD (mapSD (mapSD h) f)
nattrans-multSD h f = funExt λ s → nattrans-multSD-helper h (f s)


-- We now want to write the equational theory of this monad, and prove that the monad is indeed the free monad of that equational theory.

-- first a useful function for step, transforming a delayed (S → A) into a function from S to a delayed A:
just-delay-a : {A S : Set} {κ : Cl} → ▹ κ (S → A) → S → ▹ κ A
just-delay-a df = λ s → map▹ (λ f → f s) df

-- Here is an algebraic theory of "Delayed Mnemoids":
record DelayedMnemoidData (A S : Set) (κ : Cl) : Set where
  constructor delaymnemoiddata
  field
    lookupA : (S → A) → A
    updateA : A → (S → A)
    stepA : ▹ κ A → A

record IsDelayedMnemoid {A S : Set} {κ : Cl} (dm : DelayedMnemoidData A S κ) : Set where
  constructor isdelayedmnemoid

  open DelayedMnemoidData dm
  field
    interact-ll : (g : S → S → A) → lookupA (λ s → lookupA (g s)) ≡ lookupA (λ s → g s s)
    interact-lu : (x : A) → lookupA (updateA x) ≡ x
    interact-ul : (f : S → A) → (s : S) → updateA (lookupA f) s ≡ updateA (f s) s
    interact-uu : (x : A) → (s t : S) → updateA ((updateA x) s) t  ≡ (updateA x) s
    interact-us : (dx : ▹ κ A) → (s : S) → updateA (stepA dx) s ≡ stepA ((just-delay-a (map▹ updateA dx)) s) 
    interact-sl : (df : ▹ κ (S → A)) → stepA ((map▹ lookupA) df) ≡ lookupA (λ s → (stepA ((just-delay-a df) s)))


-- We define three functions: lookupSD, updateSD, and stepSD, that give StateDelay a DelayedMnemoid algebra structure
lookupSD : {A S : Set} {κ : Cl} → (S → (StateDelay S A κ)) → (StateDelay S A κ) 
lookupSD f = λ s → f s s

updateSD :  {A S : Set} {κ : Cl} → (StateDelay S A κ) → (S → (StateDelay S A κ))
updateSD sd = λ s → (λ t → sd s)

stepSD :  {A S : Set} {κ : Cl} → ▹ κ (StateDelay S A κ) → StateDelay S A κ
stepSD dsd = λ s → stepD ((just-delay-a dsd) s)

-- proof that lookupSD, updateSD and stepSD form a DelayedMnemoid:
StateDelayIsDelayedMnemoid : {A S : Set} {κ : Cl} → IsDelayedMnemoid {(StateDelay S A κ)}{S}{κ} (delaymnemoiddata lookupSD updateSD stepSD)
IsDelayedMnemoid.interact-ll StateDelayIsDelayedMnemoid g = refl
IsDelayedMnemoid.interact-lu StateDelayIsDelayedMnemoid x = refl
IsDelayedMnemoid.interact-ul StateDelayIsDelayedMnemoid f s = refl
IsDelayedMnemoid.interact-uu StateDelayIsDelayedMnemoid x s t = refl
IsDelayedMnemoid.interact-us StateDelayIsDelayedMnemoid dx s = refl
IsDelayedMnemoid.interact-sl StateDelayIsDelayedMnemoid df = refl

-- preparing to show that StateDelay together with lookupSD, updateSD and stepSD is the free DelayedMnemoid algebra.
-- We need to define what it means for a function to preserve the DelayedMnemoid algebraic structure
-- and what it means for a function to extend a given function.

record IsPreservingDelayedMnemoid {A B S : Set}(κ : Cl) (dmA : DelayedMnemoidData A S κ) (dmB : DelayedMnemoidData B S κ) (f : A → B) : Set where
  constructor ispreservingDelayedMnemoid

  open DelayedMnemoidData dmA
  open DelayedMnemoidData dmB renaming (lookupA to lookupB; updateA to updateB; stepA to stepB)
  field
    lookup-preserve : (g : S → A) → f(lookupA g) ≡ lookupB (λ s → f (g s)) 
    update-preserve : (x : A) → (s : S) → f((updateA x) s) ≡ updateB (f x) s  --application to s to make my life easier later on.
    step-preserve : (dx : ▹ κ A) → f (stepA dx) ≡ stepB (λ α → f (dx α))
    
record IsExtendingtoStateDelay {A B S : Set}{κ : Cl} (f : A → B) (h : (StateDelay S A κ) → B) : Set where
  constructor isextendingtoStateDelay

  field
    extendstoSD : (x : A) → h (unitSD x) ≡ (f x)

-- foldSD defines the unique preserving extension we are after
fold-helper : {A B S : Set} {κ : Cl} → (dm : DelayedMnemoidData B S κ) → IsDelayedMnemoid dm → (A → B) → Delay (S × A) κ → B
fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (nowD (s , a)) = (updateB (f a)) s
fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (stepD x) = stepB (λ α → fold-helper ((delaymnemoiddata lookupB updateB stepB)) isDMB f (x α))

foldSD : {A B S : Set}{κ : Cl} → isSet A → isSet B → (dm : DelayedMnemoidData B S κ) → IsDelayedMnemoid dm → (A → B) → (StateDelay S A κ) → B
foldSD setA setB (delaymnemoiddata lookupB updateB stepB) isDMB f x = lookupB (λ s → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f ((x s))) 


--foldSD f extends the function f : A → B
foldSD-extends : {A B S : Set}{κ : Cl} → ∀(setA : isSet A) → ∀(setB : isSet B) → ∀(dm : DelayedMnemoidData B S κ) → ∀(isDMB : IsDelayedMnemoid dm) →
                   ∀ (f : A → B) → IsExtendingtoStateDelay f (foldSD setA setB dm isDMB f)
IsExtendingtoStateDelay.extendstoSD (foldSD-extends setA setB dm isDMB f) x = IsDelayedMnemoid.interact-lu isDMB (f x)


--foldDM preseves the DelayedMnemoid structure
module _ {A B S : Set}{κ : Cl} (setA : isSet A) (setB : isSet B) (dm : DelayedMnemoidData B S κ) (isDMB : IsDelayedMnemoid dm)
         (f : A → B)
 where
  open IsPreservingDelayedMnemoid
  open DelayedMnemoidData dm renaming (lookupA to lookupB; updateA to updateB; stepA to stepB)

  lemma1 : ∀(y : Delay(S × A) κ) → ∀(s : S) → lookupB (λ s₁ → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f y) ≡
                                     updateB (fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f y) s
  lemma1 (nowD (t , x)) s = lookupB (λ s₁ → updateB (f x) t)
                             ≡⟨ cong lookupB (funExt λ s₁ → sym (IsDelayedMnemoid.interact-uu isDMB (f x) t s₁)) ⟩
                             lookupB (λ s₁ → updateB (updateB (f x) t) s₁)
                             ≡⟨ cong lookupB refl ⟩
                             lookupB (updateB (updateB (f x) t))
                             ≡⟨ IsDelayedMnemoid.interact-lu isDMB ((updateB (f x) t)) ⟩
                             updateB (f x) t
                             ≡⟨ sym (IsDelayedMnemoid.interact-uu isDMB (f x) t s) ⟩
                             updateB (updateB (f x) t) s ∎
  lemma1 (stepD x) s = lookupB (λ s₁ → stepB (λ α → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x α)))
                        ≡⟨ refl ⟩
                        lookupB (λ s → (stepB ((just-delay-a (λ α → (λ t → (fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x α))))) s )))
                        ≡⟨ sym (IsDelayedMnemoid.interact-sl isDMB ((λ α → (λ t → (fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x α)))))) ⟩
                        stepB ((map▹ lookupB) (λ α → (λ t → (fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x α)))))
                        ≡⟨ refl ⟩
                        stepB (λ α → lookupB (λ t → (fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x α))))
                        ≡⟨ cong stepB (later-ext (λ α → lemma1 ((x α)) s)) ⟩
                        stepB (λ α → updateB (fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x α)) s)
                        ≡⟨ refl ⟩
                        stepB (just-delay-a (λ α → updateB (fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x α))) s)
                        ≡⟨ refl ⟩
                        stepB (just-delay-a (map▹ updateB (λ α → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x α))) s)
                        ≡⟨ sym (IsDelayedMnemoid.interact-us isDMB ((λ α → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x α))) s) ⟩
                        updateB (stepB (λ α → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x α))) s ∎

  foldDM-preserves : IsPreservingDelayedMnemoid {(StateDelay S A κ)}{B}{S} κ (delaymnemoiddata lookupSD updateSD stepSD) dm (foldSD setA setB dm isDMB f)
  lookup-preserve foldDM-preserves g = sym (IsDelayedMnemoid.interact-ll isDMB
                                           (λ s t → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (g s t))) 
  update-preserve foldDM-preserves x s = lookupB (λ s₁ → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x s))
                                          ≡⟨ lemma1 (x s) s ⟩
                                          updateB (fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x s)) s 
                                          ≡⟨ sym (IsDelayedMnemoid.interact-ul isDMB (λ s₁ → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x s₁)) s) ⟩
                                          updateB (lookupB (λ s₁ → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x s₁))) s ∎
  step-preserve foldDM-preserves dx = lookupB (λ s → stepB (λ α → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (dx α s)))
                                       ≡⟨ refl ⟩
                                       lookupB (λ t → (stepB ((just-delay-a (λ α → (λ s → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (dx α s)))) t)))
                                       ≡⟨ sym (IsDelayedMnemoid.interact-sl isDMB ((λ α → (λ s → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (dx α s))))) ⟩
                                       stepB ((map▹ lookupB) (λ α → (λ s → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (dx α s)))) 
                                       ≡⟨ refl ⟩
                                       stepB (λ α → lookupB (λ s → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (dx α s))) ∎

-- and fold is unique in doing so. That is, for any function h that both preserves the algebra structure and extends the function f : A → B,
-- h is equivalent to fold.

-- First, we show that every x in StateDelay is of form lookupSD followed by some StepSDs, followed by an updateSD

transform-helperSD : {A S : Set} {κ : Cl} → (Delay (S × A) κ) → StateDelay S A κ
transform-helperSD (nowD (s , a)) = (updateSD (unitSD a) s)
transform-helperSD (stepD y) = stepSD (λ α → transform-helperSD (y α))

transformSD : {A S : Set} {κ : Cl} → StateDelay S A κ → StateDelay S A κ
transformSD x = lookupSD (λ s → transform-helperSD (x s))

lemma-transform-helperSD : {A S : Set} {κ : Cl} → ∀(y : Delay (S × A) κ) → ∀(s : S) → (transform-helperSD y) s ≡ y 
lemma-transform-helperSD (nowD (t , a)) s = refl
lemma-transform-helperSD (stepD y) s = cong stepD (later-ext(λ α → lemma-transform-helperSD (y α) s))

transformSD-x-is-x : {A S : Set} {κ : Cl} → ∀(x : StateDelay S A κ) → transformSD x ≡ x
transformSD-x-is-x x = funExt (λ s → lemma-transform-helperSD (x s) s)

-- Then we can show uniqueness

module _ {A B S : Set} {κ : Cl} (setA : isSet A) (setB : isSet B) (dm : DelayedMnemoidData B S κ) (isDMB : IsDelayedMnemoid dm)
                       (f : A → B) (h : StateDelay S A κ → B)
                       (isPDM : IsPreservingDelayedMnemoid {StateDelay S A κ}{B} κ (delaymnemoiddata (lookupSD) (updateSD) (stepSD)) dm h)
                       (isExt :  IsExtendingtoStateDelay f h) where

  open DelayedMnemoidData dm renaming (lookupA to lookupB; updateA to updateB; stepA to stepB)

  fold-uniqueness-lemmaSD : ∀(y : Delay (S × A) κ) → h(transform-helperSD y) ≡ fold-helper(delaymnemoiddata lookupB updateB stepB) isDMB f y
  fold-uniqueness-lemmaSD (nowD (s , a)) = h (updateSD (unitSD a) s)
                                            ≡⟨ IsPreservingDelayedMnemoid.update-preserve isPDM (unitSD a) s ⟩
                                            updateB (h (unitSD a)) s  
                                            ≡⟨ cong₂ updateB (IsExtendingtoStateDelay.extendstoSD isExt a) refl ⟩
                                            updateB (f a) s ∎
  fold-uniqueness-lemmaSD (stepD y) =  h (stepSD (λ α → transform-helperSD (y α)))
                                      ≡⟨ IsPreservingDelayedMnemoid.step-preserve isPDM (λ α → transform-helperSD (y α)) ⟩
                                      stepB (λ α → h(transform-helperSD (y α)))
                                      ≡⟨ cong stepB (later-ext (λ α → fold-uniqueness-lemmaSD (y α))) ⟩
                                      stepB (λ α → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (y α)) ∎

  fold-uniquenessSD : ∀(x : (StateDelay S A κ)) → h x ≡ (foldSD setA setB dm isDMB f x)
  fold-uniquenessSD x = h x
                          ≡⟨ cong h (sym (transformSD-x-is-x x)) ⟩
                          h (transformSD x)
                          ≡⟨ refl ⟩
                          h(lookupSD (λ s → transform-helperSD (x s)))
                          ≡⟨ IsPreservingDelayedMnemoid.lookup-preserve isPDM (λ s → transform-helperSD (x s)) ⟩
                          lookupB (λ s → h(transform-helperSD (x s)))
                          ≡⟨ cong lookupB (funExt (λ s → fold-uniqueness-lemmaSD (x s))) ⟩
                          lookupB (λ s → fold-helper (delaymnemoiddata lookupB updateB stepB) isDMB f (x s)) ∎




