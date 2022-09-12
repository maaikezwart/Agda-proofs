{-# OPTIONS --cubical --guarded -W ignore #-}
module combinations-of-lift-and-tree where

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
open import combinations-of-lift-and-list

--**************************************************************************--
--**************************************************************************--
-- Combining the monads Lift and Tree freely and via a distributive law --
--**************************************************************************--
--**************************************************************************--

-- In this document I want to define a monad that is the free combination of the Lift monad and the Multiset monad.
-- In order to do so, I will first define the the Tree monad, and check that it is indeed a monad (Step 1).
-- Then I define the TreeLift monad, check that it is a monad (Step 2), and finally check that it is the free monad on the algebra
-- structures of a delay algebra and a magma (Step 3).
-- The Lift monad has aleady been defined in my earlier work, combinations-of-lift-and-list.
-- In the same file I check that lift is indeed a monad, and define various usefull functions, such as a map function for Lift.

-- In addition to the free combination of the Tree and the Lift monads, I also compose the two monads to form the monad
-- LcT : A → Lift(Tree A). This composition uses a distributive law, which I prove does indeed satisfy all the axioms for a
-- distributive law.


--****************************--
-- Step 1: The Tree monad --
--****************************--

--We define the Tree monad as the free unital magma monad on A.
--This is a HIT.

data Tree {ℓ} (A : Type ℓ) : Type ℓ where
  ∅t        : Tree A
  singleT  : A → Tree A
  _∪ₜ_      : Tree A → Tree A → Tree A
  unitrT   : ∀ x → x ∪ₜ ∅t ≡ x
  unitlT   : ∀ x → ∅t ∪ₜ x ≡ x
  truncT   : isSet (Tree A)

-- map function for Tree
mapT : {A B : Set} → (A → B) → Tree A → Tree B
mapT f ∅t = ∅t
mapT f (singleT x) = singleT (f x)
mapT f (T₁ ∪ₜ T₂) = (mapT f T₁) ∪ₜ (mapT f T₂)
mapT f (unitrT T i) = unitrT (mapT f T) i
mapT f (unitlT T i) = unitlT (mapT f T) i
mapT f (truncT T₁ T₂ x y i i₁) = truncT (mapT f T₁) (mapT f T₂) (λ j → mapT f (x j)) (λ j → mapT f (y j)) i i₁

-- Bind and multiplication functions for Tree
BindT : {A B : Set} → (A → Tree B) → Tree A → Tree B
BindT f ∅t = ∅t
BindT f (singleT x) = f x
BindT f (x ∪ₜ y) = (BindT f x) ∪ₜ (BindT f y)
BindT f (unitrT x i) = unitrT (BindT f x) i
BindT f (unitlT x i) = unitlT (BindT f x) i
BindT f (truncT T₁ T₂ x y i i₁) = truncT (BindT f T₁) (BindT f T₂) (\ j → BindT f (x j)) (\ j → BindT f (y j)) i i₁

MultT : {A : Set} → Tree (Tree A) → Tree A
MultT ∅t = ∅t
MultT (singleT x) = x
MultT (x ∪ₜ y) = (MultT x) ∪ₜ (MultT y)
MultT (unitrT x i) = unitrT (MultT x) i
MultT (unitlT x i) = unitlT (MultT x) i
MultT (truncT T₁ T₂ x y i i₁) = truncT (MultT T₁) (MultT T₂) (\ j → MultT (x j)) (\ j → MultT (y j)) i i₁

-- Elimination principle for Tree

-- module to make the inputs more readable
-- no name for the module to make the use of it more readable
module _ {ℓ}{A : Type ℓ}
         (P : Tree A → hProp ℓ)
         (P∅ : fst (P ∅t))
         (Pη : ∀ t → fst (P (singleT t)))
         (P∪ : ∀ {t s} → fst(P t) → fst(P s) → fst(P (t ∪ₜ s)))
         where

  elimT : ∀ M → fst(P M)
  elimT ∅t = P∅
  elimT (singleT x) = Pη x
  elimT (T₁ ∪ₜ T₂) = P∪ (elimT T₁) (elimT T₂)
  elimT (unitrT T i) = isProp→PathP (λ j → snd (P (unitrT T j))) (P∪ (elimT T) (P∅)) (elimT T) i
  elimT (unitlT T i) = isProp→PathP (λ j → snd (P (unitlT T j))) (P∪ (P∅) (elimT T)) (elimT T) i
  elimT (truncT T₁ T₂ x y i j) = isOfHLevel→isOfHLevelDep 2 (λ k → isProp→isSet (snd (P k))) (elimT T₁) (elimT T₂) (cong elimT x) (cong elimT y)
                                      (truncT T₁ T₂ x y) i j


-- Proving that the Tree forms a monad

-- MultT (singleT T) = T
Tree-unitlaw1 : {A : Set} → ∀(T : Tree A) → MultT (singleT T) ≡ T
Tree-unitlaw1 T = refl

-- MultT (mapT singleT T) = T
Tree-unitlaw2 : {A : Set} → ∀(T : Tree A) → MultT (mapT singleT T) ≡ T
Tree-unitlaw2 T = elimT
                   (λ T → (MultT (mapT singleT T) ≡ T) , truncT (MultT (mapT singleT T)) T)
                   refl
                   (λ T → refl)
                   (λ eq1 eq2 → cong₂ _∪ₜ_ eq1 eq2 )
                   T

-- MultT (MultT T) = MultT (map MultT T) 
Tree-multlaw : {A : Set} → ∀(T : Tree (Tree (Tree A))) →  MultT (MultT T) ≡ MultT (mapT MultT T)
Tree-multlaw T = elimT
                  (λ T → (MultT (MultT T) ≡ MultT (mapT MultT T)) ,
                          truncT (MultT (MultT T)) (MultT (mapT MultT T)))
                  refl
                  (λ T → refl)
                  (λ eq1 eq2 → cong₂ (_∪ₜ_) eq1 eq2)
                  T

-- the unit is a natural transformation:
nattrans-singleT : {A B : Set} → ∀(f : A → B) → ∀(x : A) → mapT f (singleT x) ≡ singleT (f x)
nattrans-singleT f x = refl

-- the multiplication is a natural transformation:
nattrans-MultT : {A B : Set} → ∀(f : A → B) → ∀(TT : Tree (Tree A)) → mapT f (MultT TT) ≡ MultT (mapT (mapT f) TT)
nattrans-MultT f TT = elimT
                       ((λ TT →  (mapT f (MultT TT) ≡ MultT (mapT (mapT f) TT)) ,
                                  truncT (mapT f (MultT TT)) (MultT (mapT (mapT f) TT))))
                       refl
                       (λ TT → refl)
                       (λ eq1 eq2 → cong₂ (_∪ₜ_) eq1 eq2)
                       TT 


--*****************************--
-- Step 2: The TreeLift monad --
--*****************************--

--Now that we have a Tree monad and a Lift monad, I want to show that the following combination of the two is again a monad:
--TreeLift : (A : Set) → (κ : Cl) → Set
--TreeLift A κ = Tree (A ⊎ (▹ κ (TreeLift A κ)))

data TreeLift (A : Set) (κ : Cl) : Set where
  conTL : Tree (A ⊎ (▹ κ (TreeLift A κ))) -> TreeLift A κ

-- Elimination principle for MultiLift

-- module to make the inputs more readable
-- no name for the module to make the use of it more readable
module _ {ℓ}{A : Set}{κ : Cl}
         (P : TreeLift A κ → hProp ℓ)
         (P∅ : fst (P (conTL ∅t)))
         (Pη1 : ∀ x → fst (P (conTL (singleT (inl x)))))
         (Pη2 : ∀ {x} → (∀ α → fst (P (x α))) → fst (P (conTL (singleT (inr x)))))
         (P∪ : ∀ {t s} → fst(P (conTL t)) → fst(P (conTL s)) → fst(P (conTL (t ∪ₜ s))))
         where

  elimTL : ∀ M → fst(P M)
  elimTL (conTL ∅t) = P∅
  elimTL (conTL (singleT (inl x))) = Pη1 x
  elimTL (conTL (singleT (inr x))) = Pη2 λ α → elimTL (x α) 
  elimTL (conTL (x ∪ₜ y)) = P∪ (elimTL (conTL x)) (elimTL (conTL y))
  elimTL (conTL (unitrT T i)) = isProp→PathP (λ j → snd (P (conTL (unitrT T j)))) (P∪ (elimTL (conTL T)) (P∅)) (elimTL (conTL T)) i
  elimTL (conTL (unitlT T i)) = isProp→PathP (λ j → snd (P (conTL (unitlT T j)))) (P∪ (P∅) (elimTL (conTL T))) (elimTL (conTL T)) i
  elimTL (conTL (truncT T₁ T₂ x y i j)) = isOfHLevel→isOfHLevelDep 2 (λ z → isProp→isSet (snd (P (conTL z)))) (elimTL (conTL T₁)) (elimTL (conTL T₂))
                                          (cong elimTL (cong conTL x)) (cong elimTL (cong conTL y)) (truncT T₁ T₂ x y ) i j


--***proof that TreeLift is a set***--
-- strategy: build isomorphism, then make equivalence, then use univalence to turn equivalence into equality, then transport.

isoTL :  {A : Set}{κ : Cl} → Iso (Tree (A ⊎ (▹ κ (TreeLift A κ)))) (TreeLift A κ)  
Iso.fun isoTL = conTL
Iso.inv isoTL (conTL x) = x
Iso.rightInv isoTL (conTL x) = refl
Iso.leftInv isoTL a = refl

equivTL :  {A : Set}{κ : Cl} → (Tree (A ⊎ (▹ κ (TreeLift A κ)))) ≃ (TreeLift A κ)
equivTL = isoToEquiv isoTL

equalTL : {A : Set}{κ : Cl} → (Tree (A ⊎ (▹ κ (TreeLift A κ)))) ≡ (TreeLift A κ)
equalTL = ua equivTL

truncTL : {A : Set} {κ : Cl} → isSet (TreeLift A κ)
truncTL = subst⁻ isSet (sym equalTL) truncT

--IsotoPath as shortcut for this bit of code

--***algebraic structure for TeeLift***--

--nowML and stepML turn TreeLift into a delay algebra structure:
nowTL : {A : Set} (κ : Cl) → A → (TreeLift A κ)
nowTL κ a = conTL (singleT (inl a))

stepTL : {A : Set} (κ : Cl) → ▹ κ (TreeLift A κ) → (TreeLift A κ)
stepTL κ a = conTL (singleT (inr a))

--the union is derived from the Tree union, and turns TreeLift into a unital magma:
_∪ₜₗ_ : {A : Set} {κ : Cl} → (TreeLift A κ) → (TreeLift A κ) → (TreeLift A κ)
_∪ₜₗ_ {A} {κ} (conTL t) (conTL s) = conTL (t ∪ₜ s)

--proof that this union does indeed provide a unital magma structure: 
unitrTL : {A : Set} {κ : Cl} → ∀ (tl : (TreeLift A κ)) → tl ∪ₜₗ conTL ∅t ≡ tl
unitrTL {A} {κ} (conTL t) = cong conTL (unitrT t)

unitlTL : {A : Set} {κ : Cl} → ∀ (tl : (TreeLift A κ)) → conTL ∅t ∪ₜₗ tl ≡ tl
unitlTL {A} {κ} (conTL t) = cong conTL (unitlT t)


--***monadic structure for TreeLift***--

--a map function to turn TreeLift into a functor
mapTL : {A B : Set} (κ : Cl) → (f : A → B) → (TreeLift A κ) → (TreeLift B κ)
mapTL κ f (conTL ∅t) = conTL ∅t
mapTL κ f (conTL (singleT (inl x))) = conTL (singleT (inl (f x)))
mapTL κ f (conTL (singleT (inr x))) = stepTL κ (λ α → mapTL κ f (x α))
mapTL κ f (conTL (x ∪ₜ y)) = (mapTL κ f (conTL x)) ∪ₜₗ (mapTL κ f (conTL y))
mapTL κ f (conTL (unitrT x i)) = unitrTL (mapTL κ f (conTL x)) i
mapTL κ f (conTL (unitlT x i)) = unitlTL (mapTL κ f (conTL x)) i
mapTL κ f (conTL (truncT T₁ T₂ x y i i₁)) = truncTL (mapTL κ f (conTL T₁)) (mapTL κ f (conTL T₂)) (\ j → mapTL κ f (conTL (x j))) (\ j → mapTL κ f (conTL (y j))) i i₁

--a bind operator to make MultiLift into a monad
bindTL : {A B : Set} (κ : Cl) → (A → (TreeLift B κ)) → TreeLift A κ → TreeLift B κ
bindTL κ f (conTL ∅t) = conTL ∅t
bindTL κ f (conTL (singleT (inl x))) = f x
bindTL κ f (conTL (singleT (inr x))) = stepTL κ (\ α → bindTL κ f (x α))
bindTL κ f (conTL (x ∪ₜ y)) = (bindTL κ f (conTL x)) ∪ₜₗ (bindTL κ f (conTL y))
bindTL κ f (conTL (unitrT x i)) = unitrTL (bindTL κ f (conTL x)) i
bindTL κ f (conTL (unitlT x i)) = unitlTL (bindTL κ f (conTL x)) i
bindTL κ f (conTL (truncT T₁ T₂ x y i i₁)) = truncTL (bindTL κ f (conTL T₁)) (bindTL κ f (conTL T₂)) (\ j → bindTL κ f (conTL (x j))) (\ j → bindTL κ f (conTL (y j))) i i₁

--bindML commutes with ∪ₜₗ
bindTL-∪ₜₗ : {A B : Set} (κ : Cl) → ∀(f : A → (TreeLift B κ)) → ∀(tl sl : (TreeLift A κ)) → bindTL κ f (tl ∪ₜₗ sl) ≡ (bindTL κ f tl) ∪ₜₗ (bindTL κ f sl)
bindTL-∪ₜₗ κ f (conTL x) (conTL y) = refl

--***proof that MultiLift is a monad***--

--bindML and nowML need to be natural transformations
nattrans-nowTL : {A B : Set} (κ : Cl) → ∀(f : A → B) → ∀(x : A) → mapTL κ f (nowTL κ x) ≡ nowTL κ (f x)
nattrans-nowTL {A}{B} κ f x = refl

-- TODO: bindML

-- bindML and nowML also need to satisfy three monad laws:
-- unit is a left-identity for bind
unitlawTL1 : {A B : Set} (κ : Cl) → ∀ (f : A → (TreeLift B κ)) → ∀ (x : A) → (bindTL {A} κ f (nowTL κ x)) ≡ f x
unitlawTL1 κ f x = refl

-- unit is a right-identity for bind
unitlawTL2 : {A : Set}(κ : Cl) → ∀(x : (TreeLift A κ)) → (bindTL κ (nowTL κ) x) ≡ x
unitlawTL2 κ x = elimTL ((λ y → ((bindTL κ (nowTL κ) y) ≡ y) , truncTL (bindTL κ (nowTL κ) y) y)) 
                         refl
                         (λ y → refl)
                         (λ p → cong conTL (cong singleT (cong inr (later-ext (λ β → p β))))) 
                         (λ eq1 eq2 → cong₂ _∪ₜₗ_ eq1 eq2)
                         x
-- bind is associative
assoclawTL : {A B C : Set}(κ : Cl) → ∀(f : A → (TreeLift B κ)) → ∀ (g : B → (TreeLift C κ)) → ∀ (x : (TreeLift A κ))
                                   → (bindTL κ (\ y → (bindTL κ g (f y))) x) ≡ (bindTL κ g (bindTL κ f x))
assoclawTL {A} {B} {C} κ f g x = elimTL ((λ z → ((bindTL κ (\ y → (bindTL κ g (f y))) z) ≡ (bindTL κ g (bindTL κ f z))) ,
                                                  truncTL ((bindTL κ (\ y → (bindTL κ g (f y))) z)) (bindTL κ g (bindTL κ f z))))
                                        refl
                                        (λ y → refl)
                                        (λ p → cong conTL (cong singleT (cong inr (later-ext (λ α → p α)))))
                                        (λ {t s} → λ eq1 eq2 → (bindTL κ (λ y → bindTL κ g (f y)) (conTL t) ∪ₜₗ
                                                                bindTL κ (λ y → bindTL κ g (f y)) (conTL s))
                                                                ≡⟨ cong₂ (_∪ₜₗ_) eq1 eq2 ⟩
                                                                (bindTL κ g (bindTL κ f (conTL t)) ∪ₜₗ bindTL κ g (bindTL κ f (conTL s)))
                                                                ≡⟨ sym (bindTL-∪ₜₗ κ g (bindTL κ f (conTL t)) (bindTL κ f (conTL s))) ⟩
                                                                bindTL κ g (bindTL κ f (conTL t) ∪ₜₗ bindTL κ f (conTL s)) ∎)
                                         x

--*************************************************************************************--
-- Step 3: The TreeLift monad as the free delay-algebra and commutiative monoid monad --
--*************************************************************************************--

-- We already know that (TreeLift, stepTL) forms a delay algebra structure,
-- and (Treelift, conTL ∅t , ∪ₜₗ) forms a unital magma.
-- What we need to show is that TreeLift is the free monad with these properties.
-- That is, for a set A, and any other structure (B, δ, ε, _·_) where (B, δ) is a delay algebra and (B, ε, _·_) a unital magma,
-- given a function f : A → B, there is a unique function TreeLift A → B extending f that preserves the algebra structures.

record IsUMagma {A : Set} (ε : A) (_·_ : A → A → A) : Set where
  constructor isunitmagma

  field
    unitreq : (x : A) → x · ε ≡ x
    unitleq : (x : A) → ε · x ≡ x

record IsDelayUMagma {A : Set}(κ : Cl) (dm : DelayMonoidData A κ) : Set where
  constructor isdelayumagma

  open DelayMonoidData dm
  field
    isUMagma : IsUMagma (ε) (_·_)
    isDelayalg : IsDelayalg κ (nextA)

  open IsUMagma isUMagma public
  open IsDelayalg isDelayalg public


record IsExtendingTL {A B : Set}{κ : Cl} (f : A → B) (h : (TreeLift A κ) → B) : Set where
  constructor isextendingTL

  field
    extends : (x : A) → h (nowTL κ x) ≡ (f x)

--foldTL defines the function we are after
foldTL : {A B : Set}{κ : Cl} → isSet A → isSet B → ∀ dm → IsDelayUMagma {B} κ dm → (A → B) → (TreeLift A κ) → B
foldTL setA setB (dmdata nextB ε _·_) isDMB f (conTL ∅t) = ε
foldTL setA setB (dmdata nextB ε _·_) isDMB f (conTL (singleT (inl x))) = f x
foldTL setA setB dm@(dmdata nextB ε _·_) isDMB f (conTL (singleT (inr x))) = nextB (λ α → foldTL setA setB dm isDMB f (x α))
foldTL setA setB dm@(dmdata nextB ε _·_) isDMB f (conTL (x ∪ₜ y)) = (foldTL setA setB dm isDMB f (conTL x)) · (foldTL setA setB dm isDMB f (conTL y))
foldTL setA setB dm@(dmdata nextB ε _·_) isDMB f (conTL (unitrT x i)) = IsDelayUMagma.unitreq isDMB (foldTL setA setB dm isDMB f (conTL x)) i
foldTL setA setB dm@(dmdata nextB ε _·_) isDMB f (conTL (unitlT x i)) = IsDelayUMagma.unitleq isDMB (foldTL setA setB dm isDMB f (conTL x)) i
foldTL setA setB dm@(dmdata nextB ε _·_) isDMB f (conTL (truncT T₁ T₂ x y i i₁)) = setB (foldTL setA setB dm isDMB f (conTL T₁))
                                                                                          (foldTL setA setB dm isDMB f (conTL T₂))
                                                                                          (λ j → (foldTL setA setB dm isDMB f (conTL (x j))))
                                                                                          (λ j → (foldTL setA setB dm isDMB f (conTL (y j))))
                                                                                          i i₁


--foldTL extends the function f : A → B
foldTL-extends : {A B : Set}{κ : Cl} → ∀(setA : isSet A) → ∀(setB : isSet B) → ∀ dm → ∀(isDMB : IsDelayUMagma {B} κ dm) →
                                       ∀ (f : A → B) → IsExtendingTL f (foldTL setA setB dm isDMB f)
IsExtendingTL.extends (foldTL-extends setA setB dm isDMB f) x = refl

-- or a more direct proof of the same fact:
foldTL-extends-f : {A B : Set}{κ : Cl} → ∀(setA : isSet A) → ∀(setB : isSet B) → ∀ dm → ∀(isDMB : IsDelayUMagma {B} κ dm) →
                                         ∀ (f : A → B) → ∀ (x : A) → foldTL setA setB dm isDMB f (nowTL κ x) ≡ f x
foldTL-extends-f setA setB dm isDMB f x = refl

--foldTL preseves the DelayMonoid structure
 
module _ {A B : Set}{κ : Cl} (setA : isSet A) (setB : isSet B) (dm : _) (isDMB : IsDelayUMagma {B} κ dm)
         (f : A → B)
 where
  open IsPreservingDM
  open DelayMonoidData dm renaming (nextA to nextB)

  foldTL-preserves : IsPreservingDM {TreeLift A κ}{B} κ (dmdata (stepTL κ) (conTL ∅t) _∪ₜₗ_) dm (foldTL setA setB dm isDMB f)
  unit-preserve foldTL-preserves = refl
  next-preserve foldTL-preserves x = cong nextB (later-ext (λ α → refl))
  union-preserve foldTL-preserves (conTL x) (conTL y) = refl

--and foldTL is unique in doing so.
--That is, for any function h that both preserves the algebra structure
--and extends the function f : A → B,
--h is equivalent to fold.

module _ {A B : Set} {κ : Cl} (h : TreeLift A κ → B)
                     (setA : isSet A) (setB : isSet B) (dm : _) (isDMB : IsDelayUMagma {B} κ dm)
                     (f : A → B) (isPDM : IsPreservingDM {TreeLift A κ}{B} κ (dmdata (stepTL κ) (conTL ∅t) _∪ₜₗ_ ) dm h)
                     (isExt : IsExtendingTL f h) where

  open DelayMonoidData dm renaming (nextA to nextB)

  fold-uniquenessTL : (x : (TreeLift A κ)) → h x ≡ (foldTL setA setB dm isDMB f x)
  fold-uniquenessTL x = elimTL
                           ((λ x → (h x ≡ (foldTL setA setB dm isDMB f x)) , setB (h x) ((foldTL setA setB dm isDMB f x))))
                           (IsPreservingDM.unit-preserve isPDM)
                           (λ a →  h (conTL (singleT (inl a)))
                                    ≡⟨ refl ⟩
                                    h (nowTL κ a)
                                    ≡⟨ IsExtendingTL.extends isExt a ⟩
                                    f a ∎)
                           (λ {x} → λ eq → h (conTL (singleT (inr x)))
                                            ≡⟨ refl ⟩
                                            h (stepTL κ x)
                                            ≡⟨ IsPreservingDM.next-preserve isPDM x ⟩
                                            nextB (λ α → h (x α)) 
                                            ≡⟨ cong nextB (later-ext (λ α → (eq α)))  ⟩ 
                                            nextB (λ α → foldTL setA setB (dmdata nextB ε _·_) isDMB f (x α)) ∎)
                           (λ {x y} → λ eqx eqy → h (conTL (x ∪ₜ y))
                                                   ≡⟨ refl ⟩
                                                   h ((conTL x) ∪ₜₗ (conTL y))
                                                   ≡⟨ IsPreservingDM.union-preserve isPDM (conTL x) (conTL y) ⟩
                                                   (h (conTL x) · h (conTL y))
                                                   ≡⟨ cong₂ _·_ eqx eqy ⟩
                                                   (foldTL setA setB (dmdata nextB ε _·_) isDMB f (conTL x) ·
                                                    foldTL setA setB (dmdata nextB ε _·_) isDMB f (conTL y)) ∎)
                           x



--****************************************************--
-- Composing Lift and Tree via a distributive law --
--****************************************************--

--We now define a composite monad of the Tree and Lift monads, formed via a distributive law.
LcT : (A : Set) → (κ : Cl) → Set
LcT A κ = myLift (Tree A) κ

-- the unit of this monad is simply the composit of the units for Lift (nowL x) and Tree (singleT)
nowLcT : {A : Set} {κ : Cl} → A → (LcT A κ) 
nowLcT x = nowL (singleT x)

--LcT is a set.
truncLcT : {A : Set} {κ : Cl} → isSet (LcT A κ)
truncLcT = MyLiftSet.isSetmyLift truncT

--LLcT is a set
truncLLcT : {A : Set} {κ : Cl} → isSet (myLift (LcT A κ) κ)
truncLLcT = MyLiftSet.isSetmyLift truncLcT

-- we define a union on LcT, which will help in defining the distributive law.
_l∪t_ : {A : Set} {κ : Cl} → (LcT A κ) → (LcT A κ) → (LcT A κ)
nowL x l∪t nowL y = nowL (x ∪ₜ y)
nowL x l∪t stepL y = stepL (λ α → (nowL x l∪t (y α)))
stepL x l∪t y = stepL (λ α → ((x α) l∪t y))

lemma-stepLy : {A : Set} {κ : Cl} → ∀(x : (LcT A κ)) → ∀(y : ▹ κ (LcT A κ)) → x l∪t stepL y ≡ stepL (λ α → x l∪t (y α))
lemma-stepLy (nowL x) y = refl
lemma-stepLy (stepL x) y = stepL (λ α → x α l∪t stepL y)
                            ≡⟨ cong stepL (later-ext (λ α → lemma-stepLy (x α) y)) ⟩
                            stepL (λ α → stepL (λ β → x α l∪t y β))
                            ≡⟨ cong stepL (later-ext (λ α → cong stepL (later-ext (λ β → cong₂ _l∪t_ (tick-irr x α β) (sym (tick-irr y α β)))))) ⟩
                            stepL (λ α → stepL (λ β → x β l∪t y α)) ∎

--nowL ∅t is a unit for l∪t

unitr-l∪t : {A : Set} {κ : Cl} → ∀(x : LcT A κ) → x l∪t (nowL ∅t) ≡ x
unitr-l∪t (nowL x) = cong nowL (unitrT x)
unitr-l∪t (stepL x) = cong stepL (later-ext λ α → unitr-l∪t (x α))

unitl-l∪t : {A : Set} {κ : Cl} → ∀(x : LcT A κ) → (nowL ∅t) l∪t x ≡ x
unitl-l∪t (nowL x) = cong nowL (unitlT x)
unitl-l∪t (stepL x) = cong stepL (later-ext λ α → unitl-l∪t (x α))

lemma-nowL-l∪t-mapL : {A : Set} {κ : Cl} → ∀(x : LcT A κ) → ∀(T : Tree A) → nowL T l∪t x ≡ mapL κ (T ∪ₜ_) x
lemma-nowL-l∪t-mapL (nowL x) T = refl
lemma-nowL-l∪t-mapL (stepL x) T = cong stepL (later-ext (λ α → lemma-nowL-l∪t-mapL (x α) T))

dist-mapL-l∪t : {A B : Set} {κ : Cl} → ∀(f : (Tree A) → (Tree B)) → ∀(fdist : ∀(T S : Tree A) → f (T ∪ₜ S) ≡ f T ∪ₜ f S)
                                     → ∀(x y : (LcT A κ)) → mapL κ f (x l∪t y) ≡ (mapL κ f x) l∪t (mapL κ f y)
dist-mapL-l∪t f fdist (nowL x) (nowL y) = cong nowL (fdist x y)
dist-mapL-l∪t f fdist (nowL x) (stepL y) = cong stepL (later-ext λ α → dist-mapL-l∪t f fdist (nowL x) (y α))
dist-mapL-l∪t f fdist (stepL x) y = cong stepL (later-ext λ α → dist-mapL-l∪t f fdist (x α) y)


-- to prove the second multiplication law, I also need a ll∪t:
_ll∪t_ : {A : Set} {κ : Cl} → (myLift (LcT A κ) κ) → (myLift (LcT A κ) κ) → (myLift (LcT A κ) κ)
nowL x ll∪t nowL y = nowL (x l∪t y)
nowL x ll∪t stepL y = stepL (λ α → (nowL x ll∪t (y α)))
stepL x ll∪t y = stepL (λ α → ((x α) ll∪t y))

unitr-ll∪t : {A : Set} {κ : Cl} → ∀(x : myLift (LcT A κ) κ) → x ll∪t nowL (nowL ∅t) ≡ x
unitr-ll∪t (nowL x) = cong nowL (unitr-l∪t x)
unitr-ll∪t (stepL x) = cong stepL (later-ext λ α → unitr-ll∪t (x α))

unitl-ll∪t : {A : Set} {κ : Cl} → ∀(x : myLift (LcT A κ) κ) → nowL (nowL ∅t) ll∪t x ≡ x
unitl-ll∪t (nowL x) = cong nowL (unitl-l∪t x)
unitl-ll∪t (stepL x) = cong stepL (later-ext λ α → unitl-ll∪t (x α))

lemma-nowL-ll∪t-mapL : {A : Set} {κ : Cl} → ∀(x : myLift (LcT A κ) κ) → ∀(T : LcT A κ) → nowL T ll∪t x ≡ mapL κ (T l∪t_) x
lemma-nowL-ll∪t-mapL (nowL x) T = refl
lemma-nowL-ll∪t-mapL (stepL x) T = cong stepL (later-ext (λ α → lemma-nowL-ll∪t-mapL (x α) T))

multL-ll∪t-l∪t : {A : Set} (κ : Cl) → ∀(x y : myLift (LcT A κ) κ) → MultL κ (x ll∪t y) ≡ MultL κ x l∪t MultL κ y
multL-ll∪t-l∪t κ (nowL x) (nowL y) = refl
multL-ll∪t-l∪t κ (nowL x) (stepL y) = stepL (λ α → MultL κ (nowL x ll∪t y α))
                                          ≡⟨ cong stepL (later-ext(λ α → multL-ll∪t-l∪t κ (nowL x) (y α) )) ⟩
                                          stepL (λ α → MultL κ (nowL x) l∪t MultL κ (y α))
                                          ≡⟨ refl ⟩
                                          stepL (λ α → x l∪t MultL κ (y α))
                                          ≡⟨ sym (lemma-stepLy x ((λ α → MultL κ (y α)))) ⟩    
                                          (x l∪t stepL (λ α → MultL κ (y α))) ∎
multL-ll∪t-l∪t κ (stepL x) y = cong stepL (later-ext (λ α → multL-ll∪t-l∪t κ (x α) y))

-- LcT is a monad via a distributive law, distributing Tree over Lift.
-- Here is the distributive law:
distlawLcT : {A : Set} {κ : Cl} → Tree (myLift A κ) → (LcT A κ)
distlawLcT ∅t = nowL ∅t
distlawLcT (singleT (nowL x)) = nowL (singleT x)
distlawLcT (singleT (stepL x)) = stepL (λ α → distlawLcT (singleT (x α)))
distlawLcT (x ∪ₜ y) = (distlawLcT x) l∪t (distlawLcT y)
distlawLcT (unitrT x i) = unitr-l∪t (distlawLcT x) i
distlawLcT (unitlT x i) = unitl-l∪t (distlawLcT x) i
distlawLcT (truncT T₁ T₂ x y i i₁) = truncLcT (distlawLcT T₁) (distlawLcT T₂) (λ j → distlawLcT (x j)) (λ j → distlawLcT (y j)) i i₁

--proof that distlawLcT is indeed a distributive law:
--unit laws:
unitlawLcT1 : {A : Set} {κ : Cl} → ∀(x : myLift A κ) → (distlawLcT (singleT x)) ≡  mapL κ singleT x
unitlawLcT1 (nowL x) = refl
unitlawLcT1 (stepL x) = cong stepL (later-ext λ α → unitlawLcT1 (x α))

unitlawLcT2 : {A : Set} {κ : Cl} → ∀(T : Tree A) → (distlawLcT {A}{κ} (mapT nowL T)) ≡ nowL T
unitlawLcT2 T = elimT
                 (λ T → ((distlawLcT (mapT nowL T) ≡ nowL T) , truncLcT (distlawLcT (mapT nowL T)) (nowL T)))
                 refl
                 (λ T → refl)
                 (λ {T S} → λ eqT eqS → distlawLcT (mapT nowL T) l∪t distlawLcT (mapT nowL S)
                                         ≡⟨ cong₂ (_l∪t_) eqT eqS ⟩
                                         ((nowL T) l∪t (nowL S))
                                         ≡⟨ refl ⟩
                                         nowL (T ∪ₜ S) ∎ )
                 T


--multiplication laws:
multlawLcM1 : {A : Set} (κ : Cl) → ∀(T : Tree (Tree (myLift A κ))) → distlawLcT (MultT T) ≡
                                                                     mapL κ MultT (distlawLcT (mapT distlawLcT T))
multlawLcM1 κ T = elimT
                    (λ T → ((distlawLcT (MultT T) ≡ mapL κ MultT (distlawLcT (mapT distlawLcT T))) ,
                             truncLcT (distlawLcT (MultT T)) (mapL κ MultT (distlawLcT (mapT distlawLcT T))) ))
                    refl
                    (λ T → distlawLcT T
                            ≡⟨ sym (mapL-identity (distlawLcT T)) ⟩
                            mapL κ (λ y → y) (distlawLcT T)
                            ≡⟨ cong₂ (mapL κ) (funExt (λ y → sym (Tree-unitlaw1 y))) refl ⟩
                            mapL κ (λ y → MultT (singleT y)) (distlawLcT T)
                            ≡⟨ sym (mapmapL κ singleT MultT (distlawLcT T)) ⟩
                            mapL κ MultT (mapL κ singleT (distlawLcT T)) 
                            ≡⟨ cong (mapL κ MultT) (sym (unitlawLcT1 (distlawLcT T)))  ⟩
                            mapL κ MultT (distlawLcT (singleT (distlawLcT T))) ∎)
                    (λ {T S} → λ eqT eqS → (distlawLcT (MultT T) l∪t distlawLcT (MultT S))
                              ≡⟨ cong₂ _l∪t_ eqT eqS ⟩
                              (mapL κ MultT (distlawLcT (mapT distlawLcT T)) l∪t mapL κ MultT (distlawLcT (mapT distlawLcT S)))
                              ≡⟨ sym (dist-mapL-l∪t MultT (λ x y → refl) (distlawLcT (mapT distlawLcT T)) (distlawLcT (mapT distlawLcT S))) ⟩
                              mapL κ MultT (distlawLcT (mapT distlawLcT T) l∪t distlawLcT (mapT distlawLcT S)) ∎)
                    T 


-- lemma before we can do the second multiplication law,
lemma-dist-llut : {A : Set} {κ : Cl} → ∀(D1 D2 : (myLift (Tree (myLift A κ)) κ)) →
                                       mapL κ distlawLcT (D1 l∪t D2) ≡ (mapL κ distlawLcT D1) ll∪t (mapL κ distlawLcT D2)
lemma-dist-llut (nowL x) (nowL y) = refl
lemma-dist-llut (nowL x) (stepL y) = cong stepL (later-ext (λ α → lemma-dist-llut (nowL x) (y α)))
lemma-dist-llut (stepL x) D2 = cong stepL (later-ext (λ α → lemma-dist-llut (x α) D2))

-- I don't know how to split cases within elimT, so here is a lemma for the singelT case of elimT for multlawLcT2, split into nowL and stepL:
multlawLcT2-singleTcase : {A : Set} {κ : Cl} → ∀(x : (myLift (myLift A κ) κ)) →
                                               distlawLcT (mapT (MultL κ) (singleT x)) ≡ MultL κ (mapL κ distlawLcT (distlawLcT (singleT x)))
multlawLcT2-singleTcase (nowL x) = refl
multlawLcT2-singleTcase (stepL x) = cong stepL (later-ext λ α → multlawLcT2-singleTcase (x α))

-- and here the full proof of the second multiplication law:
multlawLcT2 : {A : Set} (κ : Cl) → ∀(T : Tree (myLift (myLift A κ) κ)) →
                                     distlawLcT (mapT (MultL κ) T) ≡ MultL κ (mapL κ distlawLcT (distlawLcT T))
multlawLcT2 κ T = elimT
                   (λ T → ((distlawLcT (mapT (MultL κ) T) ≡ MultL κ (mapL κ distlawLcT (distlawLcT T))) ,
                            truncLcT (distlawLcT (mapT (MultL κ) T)) (MultL κ (mapL κ distlawLcT (distlawLcT T)))))
                   refl
                   (λ x → multlawLcT2-singleTcase x )
                   (λ {T S} → λ eqT eqS → distlawLcT (mapT (MultL κ) T) l∪t distlawLcT (mapT (MultL κ) S)
                                           ≡⟨ cong₂ (_l∪t_) eqT eqS ⟩
                                           (MultL κ (mapL κ distlawLcT (distlawLcT T)) l∪t MultL κ (mapL κ distlawLcT (distlawLcT S)))
                                           ≡⟨ sym (multL-ll∪t-l∪t κ ((mapL κ distlawLcT (distlawLcT T))) (mapL κ distlawLcT (distlawLcT S))) ⟩
                                           MultL κ ((mapL κ distlawLcT (distlawLcT T)) ll∪t (mapL κ distlawLcT (distlawLcT S)))
                                           ≡⟨ cong (MultL κ) (sym (lemma-dist-llut (distlawLcT T)(distlawLcT S) )) ⟩
                                           MultL κ (mapL κ distlawLcT (distlawLcT T l∪t distlawLcT S)) ∎)
                   T
