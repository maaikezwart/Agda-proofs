{-# OPTIONS --cubical --guarded --rewriting -W ignore #-}
module combinations-of-lift-and-powerset-failing-withNiccoloCode where

import Agda.Builtin.Equality as R
import Agda.Builtin.Equality.Rewrite as R

open import Clocked.Primitives
open import Cubical.Foundations.Everything
open import Cubical.Data.List as List
open import Cubical.Data.List.Properties
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Sigma
open import combinations-of-lift-and-list
open import Cubical.Data.Empty as ⊥
open import Agda.Builtin.Unit

--The following code is from Niccolo Veltri
--source: https://github.com/niccoloveltri/final-pfin/blob/main/Pfin/AsFreeJoinSemilattice.agda
--It defines the powerset functor as a HIT, and proves several properties about subsets that we need here.
open import PfinAsFreeJoinSemilattice renaming (Pfin to Powerset; mapPfin to mapP; elimPfinProp to elimP; _∪_ to _∪ₚ_; nr to unitr; ø to ∅)


--**************************************************************************************--
--**************************************************************************************--
-- Combining the monads Lift and Powerset freely, but impossible via a distributive law --
--**************************************************************************************--
--**************************************************************************************--

-- In this document I want to define a monad, called PowerLift, that is the free combination of the Lift monad and the Powerset monad.
-- In order to do so, I will first define the the Powerset monad, and check that it is indeed a monad (Step 1).
-- Then I define the PowerLift monad, check that it is a monad (Step 2), and finally check that it is the free monad on the algebra
-- structures of a delay algebra and a commutative monoid (Step 3).
-- The Lift monad has aleady been defined in my earlier work, combinations-of-lift-and-list.


-- In addition to the free combination of the Powerset and the Lift monads, I will show that there is
-- no distributive law to form a monad LcP : A → Lift(Powerset A). 

--****************************--
-- Step 1: The Powerset monad --
--****************************--

--This code is based on the finite powerset example from:
--https://github.com/niccoloveltri/final-pfin/blob/main/Pfin/AsFreeJoinSemilattice.agda
--There, the finite powerset monad is defined as a HIT of the free semilattice functor on A.

--We extend the Powerset functor to a monad by defining a multiplication:

Powerset-mult : {A : Set} → Powerset (Powerset A) → Powerset A
Powerset-mult ∅ = ∅
Powerset-mult (η x) = x
Powerset-mult (x ∪ₚ y) = (Powerset-mult x) ∪ₚ (Powerset-mult y)
Powerset-mult (ass x y z i) = ass (Powerset-mult x) (Powerset-mult y) (Powerset-mult z) i
Powerset-mult (com x y i) = com (Powerset-mult x) (Powerset-mult y) i
Powerset-mult (idem x i) = idem (Powerset-mult x) i
Powerset-mult (unitr x i) = unitr (Powerset-mult x) i
Powerset-mult (trunc s₁ s₂ x y i i₁) = trunc (Powerset-mult s₁) (Powerset-mult s₂) (\ j → Powerset-mult (x j)) (\ j → Powerset-mult (y j)) i i₁

-- Proving that the Powerset forms a monad

-- Powerset-mult (unitM M) = M
Powerset-unitlaw1 : {A : Set} → ∀(X : Powerset A) → Powerset-mult (η X) ≡ X
Powerset-unitlaw1 X = refl

-- Powerset-mult (map unitM M) = M
Powerset-unitlaw2 : {A : Set} → ∀(X : Powerset A) → Powerset-mult (mapP η X) ≡ X
Powerset-unitlaw2 X = elimP
                        (λ Y → (Powerset-mult (mapP η Y) ≡ Y) , trunc (Powerset-mult (mapP η Y)) Y)
                        refl
                        (λ Y → refl)
                        (λ eq1 → λ eq2 → cong₂ _∪ₚ_ eq1 eq2 )
                        X

-- Powerset-mult (Powerset-mult M) = Powerset-mult (mapP Powerset-mult X) 
Powerset-multlaw :  {A : Set} → ∀(X : Powerset (Powerset (Powerset A))) →  Powerset-mult (Powerset-mult X) ≡ Powerset-mult (mapP Powerset-mult X)
Powerset-multlaw X = elimP
                        (λ Y → (Powerset-mult (Powerset-mult Y) ≡ Powerset-mult (mapP Powerset-mult Y))
                              , trunc (Powerset-mult (Powerset-mult Y)) (Powerset-mult (mapP Powerset-mult Y)))
                        refl
                        (λ Y → refl)
                        (λ eq1 → λ eq2 → cong₂ (_∪ₚ_) eq1 eq2)
                        X

-- the unit is a natural transformation:
nattrans-Multunit : {A B : Set} → ∀(f : A → B) → ∀(x : A) → mapP f (η x) ≡ η (f x)
nattrans-Multunit f x = refl

-- the multiplication is a natural transformation:
nattrans-PowersetMult : {A B : Set} → ∀(f : A → B) → ∀(X : Powerset (Powerset A)) → mapP f (Powerset-mult X) ≡ Powerset-mult (mapP (mapP f) X)
nattrans-PowersetMult f X = elimP
                               ((λ Y →  (mapP f (Powerset-mult Y) ≡ Powerset-mult (mapP (mapP f) Y))
                                      , trunc (mapP f (Powerset-mult Y)) (Powerset-mult (mapP (mapP f) Y))))
                               refl
                               (λ Y → refl)
                               (λ eq1 → λ eq2 → cong₂ (_∪ₚ_) eq1 eq2)
                               X 


--induction under clocks:

module ∀ElimP
  {A : Cl → Set}
  {B : (∀ k → Powerset (A k)) → Set}
  (∅* : B (\ k → ∅))
  (unitP* : (x : ∀ k → A k) → B(\ k → η (x k)))
  (_∪ₚ*_ : {x y : ∀ k → Powerset (A k)} → (a : B x) → (b : B y) → B (\ k → (x k) ∪ₚ (y k)))
  (ass* : {x y z : ∀ k → Powerset (A k)} → (a : B x) → (b : B y) → (c : B z) → PathP (λ i → B (\ k → ass (x k) (y k) (z k) i)) (a ∪ₚ* (b ∪ₚ* c)) ((a ∪ₚ* b) ∪ₚ* c))
  (com* : {x y : ∀ k → Powerset (A k)} → (a : B x) → (b : B y) → PathP (λ i → B (\ k → com (x k) (y k) i)) (a ∪ₚ* b) (b ∪ₚ* a))
  (idem* : {x : ∀ k → Powerset (A k)} → (a : B x) → PathP (λ i → B (\ k → idem (x k) i)) (a ∪ₚ* a) (a))
  (unitr* : {x : ∀ k → Powerset (A k)} → (a : B x) → PathP (λ i → B (\ k → unitr (x k) i)) (a ∪ₚ* ∅*) (a))
  (trunc* : (x : ∀ k → Powerset (A k)) → isSet (B x))
  where

  postulate
    elimCP : ∀ x → B x

    elim-∅ : elimCP (\ k → ∅) R.≡ ∅*
    elim-η  : (x : ∀ k → A k) → elimCP (\ k → η (x k)) R.≡ unitP* x
    elim-∪ₚ : (x y : ∀ k → Powerset (A k)) → elimCP (\ k → x k ∪ₚ y k) R.≡ elimCP x ∪ₚ* elimCP y

  {-# REWRITE elim-∅ elim-η elim-∪ₚ #-}

  -- we have to add the rewrites above for the following rewrite rules to typecheck.
  postulate
    elim-ass : (x y z : ∀ k → Powerset (A k)) (i : I) → elimCP (\ k → ass (x k) (y k) (z k) i) R.≡ ass* (elimCP x) (elimCP y) (elimCP z) i
    elim-com : (x y : ∀ k → Powerset (A k)) (i : I) → elimCP (\ k → com (x k) (y k) i) R.≡ com* (elimCP x) (elimCP y) i
    elim-idem : (x : ∀ k → Powerset (A k)) (i : I) → elimCP (\ k → idem (x k) i) R.≡ idem* (elimCP x) i
    elim-unitr : (x : ∀ k → Powerset (A k)) (i : I) → elimCP (\ k → unitr (x k) i) R.≡ unitr* (elimCP x) i
    elim-trunc : {x y : ∀ k → Powerset (A k)} (p q : ∀ k → x k ≡ y k) (i j : I) →
                 elimCP (\ k → trunc (x k) (y k) (p k) (q k) i j) R.≡
                 isOfHLevel→isOfHLevelDep 2 trunc* (elimCP x) (elimCP y)
                                            (\ j → elimCP (\ k → p k j))
                                            (\ j → elimCP (\ k → q k j))
                                            (λ i j k → trunc (x k) (y k) (p k) (q k) i j)
                                            i j

  {-# REWRITE elim-ass elim-com elim-idem elim-unitr elim-trunc #-}

-- Powerset commutes with ∀ κ
dist∀Pow : ∀ {A : Cl → Set} → (∀ κ → Powerset (A κ)) → Powerset (∀ κ → A κ)
dist∀Pow = ∀ElimP.elimCP ∅ η _∪ₚ_ ass com idem unitr λ x → λ y → trunc y



--*****************************--
-- Step 2: The PowerLift monad --
--*****************************--

--Now that we have a powerset monad and a lift monad, I want to show that the following combination of the two is again a monad:
--PowerLift : (A : Set) → (κ : Cl) → Set
--PowerLift A κ = Powerset (A ⊎ (▹ κ (PowerLift A κ)))

data PowerLift (A : Set) (κ : Cl) : Set where
  conPL : Powerset (A ⊎ (▹ κ (PowerLift A κ))) -> PowerLift A κ

-- Elimination principle for PowerLift

-- module to make the inputs more readable
-- no name for the module to make the use of it more readable
module _ {ℓ}{A : Set}{κ : Cl}
         (P : PowerLift A κ → hProp ℓ)
         (P∅ : fst (P (conPL ∅)))
         (Pη1 : ∀ x → fst (P (conPL (η (inl x)))))
         (Pη2 : ∀ {x} → (∀ α → fst (P (x α))) → fst (P (conPL (η (inr x)))))
         (P∪ : ∀ {x y} → fst(P (conPL x)) → fst(P (conPL y)) → fst(P (conPL (x ∪ₚ y))))
         where

  elimPL : ∀ M → fst(P M)
  elimPL (conPL ∅) = P∅
  elimPL (conPL (η (inl x))) = Pη1 x
  elimPL (conPL (η (inr x))) = Pη2 λ α → elimPL (x α) 
  elimPL (conPL (x ∪ₚ y)) = P∪ (elimPL (conPL x)) (elimPL (conPL y))
  elimPL (conPL (ass X Y Z i)) = isProp→PathP (λ j → snd (P (conPL (ass X Y Z j))))
                               ((P∪ (elimPL (conPL X)) (P∪ (elimPL (conPL Y)) (elimPL (conPL Z)))))
                               ((P∪ (P∪ (elimPL (conPL X)) (elimPL (conPL Y))) (elimPL (conPL Z)) ))
                               i
  elimPL (conPL (com X Y i)) = isProp→PathP (λ j → snd (P (conPL (com X Y j)))) (P∪ (elimPL (conPL X)) (elimPL (conPL Y))) (P∪ (elimPL (conPL Y)) (elimPL (conPL X))) i
  elimPL (conPL (idem X i)) = isProp→PathP (λ j → snd (P (conPL (idem X j)))) (P∪ (elimPL (conPL X)) (elimPL (conPL X))) (elimPL (conPL X)) i  
  elimPL (conPL (unitr X i)) = isProp→PathP (λ j → snd (P (conPL (unitr X j)))) (P∪ (elimPL (conPL X)) (P∅)) (elimPL (conPL X)) i
  elimPL (conPL (trunc X Y x y i j)) = isOfHLevel→isOfHLevelDep 2 (λ z → isProp→isSet (snd (P (conPL z)))) (elimPL (conPL X)) (elimPL (conPL Y))
                                        (cong elimPL (cong conPL x)) (cong elimPL (cong conPL y)) (trunc X Y x y ) i j

--***proof that PowerLift is a set***--
-- strategy: build isomorphism, then make equivalence, then use univalence to turn equivalence into equality, then transport.

isoPL :  {A : Set}{κ : Cl} → Iso (Powerset (A ⊎ (▹ κ (PowerLift A κ)))) (PowerLift A κ)  
Iso.fun isoPL = conPL
Iso.inv isoPL (conPL x) = x
Iso.rightInv isoPL (conPL x) = refl
Iso.leftInv isoPL a = refl

equivPL :  {A : Set}{κ : Cl} → (Powerset (A ⊎ (▹ κ (PowerLift A κ)))) ≃ (PowerLift A κ)
equivPL = isoToEquiv isoPL

equalPL : {A : Set}{κ : Cl} → (Powerset (A ⊎ (▹ κ (PowerLift A κ)))) ≡ (PowerLift A κ)
equalPL = ua equivPL

truncPL : {A : Set} {κ : Cl} → isSet (PowerLift A κ)
truncPL = subst⁻ isSet (sym equalPL) trunc

--IsotoPath as shortcut for this bit of code

--***algebraic structure for PowerLift***--

--nowPL and stepPL turn PowerLift into a delay algebra structure:
nowPL : {A : Set} (κ : Cl) → A → (PowerLift A κ)
nowPL κ a = conPL (η (inl a))

stepPL : {A : Set} (κ : Cl) → ▹ κ (PowerLift A κ) → (PowerLift A κ)
stepPL κ a = conPL (η (inr a))

--the union is derived from the powerset union, and turns PowerLift into a commutative and idempotent monoid:
_∪ₚₗ_ : {A : Set} {κ : Cl} → (PowerLift A κ) → (PowerLift A κ) → (PowerLift A κ)
_∪ₚₗ_ {A} {κ} (conPL x) (conPL y) = conPL (x ∪ₚ y)

--proof that this union does indeed provide a commutative monoid structure: 
assoc∪ₚₗ : {A : Set} {κ : Cl} → ∀(xl yl zl : (PowerLift A κ)) → (xl ∪ₚₗ yl) ∪ₚₗ zl ≡ xl ∪ₚₗ (yl ∪ₚₗ zl)
assoc∪ₚₗ {A} {κ} (conPL x) (conPL y) (conPL z) = cong conPL (sym (ass x y z))

comm∪ₚₗ : {A : Set} {κ : Cl} → ∀(xl yl : (PowerLift A κ)) → xl ∪ₚₗ yl ≡ yl ∪ₚₗ xl
comm∪ₚₗ {A} {κ} (conPL x) (conPL y) = cong conPL (com x y)

idem∪ₚₗ : {A : Set} {κ : Cl} → ∀ (xl : (PowerLift A κ)) → xl ∪ₚₗ xl ≡ xl
idem∪ₚₗ {A} {κ} (conPL x) = cong conPL (idem x)

unitr∪ₚₗ : {A : Set} {κ : Cl} → ∀ (xl : (PowerLift A κ)) → xl ∪ₚₗ conPL ∅ ≡ xl
unitr∪ₚₗ {A} {κ} (conPL x) = cong conPL (unitr x)


--***monadic structure for PowerLift***--

--a map function to turn PowerLift into a functor
mapPL : {A B : Set} (κ : Cl) → (f : A → B) → (PowerLift A κ) → (PowerLift B κ)
mapPL κ f (conPL ∅) = conPL ∅
mapPL κ f (conPL (η (inl x))) = conPL (η (inl (f x)))
mapPL κ f (conPL (η (inr x))) = stepPL κ (λ α → mapPL κ f (x α))
mapPL κ f (conPL (x ∪ₚ y)) = (mapPL κ f (conPL x)) ∪ₚₗ (mapPL κ f (conPL y))
mapPL κ f (conPL (ass x y z i)) = sym (assoc∪ₚₗ (mapPL κ f (conPL x)) (mapPL κ f (conPL y)) (mapPL κ f (conPL z))) i
mapPL κ f (conPL (com x y i)) = comm∪ₚₗ (mapPL κ f (conPL x)) (mapPL κ f (conPL y)) i 
mapPL κ f (conPL (idem x i)) = idem∪ₚₗ (mapPL κ f (conPL x)) i
mapPL κ f (conPL (unitr x i)) = unitr∪ₚₗ (mapPL κ f (conPL x)) i
mapPL κ f (conPL (trunc x y z w i i₁)) = truncPL (mapPL κ f (conPL x)) (mapPL κ f (conPL y)) (\ j → mapPL κ f (conPL (z j))) (\ j → mapPL κ f (conPL (w j))) i i₁

--a bind operator to make PowerLift into a monad
bindPL : {A B : Set} (κ : Cl) → (A → (PowerLift B κ)) → PowerLift A κ → PowerLift B κ
bindPL κ f (conPL ∅) = conPL ∅
bindPL κ f (conPL (η (inl x))) = f x
bindPL κ f (conPL (η (inr x))) = stepPL κ (\ α → bindPL κ f (x α))
bindPL κ f (conPL (x ∪ₚ y)) = (bindPL κ f (conPL x)) ∪ₚₗ (bindPL κ f (conPL y))
bindPL κ f (conPL (ass x y z i)) = sym (assoc∪ₚₗ (bindPL κ f (conPL x)) (bindPL κ f (conPL y)) (bindPL κ f (conPL z))) i
bindPL κ f (conPL (com x y i)) = comm∪ₚₗ (bindPL κ f (conPL x)) (bindPL κ f (conPL y)) i
bindPL κ f (conPL (idem x i)) = idem∪ₚₗ (bindPL κ f (conPL x)) i
bindPL κ f (conPL (unitr x i)) = unitr∪ₚₗ (bindPL κ f (conPL x)) i
bindPL κ f (conPL (trunc x y z w i i₁)) = truncPL (bindPL κ f (conPL x)) (bindPL κ f (conPL y)) (\ j → bindPL κ f (conPL (z j))) (\ j → bindPL κ f (conPL (w j))) i i₁

--bindPL commutes with ∪ₚₗ
bindPL-∪ₚₗ : {A B : Set} (κ : Cl) → ∀(f : A → (PowerLift B κ)) → ∀(xl yl : (PowerLift A κ)) → bindPL κ f (xl ∪ₚₗ yl) ≡ (bindPL κ f xl) ∪ₚₗ (bindPL κ f yl)
bindPL-∪ₚₗ κ f (conPL x) (conPL y) = refl

--***proof that PowerLift is a monad***--

--bindPL and nowPL need to be natural transformations
nattrans-nowPL : {A B : Set} (κ : Cl) → ∀(f : A → B) → ∀(x : A) → mapPL κ f (nowPL κ x) ≡ nowPL κ (f x)
nattrans-nowPL {A}{B} κ f x = refl

-- TODO: bindPL

-- bindPL and nowPL also need to satisfy three monad laws:
-- unit is a left-identity for bind
unitlawPL1 : {A B : Set} (κ : Cl) → ∀ (f : A → (PowerLift B κ)) → ∀ (x : A) → (bindPL {A} κ f (nowPL κ x)) ≡ f x
unitlawPL1 κ f x = refl

-- unit is a right-identity for bind
unitlawPL2 : {A : Set}(κ : Cl) → ∀(x : (PowerLift A κ)) → (bindPL κ (nowPL κ) x) ≡ x
unitlawPL2 κ x = elimPL ((λ y → ((bindPL κ (nowPL κ) y) ≡ y)
                           , truncPL (bindPL κ (nowPL κ) y) y)) 
                         refl
                         (λ y → refl)
                         (λ p → cong conPL (cong η (cong inr (later-ext (λ β → p β))))) 
                         (λ eq1 → λ eq2 → cong₂ _∪ₚₗ_ eq1 eq2)
                         x
-- bind is associative
assoclawPL : {A B C : Set}(κ : Cl) → ∀(f : A → (PowerLift B κ)) → ∀ (g : B → (PowerLift C κ)) → ∀ (x : (PowerLift A κ))
                     → (bindPL κ (\ y → (bindPL κ g (f y))) x) ≡ (bindPL κ g (bindPL κ f x))
assoclawPL {A} {B} {C} κ f g x = elimPL ((λ z → ((bindPL κ (\ y → (bindPL κ g (f y))) z) ≡ (bindPL κ g (bindPL κ f z)))
                                           , truncPL ((bindPL κ (\ y → (bindPL κ g (f y))) z)) (bindPL κ g (bindPL κ f z))))
                                        refl
                                        (λ y → refl)
                                        (λ p → cong conPL (cong η (cong inr (later-ext (λ α → p α)))))
                                        (λ {x y} → λ eq1 → λ eq2 → (bindPL κ (λ y → bindPL κ g (f y)) (conPL x) ∪ₚₗ
                                                           bindPL κ (λ y → bindPL κ g (f y)) (conPL y))
                                                           ≡⟨ cong₂ (_∪ₚₗ_) eq1 eq2 ⟩
                                                           (bindPL κ g (bindPL κ f (conPL x)) ∪ₚₗ bindPL κ g (bindPL κ f (conPL y)))
                                                           ≡⟨ sym (bindPL-∪ₚₗ κ g (bindPL κ f (conPL x)) (bindPL κ f (conPL y))) ⟩
                                                            bindPL κ g (bindPL κ f (conPL x) ∪ₚₗ bindPL κ f (conPL y)) ∎)
                                        x


--*************************************************************************************--
-- Step 3: The PowerLift monad as the free delay-algebra and commutiative monoid monad --
--*************************************************************************************--

-- We already know that (PowerLift, stepPL) forms a delay algebra structure,
-- and (Powerlift, conPL m∅ ,  ∪ₘₗ) forms a commutative, idempotent monoid.
-- What we need to show is that PowerLift is the free monad with these properties.
-- That is, for a set A, and any other structure (B, δ, ε, _·_) where (B, δ) is a delay algebra and (B, ε, _·_) a commutative and idempotent monoid
-- given a function f : A → B, there is a unique function PowerLift A → B extending f that preserves the algebra structures.

record IsCIMonoid {A : Set} (ε : A) (_·_ : A → A → A) : Set where
  constructor iscimonoid

  field
    asso : (x y z : A) → (x · y) · z ≡ x · (y · z)
    comm : (x y : A) → (x · y) ≡ (y · x)
    idemp : (x : A) → (x · x) ≡ x
    uniteq : (x : A) → x · ε ≡ x

record IsDelayCIMonoid {A : Set}(κ : Cl) (dm : DelayMonoidData A κ) : Set where
  constructor isdelaycimonoid

  open DelayMonoidData dm
  field
    isCIMonoid : IsCIMonoid (ε) (_·_)
    isDelayalg : IsDelayalg κ (nextA)

  open IsCIMonoid isCIMonoid public
  open IsDelayalg isDelayalg public


record IsExtendingPL {A B : Set}{κ : Cl} (f : A → B) (h : (PowerLift A κ) → B) : Set where
  constructor isextendingPL

  field
    extends : (x : A) → h (nowPL κ x) ≡ (f x)

--foldPL defines the function we are after
foldPL : {A B : Set}{κ : Cl} → isSet A → isSet B → ∀ dm → IsDelayCIMonoid {B} κ dm → (A → B) → (PowerLift A κ) → B
foldPL setA setB (dmdata nextB ε _·_) isDMB f (conPL ∅) = ε
foldPL setA setB (dmdata nextB ε _·_) isDMB f (conPL (η (inl x))) = f x
foldPL setA setB dm@(dmdata nextB ε _·_) isDMB f (conPL (η (inr x))) = nextB (λ α → foldPL setA setB dm isDMB f (x α))
foldPL setA setB dm@(dmdata nextB ε _·_) isDMB f (conPL (x ∪ₚ y)) = (foldPL setA setB dm isDMB f (conPL x)) · (foldPL setA setB dm isDMB f (conPL y))
foldPL setA setB dm@(dmdata nextB ε _·_) isDMB f (conPL (ass x y z i)) = sym (IsDelayCIMonoid.asso isDMB (foldPL setA setB dm isDMB f (conPL x))
                                                                                                     (foldPL setA setB dm isDMB f (conPL y))
                                                                                                     (foldPL setA setB dm isDMB f (conPL z))) i
foldPL setA setB dm@(dmdata nextB ε _·_) isDMB f (conPL (com x y i)) = IsDelayCIMonoid.comm isDMB (foldPL setA setB dm isDMB f (conPL x)) (foldPL setA setB dm isDMB f (conPL y)) i
foldPL setA setB dm@(dmdata nextB ε _·_) isDMB f (conPL (idem x i)) = IsDelayCIMonoid.idemp isDMB (foldPL setA setB dm isDMB f (conPL x)) i
foldPL setA setB dm@(dmdata nextB ε _·_) isDMB f (conPL (unitr x i)) = IsDelayCIMonoid.uniteq isDMB (foldPL setA setB dm isDMB f (conPL x)) i
foldPL setA setB dm@(dmdata nextB ε _·_) isDMB f (conPL (trunc x y x₁ y₁ i i₁)) = setB (foldPL setA setB dm isDMB f (conPL x))
                                                                                      (foldPL setA setB dm isDMB f (conPL y))
                                                                                      (λ j → (foldPL setA setB dm isDMB f (conPL (x₁ j))))
                                                                                      (λ j → (foldPL setA setB dm isDMB f (conPL (y₁ j))))
                                                                                      i i₁


--foldPL extends the function f : A → B
foldPL-extends : {A B : Set}{κ : Cl} → ∀(setA : isSet A) → ∀(setB : isSet B) → ∀ dm → ∀(isDMB : IsDelayCIMonoid {B} κ dm) →
                   ∀ (f : A → B) → IsExtendingPL f (foldPL setA setB dm isDMB f)
IsExtendingPL.extends (foldPL-extends setA setB dm isDMB f) x = refl

-- or a more direct proof of the same fact:
foldPL-extends-f : {A B : Set}{κ : Cl} → ∀(setA : isSet A) → ∀(setB : isSet B) → ∀ dm → ∀(isDMB : IsDelayCIMonoid {B} κ dm) →
                   ∀ (f : A → B) → ∀ (x : A) → foldPL setA setB dm isDMB f (nowPL κ x) ≡ f x
foldPL-extends-f setA setB dm isDMB f x = refl

--foldPL preseves the DelayMonoid structure
 
module _ {A B : Set}{κ : Cl} (setA : isSet A) (setB : isSet B) (dm : _) (isDMB : IsDelayCIMonoid {B} κ dm)
         (f : A → B)
 where
  open IsPreservingDM
  open DelayMonoidData dm renaming (nextA to nextB)

  foldPL-preserves : IsPreservingDM {PowerLift A κ}{B} κ (dmdata (stepPL κ) (conPL ∅) _∪ₚₗ_) dm (foldPL setA setB dm isDMB f)
  unit-preserve foldPL-preserves = refl
  next-preserve foldPL-preserves x = cong nextB (later-ext (λ α → refl))
  union-preserve foldPL-preserves (conPL x) (conPL y) = refl

--and foldPL is unique in doing so.
--That is, for any function h that both preserves the algebra structure
--and extends the function f : A → B,
-- h is equivalent to fold.

module _ {A B : Set} {κ : Cl} (h : PowerLift A κ → B)
                       (setA : isSet A) (setB : isSet B) (dm : _) (isDMB : IsDelayCIMonoid {B} κ dm)
                       (f : A → B) (isPDM : IsPreservingDM {PowerLift A κ}{B} κ (dmdata (stepPL κ) (conPL ∅) _∪ₚₗ_ ) dm h)
                       (isExt : IsExtendingPL f h) where

  open DelayMonoidData dm renaming (nextA to nextB)

  fold-uniquenessPL : (x : (PowerLift A κ)) → h x ≡ (foldPL setA setB dm isDMB f x)
  fold-uniquenessPL x = elimPL
                           ((λ x → (h x ≡ (foldPL setA setB dm isDMB f x)) , setB (h x) ((foldPL setA setB dm isDMB f x))))
                           (IsPreservingDM.unit-preserve isPDM)
                           (λ a →  h (conPL (η (inl a)))
                                    ≡⟨ refl ⟩
                                    h (nowPL κ a)
                                    ≡⟨ IsExtendingPL.extends isExt a ⟩
                                    f a ∎)
                           (λ {x} → λ eq → h (conPL (η (inr x)))
                                            ≡⟨ refl ⟩
                                            h (stepPL κ x)
                                            ≡⟨ IsPreservingDM.next-preserve isPDM x ⟩
                                            nextB (λ α → h (x α)) 
                                            ≡⟨ cong nextB (later-ext (λ α → (eq α)))  ⟩ 
                                            nextB (λ α → foldPL setA setB (dmdata nextB ε _·_) isDMB f (x α)) ∎)
                           (λ {x y} → λ eqx eqy → h (conPL (x ∪ₚ y))
                                                   ≡⟨ refl ⟩
                                                   h ((conPL x) ∪ₚₗ (conPL y))
                                                   ≡⟨ IsPreservingDM.union-preserve isPDM (conPL x) (conPL y) ⟩
                                                   (h (conPL x) · h (conPL y))
                                                   ≡⟨ cong₂ _·_ eqx eqy ⟩
                                                   (foldPL setA setB (dmdata nextB ε _·_) isDMB f (conPL x) ·
                                                   foldPL setA setB (dmdata nextB ε _·_) isDMB f (conPL y)) ∎)
                           x


--***********************************************************************************--
-- Showing that it is impossible to compose Lift and Powerset via a distributive law --
--***********************************************************************************--

--We now try to define a composite monad of the Powerset and Lift monads, formed via a distributive law.
LcP : (A : Set) → (κ : Cl) → Set
LcP A κ = myLift (Powerset A) κ

-- the unit of this candidate monad is simply the composit of the units for Lift (nowL x) and Powerset (unitP)
nowLcP : {A : Set} {κ : Cl} → A → (LcP A κ) 
nowLcP x = nowL (η x)

--LcP is a set.
truncLcP : {A : Set} {κ : Cl} → isSet (LcP A κ)
truncLcP = MyLiftSet.isSetmyLift trunc

--LLcP is a set
truncLLcP : {A : Set} {κ : Cl} → isSet (myLift (LcP A κ) κ)
truncLLcP = MyLiftSet.isSetmyLift truncLcP

-- we define a union on LcP, which will help in defining the distributive law.
_l∪p_ : {A : Set} {κ : Cl} → (LcP A κ) → (LcP A κ) → (LcP A κ)
nowL x l∪p nowL y = nowL (x ∪ₚ y)
nowL x l∪p stepL y = stepL (λ α → (nowL x l∪p (y α)))
stepL x l∪p nowL y = stepL (λ α → ((x α) l∪p nowL y))
stepL x l∪p stepL y = stepL (λ α → ((x α) l∪p (y α)))

--l∪p is associative, commutative, idempotent, and nowL ∅ is a unit for l∪p
assoc-l∪p : {A : Set} {κ : Cl} → ∀(x y z : LcP A κ) → (x l∪p y) l∪p z ≡ x l∪p (y l∪p z)
assoc-l∪p (nowL x) (nowL y) (nowL z) = cong nowL (sym (ass x y z))
assoc-l∪p (nowL x) (nowL y) (stepL z) = cong stepL (later-ext λ α → assoc-l∪p (nowL x) (nowL y) (z α))
assoc-l∪p (nowL x) (stepL y) (nowL z) = cong stepL (later-ext λ α → assoc-l∪p (nowL x) (y α) (nowL z))
assoc-l∪p (nowL x) (stepL y) (stepL z) = cong stepL (later-ext λ α → assoc-l∪p (nowL x) (y α) (z α))
assoc-l∪p (stepL x) (nowL y) (nowL z) = cong stepL (later-ext λ α → assoc-l∪p (x α) (nowL y) (nowL z))
assoc-l∪p (stepL x) (nowL y) (stepL z) = cong stepL (later-ext λ α → assoc-l∪p (x α) (nowL y) (z α))
assoc-l∪p (stepL x) (stepL y) (nowL z) = cong stepL (later-ext λ α → assoc-l∪p (x α) (y α) (nowL z))
assoc-l∪p (stepL x) (stepL y) (stepL z) = cong stepL (later-ext λ α → assoc-l∪p (x α) (y α) (z α))

comm-l∪p : {A : Set} {κ : Cl} → ∀(x y : LcP A κ) → (x l∪p y) ≡ y l∪p x
comm-l∪p (nowL x) (nowL y) = cong nowL (com x y)
comm-l∪p (nowL x) (stepL y) = cong stepL (later-ext λ α → comm-l∪p (nowL x) (y α))
comm-l∪p (stepL x) (nowL y) = cong stepL (later-ext λ α → comm-l∪p (x α) (nowL y))
comm-l∪p (stepL x) (stepL y) = cong stepL (later-ext λ α → comm-l∪p (x α) (y α))

idem-l∪p :  {A : Set} {κ : Cl} → ∀(x : LcP A κ) → x l∪p x ≡ x
idem-l∪p (nowL x) = cong nowL (idem x)
idem-l∪p (stepL x) = cong stepL (later-ext λ α → idem-l∪p (x α))

unit-l∪p : {A : Set} {κ : Cl} → ∀(x : LcP A κ) → x l∪p (nowL ∅) ≡ x
unit-l∪p (nowL x) = cong nowL (unitr x)
unit-l∪p (stepL x) = cong stepL (later-ext λ α → unit-l∪p (x α))

lemma-nowL-l∪p-mapL : {A : Set} {κ : Cl} → ∀(x : LcP A κ) → ∀(M : Powerset A) → nowL M l∪p x ≡ mapL κ (M ∪ₚ_) x
lemma-nowL-l∪p-mapL (nowL x) M = refl
lemma-nowL-l∪p-mapL (stepL x) M = cong stepL (later-ext (λ α → lemma-nowL-l∪p-mapL (x α) M))

--notice the difference with _l∪m_, which we used for multiset:
_l∪p'_ : {A : Set} {κ : Cl} → (LcP A κ) → (LcP A κ) → (LcP A κ)
nowL x l∪p' nowL y = nowL (x ∪ₚ y)
nowL x l∪p' stepL y = stepL (λ α → (nowL x l∪p' (y α)))
stepL x l∪p' y = stepL (λ α → ((x α) l∪p' y))

-- _l∪p'_ is not idempotent:
-- stepL (λ α → nowL x) l∪p' stepL (λ α → nowL x) =
-- stepL (λ α → (nowL x) l∪p' stepL (λ α → nowL x)) =
-- stepL (λ α → stepL (λ β → nowL x l∪p' nowL x)) =
-- stepL (λ α → stepL (λ β → nowL (x ∪ₚ x))) =
-- stepL (λ α → stepL (λ β → nowL x)) ≠ stepL (λ α → nowL x)


--mapL κ f distributes over l∪p if f distributes over ∪ₚ
dist-mapL-l∪p : {A B : Set} {κ : Cl} → ∀(f : (Powerset A) → (Powerset B)) → ∀(fdist : ∀(x y : Powerset A) → f (x ∪ₚ y) ≡ f x ∪ₚ f y)
                                     → ∀(lx ly : (LcP A κ)) → mapL κ f (lx l∪p ly) ≡ (mapL κ f lx) l∪p (mapL κ f ly)
dist-mapL-l∪p f fdist (nowL x) (nowL y) = cong nowL (fdist x y)
dist-mapL-l∪p f fdist (nowL x) (stepL y) = cong stepL (later-ext λ α → dist-mapL-l∪p f fdist (nowL x) (y α))
dist-mapL-l∪p f fdist (stepL x) (nowL y) = cong stepL (later-ext λ α → dist-mapL-l∪p f fdist (x α) (nowL y))
dist-mapL-l∪p f fdist (stepL x) (stepL y) = cong stepL (later-ext λ α → dist-mapL-l∪p f fdist (x α) (y α))

-- and why not, I also need a ll∪p:
_ll∪p_ : {A : Set} {κ : Cl} → (myLift (LcP A κ) κ) → (myLift (LcP A κ) κ) → (myLift (LcP A κ) κ)
nowL x ll∪p nowL y = nowL (x l∪p y)
nowL x ll∪p stepL y = stepL (λ α → (nowL x ll∪p (y α)))
stepL x ll∪p nowL y = stepL (λ α → ((x α) ll∪p (nowL y)))
stepL x ll∪p stepL y = stepL (λ α → ((x α) ll∪p (y α)))

assoc-ll∪p : {A : Set} {κ : Cl} → ∀(x y z : (myLift (LcP A κ) κ)) → (x ll∪p y) ll∪p z ≡ x ll∪p (y ll∪p z)
assoc-ll∪p (nowL x) (nowL y) (nowL z) = cong nowL (assoc-l∪p x y z)
assoc-ll∪p (nowL x) (nowL y) (stepL z) = cong stepL (later-ext λ α → assoc-ll∪p (nowL x) (nowL y) (z α))
assoc-ll∪p (nowL x) (stepL y) (nowL z) = cong stepL (later-ext λ α → assoc-ll∪p (nowL x) (y α) (nowL z))
assoc-ll∪p (nowL x) (stepL y) (stepL z) = cong stepL (later-ext λ α → assoc-ll∪p (nowL x) (y α) (z α))
assoc-ll∪p (stepL x) (nowL y) (nowL z) = cong stepL (later-ext λ α → assoc-ll∪p (x α) (nowL y) (nowL z))
assoc-ll∪p (stepL x) (nowL y) (stepL z) = cong stepL (later-ext λ α → assoc-ll∪p (x α) (nowL y) (z α))
assoc-ll∪p (stepL x) (stepL y) (nowL z) = cong stepL (later-ext λ α → assoc-ll∪p (x α) (y α) (nowL z))
assoc-ll∪p (stepL x) (stepL y) (stepL z) = cong stepL (later-ext λ α → assoc-ll∪p (x α) (y α) (z α))

unit-ll∪p : {A : Set} {κ : Cl} → ∀(x : myLift (LcP A κ) κ) → nowL (nowL ∅) ll∪p x ≡ x
unit-ll∪p (nowL x) = nowL (nowL ∅ l∪p x)
                      ≡⟨ cong nowL (comm-l∪p (nowL ∅) x) ⟩
                      nowL (x l∪p nowL ∅)
                      ≡⟨ cong nowL (unit-l∪p x) ⟩
                      nowL x ∎
unit-ll∪p (stepL x) = cong stepL (later-ext λ α → unit-ll∪p (x α))

lemma-nowL-ll∪p-mapL : {A : Set} {κ : Cl} → ∀(x : myLift (LcP A κ) κ) → ∀(X : LcP A κ) → nowL X ll∪p x ≡ mapL κ (X l∪p_) x
lemma-nowL-ll∪p-mapL (nowL x) X = refl
lemma-nowL-ll∪p-mapL (stepL x) X = cong stepL (later-ext (λ α → lemma-nowL-ll∪p-mapL (x α) X))

-- The following lemma is crucial in the proof of the second multiplication law, but does not hold for powerset:

-- multL-ll∪p-l∪p : {A : Set} (κ : Cl) → ∀(x y : myLift (LcP A κ) κ) → MultL κ (x ll∪p y) ≡ MultL κ x l∪p MultL κ y

-- To see this, consider x = stepL (λ α → nowL (nowL x') and y = nowL (stepL (λ α → nowL y'))
-- Then: MultL κ (x ll∪p y) = MultL κ stepL (λ α → (nowL (nowL x') ll∪p (nowL (stepL (λ β → nowL y')))))
--                          = MultL κ stepL (λ α → nowL (nowL x' l∪p stepL (λ β → nowL y')))
--                          = MultL κ stepL (λ α → nowL (stepL (λ β → nowL x' l∪p nowL y')))
--                          = MultL κ stepL (λ α → nowL (stepL (λ β → nowL (x' ∪ₚ y'))))
--                          = stepL (λ α → stepL (λ β → nowL (x' ∪ₚ y')))
-- whereas: MultL κ x l∪p MultL κ y = stepL (λ α → nowL x') l∪p stepL (λ α → nowL y')
--                                  = stepL (λ α → nowL x' l∪p nowL y')
--                                  = stepL (λ α → nowL (x' ∪ₚ y'))

-- The most straightforward candidate for a distributive law therefore fails the second multiplication axiom.
-- We show that is does still satisfy the other three axioms.
-- Here is the candidate distributive law:
distlawLcP : {A : Set} {κ : Cl} → Powerset (myLift A κ) → (LcP A κ)
distlawLcP ∅ = nowL ∅
distlawLcP (η (nowL x)) = nowL (η x)
distlawLcP (η (stepL x)) = stepL (λ α → distlawLcP (η (x α)))
distlawLcP (x ∪ₚ y) = (distlawLcP x) l∪p (distlawLcP y)
distlawLcP (ass x y z i) = assoc-l∪p (distlawLcP x) (distlawLcP y) (distlawLcP z) (~ i)
distlawLcP (com x y i) = comm-l∪p (distlawLcP x) (distlawLcP y) i
distlawLcP (idem x i) = idem-l∪p (distlawLcP x) i
distlawLcP (unitr x i) = unit-l∪p (distlawLcP x) i
distlawLcP (trunc x y x₁ y₁ i i₁) = truncLcP (distlawLcP x) (distlawLcP y) (λ j → distlawLcP (x₁ j)) (λ j → distlawLcP (y₁ j)) i i₁

--proof that distlawLcP satisfies three out of 4 axioms:
--unit laws:
unitlawLcP1 : {A : Set} {κ : Cl} → ∀(x : myLift A κ) → (distlawLcP (η x)) ≡  mapL κ η x
unitlawLcP1 (nowL x) = refl
unitlawLcP1 (stepL x) = cong stepL (later-ext λ α → unitlawLcP1 (x α))

unitlawLcP2 : {A : Set} {κ : Cl} → ∀(X : Powerset A) → (distlawLcP {A}{κ} (mapP nowL X)) ≡ nowL X
unitlawLcP2 X = elimP
                 (λ Y → ((distlawLcP (mapP nowL Y) ≡ nowL Y) , truncLcP (distlawLcP (mapP nowL Y)) (nowL Y)))
                 refl
                 (λ Y → refl)
                 (λ {X Y} → λ eqX eqY → distlawLcP (mapP nowL X) l∪p distlawLcP (mapP nowL Y)
                                         ≡⟨ cong₂ (_l∪p_) eqX eqY ⟩
                                         ((nowL X) l∪p (nowL Y))
                                         ≡⟨ refl ⟩
                                         nowL (X ∪ₚ Y) ∎ )
                 X


--1st multiplication law:
multlawLcP1 : {A : Set} (κ : Cl) → ∀(X : Powerset (Powerset (myLift A κ))) → distlawLcP (Powerset-mult X) ≡
                                                                             mapL κ Powerset-mult (distlawLcP (mapP distlawLcP X))
multlawLcP1 κ X = elimP
                    (λ Y → ((distlawLcP (Powerset-mult Y) ≡ mapL κ Powerset-mult (distlawLcP (mapP distlawLcP Y))) ,
                     truncLcP (distlawLcP (Powerset-mult Y)) (mapL κ Powerset-mult (distlawLcP (mapP distlawLcP Y))) ))
                    refl
                    (λ Y → distlawLcP Y
                            ≡⟨ sym (mapL-identity (distlawLcP Y)) ⟩
                            mapL κ (λ y → y) (distlawLcP Y)
                            ≡⟨ cong₂ (mapL κ) (funExt (λ y → sym (Powerset-unitlaw1 y))) refl ⟩
                            mapL κ (λ y → Powerset-mult (η y)) (distlawLcP Y)
                            ≡⟨ sym (mapmapL κ η Powerset-mult (distlawLcP Y)) ⟩
                            mapL κ Powerset-mult (mapL κ η (distlawLcP Y)) 
                            ≡⟨ cong (mapL κ Powerset-mult) (sym (unitlawLcP1 (distlawLcP Y)))  ⟩
                            mapL κ Powerset-mult (distlawLcP (η (distlawLcP Y))) ∎)
                    (λ {X Y} → λ eqX eqY → (distlawLcP (Powerset-mult X) l∪p distlawLcP (Powerset-mult Y))
                              ≡⟨ cong₂ _l∪p_ eqX eqY ⟩
                              (mapL κ Powerset-mult (distlawLcP (mapP distlawLcP X)) l∪p mapL κ Powerset-mult (distlawLcP (mapP distlawLcP Y)))
                              ≡⟨ sym (dist-mapL-l∪p Powerset-mult (λ x y → refl) (distlawLcP (mapP distlawLcP X)) (distlawLcP (mapP distlawLcP Y))) ⟩
                              mapL κ Powerset-mult (distlawLcP (mapP distlawLcP X) l∪p distlawLcP (mapP distlawLcP Y)) ∎)
                    X 



-- We now show that no distributive law is possible.
-- Notice that our candidate distirbutive law was defined completely in terms of the union l∪p.

-- This union gave problems in the second multiplication axiom.
-- Is another union possible?

-- first we say what it means for a function of type Powerset (myLift A κ) → (LcP A κ) to be a distributive law:

record IsDistLaw {A B : Set} {κ : Cl} (canddistlaw : {A : Set} {κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) : Set where
  constructor isdistlaw

  field
    unit1 : (x : myLift A κ) → (canddistlaw (η x)) ≡  mapL κ η x
    unit2 : (x : Powerset A) → (canddistlaw {A}{κ} (mapP nowL x)) ≡ nowL x
    mult1 : (X : Powerset (Powerset (myLift A κ))) → canddistlaw (Powerset-mult X) ≡ mapL κ Powerset-mult (canddistlaw (mapP canddistlaw X))
    mult2 : (X : Powerset (myLift (myLift A κ) κ)) → canddistlaw (mapP (MultL κ) X) ≡ MultL κ (mapL κ canddistlaw (canddistlaw X))
    nattrans : (X : Powerset(myLift A κ)) → (f : A → B) → canddistlaw (mapP (mapL κ f) X) ≡ mapL κ (mapP f) (canddistlaw X)

--Then we see that we must have:

forced-empty : {A B : Set} {κ : Cl} → ∀(cdl : {A : Set} {κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{B}{κ} cdl → cdl {A}{κ} ∅ ≡ nowL ∅
forced-empty cdl cdlproof = cdl ∅
                             ≡⟨ refl ⟩
                             cdl (mapP nowL ∅)
                             ≡⟨ IsDistLaw.unit2 cdlproof ∅ ⟩
                             nowL ∅ ∎

forced-unit1 : {A B : Set} {κ : Cl} → ∀(cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{B}{κ} cdl →
                                      ∀(x : myLift A κ) → cdl (η x) ≡ mapL κ η x
forced-unit1 cdl cdlproof x = IsDistLaw.unit1 cdlproof x

-- so in particular:
-- cdl η (nowL x) is forced to be equal to nowL (η x), and
-- cdl η (stepL x) is forded to be equal to stepL (λ α → cdl (η (x α))):

forced-unit1-specific-now : {A B : Set} {κ : Cl} → ∀(cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{B}{κ} cdl →
                                                   ∀(x : A) → cdl {A}{κ} (η (nowL x)) ≡ nowL (η x)
forced-unit1-specific-now cdl cdlproof x = forced-unit1 cdl cdlproof (nowL x)

forced-unit1-specific-step : {A B : Set} {κ : Cl} → ∀(cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{B}{κ} cdl →
                               ∀(x : ▹ κ (myLift A κ)) → cdl (η (stepL x)) ≡ stepL (λ α → cdl (η (x α)))
forced-unit1-specific-step {A}{B}{κ} cdl cdlproof x = cdl (η (stepL x))
                                             ≡⟨ forced-unit1 cdl cdlproof (stepL x) ⟩
                                             mapL κ η (stepL x)
                                             ≡⟨ refl ⟩
                                             stepL (λ α → mapL κ η (x α))
                                             ≡⟨ cong stepL (later-ext (λ α → sym (forced-unit1 cdl cdlproof (x α)))) ⟩
                                             stepL (λ α → cdl (η (x α))) ∎

-- Also, we must have:

forced-unit2 : {A B : Set} {κ : Cl} → ∀(cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{B}{κ} cdl →
                                      ∀(x : Powerset A) → cdl (mapP nowL x) ≡ nowL x
forced-unit2 cdl cdlproof x = IsDistLaw.unit2 cdlproof x

-- so in particular:
-- cdl {nowL x, nowL y} = nowL {x, y}

forced-unit2-specific : {A B : Set} {κ : Cl} → ∀(cdl : {A : Set} {κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{B}{κ} cdl →
                                               ∀(x y : A) → cdl (mapP nowL ((η x) ∪ₚ (η y))) ≡ nowL ((η x) ∪ₚ (η y))
forced-unit2-specific cdl cdlproof x y = forced-unit2 cdl cdlproof ((η x) ∪ₚ (η y)) 

-- This means that for any union operation l∪p we must have: nowL x l∪p nowL y = nowL (x ∪ₚ y)
-- Next we will show that such a union operation must also satisfy: stepL x l∪p stepL y = stepL (λ α → ((x α) l∪p (y α))
-- to prove this, we first introduce a candidate union operation c-l∪p. This is exactly the same union operation as l∪p above:

_c-l∪p_ : {A : Set} {κ : Cl} → (LcP A κ) → (LcP A κ) → (LcP A κ)
nowL x c-l∪p nowL y = nowL (x ∪ₚ y)
nowL x c-l∪p stepL y = stepL (λ α → (nowL x c-l∪p (y α)))
stepL x c-l∪p nowL y = stepL (λ α → ((x α) c-l∪p nowL y))
stepL x c-l∪p stepL y = stepL (λ α → ((x α) c-l∪p (y α)))

-- We use this to prove that:

lemma-lemma-x-is-step-left : {A : Set} {κ : Cl} → ∀(x : A) → ∀(y : ▹ κ (myLift A κ)) → (▹ κ ⊥ → nowL x ≡ stepL y) → ⊥
lemma-lemma-x-is-step-left x y proof = fix (λ dbot → MyLiftSet.encode (nowL x) (stepL y) (proof dbot))

lemma-x-is-step-left : {A : Set} {κ : Cl} → ∀(x : (myLift A κ)) → ∀(y : ▹ κ (myLift A κ)) → (▹ κ ⊥ → x ≡ stepL y) → (Σ[ x' ∈ ▹ κ (myLift A κ) ] (x ≡ stepL x')) 
lemma-x-is-step-left (nowL x) y proof = rec (lemma-lemma-x-is-step-left x y proof)
lemma-x-is-step-left (stepL x) y proof = (x , refl)

lemma-x-is-step-right : {A : Set} {κ : Cl} → ∀(x : (myLift A κ)) → ∀(y : ▹ κ (myLift A κ)) → (Σ[ x' ∈ ▹ κ (myLift A κ) ] (x ≡ stepL x')) → (▹ κ ⊥ → x ≡ stepL y)
lemma-x-is-step-right x y (x' , proof) dbot = x
                                              ≡⟨ proof ⟩
                                              stepL x'
                                              ≡⟨ cong stepL (later-ext (λ α → rec (dbot α))) ⟩
                                              stepL y ∎

forced-step-lemma : {A : Set} {κ : Cl} → ∀(cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{A}{κ} cdl →
                                           ∀(x y : ▹ κ (myLift A κ)) → (▹ κ ⊥ → stepL x ≡ stepL y) →
                                           (▹ κ ⊥ → (cdl (η (stepL x) ∪ₚ η (stepL y))) ≡ stepL (λ α → cdl (η (x α))))
forced-step-lemma {A}{κ} cdl cdlproof x y proof dbot = cdl (η (stepL x) ∪ₚ η (stepL y))
                                                                ≡⟨ cong cdl (cong ((η (stepL x)) ∪ₚ_)
                                                                  (cong η (sym (proof dbot)))) ⟩
                                                                cdl (η (stepL x) ∪ₚ η (stepL x))
                                                                ≡⟨ cong cdl (idem (η (stepL x))) ⟩
                                                                cdl (η (stepL x))
                                                                ≡⟨ forced-unit1-specific-step cdl cdlproof x ⟩
                                                                stepL (λ α → cdl (η (x α))) ∎

forced-step : {A : Set} {κ : Cl} → ∀(cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{A}{κ} cdl →
                                           ∀(x y : ▹ κ (myLift A κ)) → Σ[ x' ∈ ▹ κ (myLift (Powerset A) κ) ] (cdl ((η (stepL x)) ∪ₚ (η (stepL y))) ≡ stepL x') 
forced-step {A}{κ} cdl cdlproof x y = lemma-x-is-step-left (cdl ((η (stepL x)) ∪ₚ (η (stepL y))))
                                                                   (λ α → (cdl (η (x α))))
                                                   (forced-step-lemma cdl cdlproof x y
                                                      (lemma-x-is-step-right (stepL x) y ((x , refl)))) 

-- What I need now is:
-- cdl {stepL (λ α → nowL x) , stepL (λ α → nowL y)} = step (λ α → nowL {x,y})

stepnowxy-lemma1 : {A : Set} {κ : Cl} → ∀(cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{A}{κ} cdl →
                                 ∀(x y a : A) → cdl (mapP (mapL κ (λ b → a))(η (stepL (λ α → nowL x)) ∪ₚ η (stepL (λ α → nowL y)))) ≡
                                              stepL (λ α → nowL (η a))
stepnowxy-lemma1 {A}{κ} cdl cdlproof x y a = cdl (η (stepL (λ α → nowL a)) ∪ₚ η (stepL (λ α → nowL a)))
                                              ≡⟨ cong cdl (idem (η (stepL (λ α → nowL a)))) ⟩
                                              cdl (η (stepL (λ α → nowL a)))
                                              ≡⟨ forced-unit1-specific-step cdl cdlproof ((λ α → nowL a)) ⟩
                                              stepL (λ α → cdl (η (nowL a)))
                                              ≡⟨ cong stepL (later-ext (λ α → forced-unit1-specific-now cdl cdlproof a)) ⟩
                                              stepL (λ α → nowL (η a)) ∎

stepnowxy-lemma2 : {A : Set} {κ : Cl} → ∀(cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{A}{κ} cdl →
                                 ∀(x y a : A) → mapL κ (mapP (λ b → a)) (cdl (η (stepL (λ α → nowL x)) ∪ₚ η (stepL (λ α → nowL y)))) ≡
                                              stepL (λ α → nowL (η a))
stepnowxy-lemma2 {A}{κ} cdl cdlproof x y a = mapL κ (mapP (λ b → a)) (cdl (η (stepL (λ α → nowL x)) ∪ₚ η (stepL (λ α → nowL y))))
                                              ≡⟨ sym (IsDistLaw.nattrans cdlproof ((η (stepL (λ α → nowL x)) ∪ₚ η (stepL (λ α → nowL y)))) (λ b → a)) ⟩
                                              cdl (mapP (mapL κ (λ b → a))(η (stepL (λ α → nowL x)) ∪ₚ η (stepL (λ α → nowL y))))
                                              ≡⟨ stepnowxy-lemma1 cdl cdlproof x y a ⟩
                                              stepL (λ α → nowL (η a)) ∎


-- so after mapL κ mapP λ b → a, we know that cdl {step now x, step now y} becomes step now {a}
-- so what can cdl {step now x, step now y} be?
-- three "obvious" candidates are step now {x}, step now {y}, and step now {x,y}. Because of commutativity of { , }
-- we cannot choose one of the former two options, as chosing between x and y is impossible. It therefore has to be the third option
-- But how do we prove this in Agda?
 
stepnowxy : {A : Set} {κ : Cl} → ∀(cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{A}{κ} cdl →
                                 ∀(x y : A) → cdl {A}{κ} (η (stepL (λ α → nowL x)) ∪ₚ η (stepL (λ α → nowL y))) ≡ stepL (λ α → nowL (η x ∪ₚ η y))
stepnowxy cdl cdlproof x y = {!!}

--We assume this for now, and continue the proof.

-- We now focus on cdl {now x, step y}. What can it be?
-- Since it is an element of LcP, it is either equal to now z, or to step z.
-- We prove that both options lead to a (delayed) contradiction.

-- In the case of cdl {now x, step y} = now z, we show that z = x:

record IsNatTransH {A B : Set} {κ : Cl} (h : {A B : Set} → (A × ▹ κ (myLift B κ)) → A) : Set where
  constructor isnattransh

  field
     nattransh : ((x , y) : (A × ▹ κ (myLift B κ))) → (f : A → B) → f(h {A}{B} (x , y)) ≡ h {B}{B} (f x , y) 

lemma-now-step-is-nowzx : {B : Set} {κ : Cl} → ∀(t : ⊤) → ∀(x : B) → ∀(y : ▹ κ (myLift B κ)) → ∀(h : {A B : Set} → ((A × ▹ κ (myLift B κ)) → A)) →
                                               (IsNatTransH{⊤}{B}{κ} h) → h {B}{B} (x , y) ≡ x
lemma-now-step-is-nowzx t x y h proof = h(x , y)
                                       ≡⟨ refl ⟩
                                       h( ((λ(t : ⊤) → x) t) , y)
                                       ≡⟨ sym (IsNatTransH.nattransh proof ((t , y)) ((λ(t : ⊤) → x))) ⟩
                                       (λ(t : ⊤) → x) (h (t , y))
                                       ≡⟨ refl ⟩
                                       x ∎


now-step-is-now-zx : {A : Set} {κ : Cl} → ∀(cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{A}{κ} cdl →
                                          ∀(x : A) → ∀(y : ▹ κ (myLift A κ)) → ∀(h : {A B : Set} → ((A × ▹ κ (myLift B κ)) → A)) → IsNatTransH{⊤}{A}{κ} h → 
                                          cdl (η (nowL x) ∪ₚ η (stepL y)) ≡ nowL (η (h (x , y))) → h (x , y) ≡ x
now-step-is-now-zx cdl cdlproof x y h proof = {!!}  --if it follows that h is nattrans then done by above lemma, if I can somehow get a t in Top to feed the lemma.


--for the following contradiction, we will assume cdl {now x, step y} = now x

record Assumption {A : Set} {κ : Cl} (cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) : Set where
  constructor assumption

  field
    assumption1 : (x : A) → (y : ▹ κ (myLift A κ)) → ((cdl (η (nowL x) ∪ₚ η (stepL y))) ≡ nowL (η x))
   
--we show that this leads to the contradiction ▹ κ ⊥

contradiction-lemma1 : {A : Set} {κ : Cl} → ∀(cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{A}{κ} cdl →
                                      Assumption {myLift A κ}{κ} cdl → ∀(x y : A) →
                                      cdl (mapP (MultL κ) (η (stepL(λ α → nowL (nowL x))) ∪ₚ η (nowL (stepL(λ α → nowL y))))) ≡
                                      stepL(λ α → nowL (η x ∪ₚ η y))
contradiction-lemma1 cdl cdlproof cdlass x y  = cdl (η (stepL (λ α → nowL x)) ∪ₚ η (stepL (λ α → nowL y)))
                                                 ≡⟨ stepnowxy cdl cdlproof x y ⟩
                                                 stepL (λ α → nowL (η x ∪ₚ η y)) ∎ 
                                      

contradiction-lemma2 : {A : Set} {κ : Cl} → ∀(cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{A}{κ} cdl →
                                      Assumption {myLift A κ}{κ} cdl → ∀(x y : A) →
                                      MultL κ (mapL κ cdl (cdl (η (stepL(λ α → nowL (nowL x))) ∪ₚ η (nowL (stepL(λ α → nowL y)))))) ≡
                                      stepL(λ α → nowL (η y))
contradiction-lemma2 {A}{κ} cdl cdlproof cdlass x y = MultL κ (mapL κ cdl (cdl (η (stepL(λ α → nowL (nowL x))) ∪ₚ η (nowL (stepL(λ α → nowL y))))))
                                                ≡⟨ cong (MultL κ) (cong (mapL κ cdl) (cong cdl (com (η (stepL(λ α → nowL (nowL x)))) (η (nowL (stepL(λ α → nowL y))))))) ⟩
                                                MultL κ (mapL κ cdl (cdl (η (nowL (stepL(λ α → nowL y))) ∪ₚ η (stepL(λ α → nowL (nowL x))))))
                                                ≡⟨ cong (MultL κ) (cong (mapL κ cdl) (Assumption.assumption1 cdlass ((stepL(λ α → nowL y))) λ α → nowL (nowL x))) ⟩ 
                                                MultL κ (mapL κ cdl (nowL (η (stepL(λ α → nowL y)))))
                                                ≡⟨ refl ⟩
                                                MultL κ (nowL (cdl (η (stepL(λ α → nowL y)))))
                                                ≡⟨ refl ⟩
                                                cdl (η (stepL(λ α → nowL y)))
                                                ≡⟨ forced-unit1-specific-step cdl cdlproof (λ α → nowL y) ⟩
                                                stepL (λ α → cdl (η (nowL y)))
                                                ≡⟨ cong stepL (later-ext (λ α → forced-unit1-specific-now cdl cdlproof y)) ⟩
                                                stepL (λ α → nowL (η y)) ∎

contradiction-lemma3 : {A : Set} {κ : Cl} → ∀(cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{A}{κ} cdl →
                                      Assumption {myLift A κ}{κ} cdl → ∀(x y : A) → stepL (λ α → nowL (η y)) ≡ stepL (λ α → nowL (η x ∪ₚ η y))
contradiction-lemma3 {A}{κ} cdl cdlproof cdlass x y = stepL (λ α → nowL (η y))
                                                      ≡⟨ sym (contradiction-lemma2 cdl cdlproof cdlass x y) ⟩
                                                      MultL κ (mapL κ cdl (cdl (η (stepL(λ α → nowL (nowL x))) ∪ₚ η (nowL (stepL(λ α → nowL y))))))
                                                      ≡⟨ sym (IsDistLaw.mult2 cdlproof ((η (stepL(λ α → nowL (nowL x))) ∪ₚ η (nowL (stepL(λ α → nowL y)))))) ⟩
                                                      cdl (mapP (MultL κ) (η (stepL(λ α → nowL (nowL x))) ∪ₚ η (nowL (stepL(λ α → nowL y)))))
                                                      ≡⟨ contradiction-lemma1 cdl cdlproof cdlass x y ⟩
                                                      stepL (λ α → nowL (η x ∪ₚ η y)) ∎

contradiction-lemma41 : {A : Set} {κ : Cl} → ∀(x y : A) → (MyLiftSet.Cover {Powerset A}{κ} (stepL (λ α → nowL (η y))) (stepL (λ α → nowL (η x ∪ₚ η y)))) →
                                           ▹ κ (η y ≡ η x ∪ₚ η y)
contradiction-lemma41 {A}{κ} x y proof α = proof α


contradiction-lemma41' : {A : Set} {κ : Cl} → ∀(x y : A) → (MyLiftSet.Cover {Powerset A}{κ} (stepL (λ α → nowL (η x))) (stepL (λ α → nowL (η y)))) →
                                           ▹ κ (η x ≡ η y)
contradiction-lemma41' {A}{κ} x y proof α = proof α

contradiction-lemma4 : {A : Set} {κ : Cl} → ∀(x y : A) → stepL (λ α → nowL (η y)) ≡ stepL (λ α → nowL (η x ∪ₚ η y)) → ▹ κ (η y ≡ η x ∪ₚ η y)
contradiction-lemma4 x y proof = contradiction-lemma41 x y (MyLiftSet.encode ((stepL (λ α → nowL (η y)))) ((stepL (λ α → nowL (η x ∪ₚ η y)))) proof)

contradiction-lemma4' : {A : Set} {κ : Cl} → ∀(x y : A) → stepL (λ α → nowL (η x)) ≡ stepL (λ α → nowL (η y)) → ▹ κ (η x ≡ η y)
contradiction-lemma4' x y proof = contradiction-lemma41' x y (MyLiftSet.encode ((stepL (λ α → nowL (η x)))) ((stepL (λ α → nowL (η y)))) proof)

contradiction-lemma4b : {A : Set} {κ : Cl} → ∀(cdl : {A : Set}{κ : Cl} →  Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{A}{κ} cdl →
                                      Assumption {myLift A κ}{κ} cdl → ∀(x y : A) → ▸ κ λ α → (η y ≡ η x ∪ₚ η y)
contradiction-lemma4b cdl cdlproof cdlass x y = contradiction-lemma4 x y (contradiction-lemma3 cdl cdlproof cdlass x y) 

contradiction-lemma61 : {A : Set} → ∀(x y : A) → (η y ≡ η x ∪ₚ η y) → (η x) ≤ (η y)
contradiction-lemma61 x y eq = sym eq

contradiction-lemma62 : {A : Set} → (∀(x y : A) → (η y ≡ η x ∪ₚ η y)) → ∀(x y : A) → (η x) ≡ (η y)
contradiction-lemma62 proof x y = antisym≤ (contradiction-lemma61 x y (proof x y)) (contradiction-lemma61 y x (proof y x))

contradiction-lemma63 : {A : Set} → isSet A → ∀(x y : A) → (η x) ≡ (η y) → x ≡ y
contradiction-lemma63 setA x y eq = ηisInjective setA eq

NEWLEMMA : {A : Set}{κ : Cl} → isSet A → Σ[ x' ∈ A ] (Σ[ y' ∈ A ] (x' ≡ y' → ⊥)) → (∀(x y : A) → stepL {Powerset A}{κ} (λ α → (nowL (η x))) ≡ stepL (λ α → (nowL (η y)))) → ▹ κ ⊥
NEWLEMMA setA (x' , y' , botproof) forallproof = λ α → botproof (contradiction-lemma63 setA x' y' (contradiction-lemma4' x' y' (forallproof x' y') α)) 


contradiction-lemma6 : {A : Set} → isSet A → (∀(x y : A) → (η y ≡ η x ∪ₚ η y)) → ∀(x y : A) → x ≡ y
contradiction-lemma6 setA proof x y = contradiction-lemma63 setA x y (contradiction-lemma62 proof x y)

-- To get an actual contradiction I need to assume that A has at least two non-equal elements
contradiction-lemma7 : {A : Set} → isSet A → Σ[ x' ∈ A ] (Σ[ y' ∈ A ] (x' ≡ y' → ⊥)) → (∀(x y : A) → (η y ≡ η x ∪ₚ η y)) → ⊥
contradiction-lemma7 setA (x' , y' , botproof) forallproof = botproof (contradiction-lemma6 setA forallproof x' y')

contradiction1 : {A : Set} {κ : Cl} → isSet A → Σ[ x' ∈ A ] (Σ[ y' ∈ A ] (x' ≡ y' → ⊥)) →
                                      ∀(cdl : {A : Set}{κ : Cl} →  Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{A}{κ} cdl →
                                      Assumption {myLift A κ}{κ} cdl → ▹ κ ⊥
contradiction1 setA (x' , y' , botproof) cdl cdlproof cdlass = λ α → contradiction-lemma7 setA ((x' , y' , botproof))
                                                                 λ x y → {!contradiction-lemma3!} 


-- TEST:

test : {A : Set}{κ : Cl} → (x y : ▹ κ A) → (x ≡ y) → (▸ κ λ α → x α ≡ y α) 
test x y p = λ α → λ i → p i α


-- The only other option for cdl {now x, step y} is to be of form step z

record Assumption2 {A : Set} {κ : Cl} (cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) : Set where
  constructor assumption

  field
    assumption2 : (x : A) → (y : ▹ κ (myLift A κ)) → Σ[ z ∈ ▹ κ (myLift (Powerset A) κ) ] ((cdl (η (nowL x) ∪ₚ η (stepL y))) ≡ stepL z)




lemma-z-is-now : {A : Set}{κ : Cl} → ∀(z : (myLift (myLift A κ) κ)) → ∀(a : A) → (MultL κ (stepL (λ α → z)) ≡ stepL (λ α → nowL a)) → z ≡ (nowL (nowL a))
lemma-z-is-now (nowL z) a proof = {!!}
lemma-z-is-now (stepL x) a proof = {!!}








-- forced-step-lemma-lemma : {A : Set} {κ : Cl} → ∀(cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{A}{κ} cdl →
--                                            ∀(x y : ▹ κ (myLift A κ)) → ∀(a : A) → (▹ κ ⊥ → stepL x ≡ stepL y) →
--                                            (▹ κ ⊥ → (cdl (mapP (mapL κ (λ b → a)) (η (stepL x) ∪ₚ η (stepL y))) ≡
--                                                      stepL (λ α → cdl (η (mapL κ (λ b → a) (x α))))))
-- forced-step-lemma-lemma {A}{κ} cdl cdlproof x y a proof dbot = cdl (mapP (mapL κ (λ b → a)) (η (stepL x) ∪ₚ η (stepL y)))
--                                                                 ≡⟨ cong cdl refl ⟩
--                                                                 cdl ((mapP (mapL κ (λ b → a)) (η (stepL x))) ∪ₚ (mapP (mapL κ (λ b → a)) (η (stepL y))))
--                                                                 ≡⟨ cong cdl (cong (mapP (mapL κ (λ b → a)) (η (stepL x)) ∪ₚ_)
--                                                                   (cong (mapP (mapL κ (λ b → a))) (cong η (sym (proof dbot))))) ⟩
--                                                                 cdl ((mapP (mapL κ (λ b → a)) (η (stepL x))) ∪ₚ (mapP (mapL κ (λ b → a)) (η (stepL x))))
--                                                                 ≡⟨ cong cdl (idem ((mapP (mapL κ (λ b → a)) (η (stepL x))))) ⟩
--                                                                 cdl (mapP (mapL κ (λ b → a)) (η (stepL x)))
--                                                                 ≡⟨ cong cdl refl ⟩
--                                                                 cdl (η ((mapL κ (λ b → a) (stepL x))))
--                                                                 ≡⟨ cong cdl refl ⟩
--                                                                 cdl (η (stepL (λ α → (mapL κ (λ b → a) (x α)))))
--                                                                 ≡⟨ forced-unit1-specific-step cdl cdlproof ((λ α → (mapL κ (λ b → a) (x α)))) ⟩
--                                                                 stepL (λ α → cdl (η (mapL κ (λ b → a) (x α)))) ∎

-- forced-step-lemma : {A : Set} {κ : Cl} → ∀(cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{A}{κ} cdl →
--                                            ∀(x y : ▹ κ (myLift A κ)) → ∀(a : A) → 
--                                            Σ[ x' ∈ ▹ κ (myLift (Powerset A) κ) ] (cdl (mapP (mapL κ (λ b → a)) ((η (stepL x)) ∪ₚ (η (stepL y)))) ≡ stepL x') 
-- forced-step-lemma {A}{κ} cdl cdlproof x y a = lemma-x-is-step-left (cdl (mapP (mapL κ (λ b → a)) ((η (stepL x)) ∪ₚ (η (stepL y)))))
--                                                                    (λ α → (cdl (η (mapL κ (λ b → a) (x α)))))
--                                                    (forced-step-lemma-lemma cdl cdlproof x y a
--                                                       (lemma-x-is-step-right (stepL x) y ((x , refl)))) 

-- forced-step-lemma-nattrans : {A : Set} {κ : Cl} → ∀(cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{A}{κ} cdl →
--                                            ∀(x y : ▹ κ (myLift A κ)) → ∀(a : A) → 
--                                            Σ[ x' ∈ ▹ κ (myLift (Powerset A) κ) ] ((mapL κ (mapP (λ b → a)) (cdl ((η (stepL x)) ∪ₚ (η (stepL y))))) ≡ stepL x')
-- forced-step-lemma-nattrans {A} {κ} cdl cdlproof x y a = lemma-x-is-step-left ((mapL κ (mapP (λ b → a)) (cdl ((η (stepL x)) ∪ₚ (η (stepL y))))))
--                                                                              ((λ α → (cdl (η (mapL κ (λ b → a) (x α))))))
--                                                              {!!}

-- forced-step : {A B : Set} {κ : Cl} → ∀(cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{B}{κ} cdl →
--                                       ∀(x y : ▹ κ (myLift A κ)) → cdl ((η (stepL x)) ∪ₚ (η (stepL y))) ≡ (cdl (η (stepL x))) c-l∪p (cdl (η (stepL y)))
-- forced-step cdl cdlproof x y = {!!}





-- -- -- forced-union : 

-- -- -- We already know that cdl {now x, now y} = now {x, y}
-- -- -- and that cdl {step x, step y} = step (λ α → cdl {x α, y α})
-- -- -- So what about cdl {now x, step y}?
-- -- -- since it is an element of LcP, it is either equal to now z, or to step z.
-- -- -- We prove that both options lead to a contradiction.

-- -- -- In the case of cdl {now x, step y} = now z, we show that z = x:

-- -- --NOTE TO SELF: maybe try making module where assumption cld now step = now holds. Then prove IF that holds, then ....

-- -- xisz : {A B : Set} {κ : Cl} →  ∀(cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{B}{κ} cdl →
-- --                                       ∀(x : A) → ∀(y : ▹ κ (myLift A κ)) → ∀(z : Powerset A)  → cdl ((η (nowL x)) ∪ₚ (η (stepL y))) ≡ nowL z → (η x) ≡ z
-- -- xisz cdl cdlproof x y z eq = {!!}

-- -- --counterEq1 : {A B : Set} {κ : Cl} → ∀(cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{B}{κ} cdl → ∀(x y : A) → 
-- -- --                                            cdl (mapP (MultL κ) (η (nowL (stepL (λ α → nowL x))) ∪ₚ (η (stepL (λ α → (nowL (nowL y)))))))
-- -- --                                            ≡ stepL (λ α → nowL ((η x) ∪ₚ (η y)))
-- -- --counterEq1 cdl cdlproof x y = cdl (η (stepL (λ α → nowL x)) ∪ₚ η (stepL (λ β → nowL y)))
-- -- --                               ≡⟨ forced-step cdl cdlproof ((stepL (λ α → nowL x))) ((stepL (λ α → nowL y))) x refl ⟩
-- -- --                               (cdl (η (stepL (λ α → nowL x))) c-l∪p cdl (η (stepL (λ α → nowL y))))
-- -- --                               ≡⟨ cong₂ _c-l∪p_ (IsDistLaw.unit1 cdlproof (stepL (λ α → nowL x))) (IsDistLaw.unit1 cdlproof (stepL (λ α → nowL y))) ⟩
-- -- --                               (stepL (λ α → nowL (η x)) c-l∪p stepL (λ α → nowL (η y)))
-- -- --                               ≡⟨ refl ⟩ 
-- -- --                               stepL (λ α → nowL (η x ∪ₚ η y)) ∎

-- -- --counterEq2 : {A B : Set} {κ : Cl} → ∀(cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{B}{κ} cdl → ∀(x y : A) → 
-- -- --                                            cdl ((η (nowL (stepL (λ α → nowL x)))) ∪ₚ (η (stepL (λ α → (nowL (nowL y)))))) ≡ nowL (η (stepL (λ ))) →
-- -- --                                            MultL κ (mapL κ cdl (cdl (η (nowL (stepL (λ α → nowL x))) ∪ₚ (η (stepL (λ α → (nowL (nowL y))))))))
-- -- --                                            ≡ stepL (λ α → nowL (η y))
-- -- --counterEq2 {A}{B}{κ} cdl cdlproof x y eq = MultL κ (mapL κ cdl (cdl (η (nowL (stepL (λ α → nowL x))) ∪ₚ η (stepL (λ α → nowL (nowL y))))))
-- -- --                                         ≡⟨ cong (MultL κ) (cong (mapL κ cdl) {!xisz !}) ⟩
-- -- --                                         MultL κ (mapL κ cdl (nowL (η (stepL (λ α → nowL x)))))
-- -- --                                         ≡⟨ {!!} ⟩
-- -- --                                         stepL (λ α → nowL (η y)) ∎                                            


-- -- -- canddistlaw (mapP (MultL κ) X) ≡ MultL κ (mapL κ canddistlaw (canddistlaw X))

-- -- not-nowLx : {A B : Set} {κ : Cl} →  ∀(cdl : {A : Set}{κ : Cl} → Powerset (myLift A κ) → (LcP A κ)) → IsDistLaw {A}{B}{κ} cdl →
-- --                                       ∀(x : A) → ∀(y : ▹ κ (myLift A κ)) → cdl ((η (nowL x)) ∪ₚ (η (stepL y))) ≡ nowL (η x) → ⊥
-- -- not-nowLx cdl cdlproof x y eq

