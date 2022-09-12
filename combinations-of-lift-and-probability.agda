{-# OPTIONS --cubical --guarded --rewriting -W ignore #-}
module combinations-of-lift-and-probability where

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
open import Cubical.HITs.Rationals.QuoQ
open import Agda.Builtin.Unit

--The following code is from Niccolo Veltri and Rasmus Møgelberg
--source: https://github.com/rmogelberg/FinProbHITGR/blob/main/DistHIT.agda
--It defines the probability functor as a HIT, and proves it clock-irrelevant.
open import DistHIT 

--***********************************************************************--
--***********************************************************************--
-- Combining the monads Lift and Finite Probability Distributions freely --
--***********************************************************************--
--***********************************************************************--

-- In this document I want to define a monad, called ProbLift, that is the free combination of the Lift monad and the finite probability distributions monad.
-- In order to do so, I will first define the the Probability monad, and check that it is indeed a monad (Step 1).
-- Then I define the ProbLift monad, check that it is a monad (Step 2), and finally check that it is the free monad on the algebra
-- structures of a delay algebra and a barycentric algebra (Step 3).
-- The Lift monad has aleady been defined in my earlier work, combinations-of-lift-and-list.
-- The Probability functor has already been defined in the file DistHIT by Niccolo Veltri and Rasmus Møgelberg. 


--*******************************--
-- Step 1: The Probability monad --
--*******************************--

--We extend the Probability functor to a monad by defining a multiplication:

Dfin-mult : {A : Set} → Dfin (Dfin A) → Dfin A
Dfin-mult (η x) = x
Dfin-mult (choose x y q) = choose (Dfin-mult x) (Dfin-mult y) q
Dfin-mult (comm x y q i) = comm (Dfin-mult x) (Dfin-mult y) q i
Dfin-mult (idem x q i) = idem (Dfin-mult x) q i
Dfin-mult (Dfin.assoc x y z p q r eq i) = Dfin.assoc (Dfin-mult x) (Dfin-mult y) (Dfin-mult z) p q r eq i
Dfin-mult (trunc x x₁ y y₁ i i₁) = trunc (Dfin-mult x) (Dfin-mult x₁) (λ j → Dfin-mult (y j)) (λ j → Dfin-mult (y₁ j)) i i₁

-- Proving that Dfin forms a monad

-- Dfin-mult (η d) = d
Dfin-unitlaw1 : {A : Set} → ∀(d : Dfin A) → Dfin-mult (η d) ≡ d
Dfin-unitlaw1 d = refl

-- Dfin-mult (map unitM M) = M
Dfin-unitlaw2 : {A : Set} → ∀(d : Dfin A) → Dfin-mult (mapDfin η d) ≡ d
Dfin-unitlaw2 = elimDfinProp (λ _ → trunc _ _)
                             (λ _ → refl)
                             (λ eq1 eq2 q i → choose (eq1 i) (eq2 i) q )
                               

-- Dfin-mult (Dfin-mult D) = Dfin-mult (mapDfin Dfin-mult D) 
Dfin-multlaw :  {A : Set} → ∀(D : Dfin (Dfin (Dfin A))) →  Dfin-mult (Dfin-mult D) ≡ Dfin-mult (mapDfin Dfin-mult D)
Dfin-multlaw = elimDfinProp (λ _ → trunc _ _)
                            (λ _ → refl)
                            (λ eq1 eq2 q i → choose (eq1 i) (eq2 i) q ) 

-- the unit is a natural transformation:
nattrans-DfinUnit : {A B : Set} → ∀(f : A → B) → ∀(d : A) → mapDfin f (η d) ≡ η (f d)
nattrans-DfinUnit f d = refl

-- the multiplication is a natural transformation:
nattrans-DfinMult : {A B : Set} → ∀(f : A → B) → ∀(D : Dfin (Dfin A)) → mapDfin f (Dfin-mult D) ≡ Dfin-mult (mapDfin (mapDfin f) D)
nattrans-DfinMult f = elimDfinProp (λ _ → trunc _ _)
                                   (λ _ → refl)
                                   (λ eq1 eq2 q i → choose (eq1 i) (eq2 i) q ) 

--****************************--
-- Step 2: The ProbLift monad --
--****************************--

--Now that we have a probability monad and a lift monad, I want to show that the following combination of the two is again a monad:
--ProbLift : (A : Set) → (κ : Cl) → Set
--ProbLift A κ = Dfin (A ⊎ (▹ κ (ProbLift A κ)))

data ProbLift (A : Set) (κ : Cl) : Set where
  conDL : Dfin (A ⊎ (▹ κ (ProbLift A κ))) -> ProbLift A κ

-- Elimination principle for ProbLift

-- module to make the inputs more readable
-- no name for the module to make the use of it more readable
module _ {ℓ}{A : Set}{κ : Cl}
         (P : ProbLift A κ → hProp ℓ)
         (Pη1 : ∀ x → fst (P (conDL (η (inl x)))))
         (Pη2 : ∀ {x} → (∀ α → fst (P (x α))) → fst (P (conDL (η (inr x)))))
         (Pchoose : ∀ {x y} → fst(P (conDL x)) → fst(P (conDL y)) → ∀(q : ℚ) → fst(P (conDL (choose x y q))))
         where

  elimDL : ∀ M → fst(P M)
  elimDL (conDL (η (inl x))) = Pη1 x
  elimDL (conDL (η (inr x))) = Pη2 λ α → elimDL (x α)
  elimDL (conDL (choose x y q)) = Pchoose (elimDL (conDL x)) (elimDL (conDL y)) q
  elimDL (conDL (comm x y q i)) = isProp→PathP (λ j → snd (P (conDL (comm x y q j)))) (Pchoose (elimDL (conDL x)) (elimDL (conDL y)) q)
                                                                                      (Pchoose (elimDL (conDL y)) (elimDL (conDL x)) (1 - q)) i
  elimDL (conDL (idem x q i)) = isProp→PathP (λ j → snd (P (conDL (idem x q j)))) (Pchoose (elimDL (conDL x)) (elimDL (conDL x)) q) (elimDL (conDL x)) i
  elimDL (conDL (Dfin.assoc x y z p q r eq i)) = isProp→PathP (λ j → snd (P (conDL (Dfin.assoc x y z p q r eq j))))
                                                   (Pchoose (Pchoose (elimDL (conDL x)) (elimDL (conDL y)) p) (elimDL (conDL z)) q)
                                                   (Pchoose (elimDL (conDL x)) (Pchoose (elimDL (conDL y)) (elimDL (conDL z)) r) (p · q)) i
  elimDL (conDL (trunc X Y x y i j)) = isOfHLevel→isOfHLevelDep 2 (λ z → isProp→isSet (snd (P (conDL z)))) (elimDL (conDL X)) (elimDL (conDL Y))
                                         (cong elimDL (cong conDL x)) (cong elimDL (cong conDL y)) (trunc X Y x y) i j

--***proof that ProbLift is a set***--
-- strategy: build isomorphism, then make equivalence, then use univalence to turn equivalence into equality, then transport.

isoDL :  {A : Set}{κ : Cl} → Iso (Dfin (A ⊎ (▹ κ (ProbLift A κ)))) (ProbLift A κ)  
Iso.fun isoDL = conDL
Iso.inv isoDL (conDL x) = x
Iso.rightInv isoDL (conDL x) = refl
Iso.leftInv isoDL a = refl

equivDL :  {A : Set}{κ : Cl} → (Dfin (A ⊎ (▹ κ (ProbLift A κ)))) ≃ (ProbLift A κ)
equivDL = isoToEquiv isoDL

equalDL : {A : Set}{κ : Cl} → (Dfin (A ⊎ (▹ κ (ProbLift A κ)))) ≡ (ProbLift A κ)
equalDL = ua equivDL

truncDL : {A : Set} {κ : Cl} → isSet (ProbLift A κ)
truncDL = subst⁻ isSet (sym equalDL) trunc


--***algebraic structure for ProbLift***--

--nowDL and stepDL turn ProbLift into a delay algebra structure:
nowDL : {A : Set} {κ : Cl} → A → (ProbLift A κ)
nowDL a = conDL (η (inl a))

stepDL : {A : Set} {κ : Cl} → ▹ κ (ProbLift A κ) → (ProbLift A κ)
stepDL a = conDL (η (inr a))

--choose is derived from Dfin choose, and turns ProbLift into a barycentric algebra:
chooseDL : {A : Set} {κ : Cl} → (ProbLift A κ) → (ProbLift A κ) → ℚ → (ProbLift A κ)
chooseDL {A} {κ} (conDL x) (conDL y) q = conDL (choose x y q)

-- --proof that this choose function does indeed provide a barycentric algebra structure: 
commDL : {A : Set} {κ : Cl} → ∀(xl yl : (ProbLift A κ)) → ∀(q : ℚ) → chooseDL xl yl q ≡ chooseDL yl xl (1 - q)
commDL {A} {κ} (conDL x) (conDL y) q = cong conDL (comm x y q)

idemDL : {A : Set} {κ : Cl} → ∀ (xl : (ProbLift A κ)) → ∀(q : ℚ) → chooseDL xl xl q ≡ xl
idemDL {A} {κ} (conDL x) q = cong conDL (idem x q)

assocDL : {A : Set} {κ : Cl} → ∀(xl yl zl : (ProbLift A κ)) → ∀(p q r : ℚ) → ∀(eq : r · (1 - (p · q)) ≡ q · (1 - p)) →
                                              chooseDL (chooseDL xl yl p) zl q ≡ chooseDL xl (chooseDL yl zl r) (p · q)
assocDL {A} {κ} (conDL x) (conDL y) (conDL z) p q r eq = cong conDL (Dfin.assoc x y z p q r eq)

--***monadic structure for ProbLift***--

--a map function to turn ProbLift into a functor
mapDL : {A B : Set} {κ : Cl} → (f : A → B) → (ProbLift A κ) → (ProbLift B κ)
mapDL f (conDL (η (inl x))) = conDL (η (inl (f x)))
mapDL f (conDL (η (inr x))) = stepDL (λ α → mapDL f (x α))
mapDL f (conDL (choose x y q)) = chooseDL (mapDL f (conDL x)) (mapDL f (conDL y)) q 
mapDL f (conDL (comm x y q i)) = commDL (mapDL f (conDL x)) (mapDL f (conDL y)) q i
mapDL f (conDL (idem x q i)) = idemDL (mapDL f (conDL x)) q i
mapDL f (conDL (Dfin.assoc x y z p q r eq i)) = assocDL (mapDL f (conDL x)) (mapDL f (conDL y)) (mapDL f (conDL z)) p q r eq i
mapDL f (conDL (trunc x y z w i i₁)) = truncDL (mapDL f (conDL x)) (mapDL f (conDL y)) (\ j → mapDL f (conDL (z j))) (\ j → mapDL f (conDL (w j))) i i₁

--a bind operator to make ProbLift into a monad
bindDL : {A B : Set} {κ : Cl} → (A → (ProbLift B κ)) → ProbLift A κ → ProbLift B κ
bindDL f (conDL (η (inl x))) = f x
bindDL f (conDL (η (inr x))) = stepDL (\ α → bindDL f (x α))
bindDL f (conDL (choose x y q)) = chooseDL (bindDL f (conDL x)) (bindDL f (conDL y)) q
bindDL f (conDL (comm x y q i)) = commDL (bindDL f (conDL x)) (bindDL f (conDL y)) q i
bindDL f (conDL (idem x q i)) = idemDL (bindDL f (conDL x)) q i
bindDL f (conDL (Dfin.assoc x y z p q r eq i)) = assocDL (bindDL f (conDL x)) (bindDL f (conDL y)) (bindDL f (conDL z)) p q r eq i
bindDL f (conDL (trunc x y z w i i₁)) = truncDL (bindDL f (conDL x)) (bindDL f (conDL y)) (\ j → bindDL f (conDL (z j))) (\ j → bindDL f (conDL (w j))) i i₁

--bindDL commutes with ∪ₚₗ
bindDL-choose : {A B : Set} {κ : Cl} → ∀(f : A → (ProbLift B κ)) → ∀(xl yl : (ProbLift A κ)) → ∀(q : ℚ) → bindDL f (chooseDL xl yl q) ≡ chooseDL (bindDL f xl) (bindDL f yl) q
bindDL-choose f (conDL x) (conDL y) q = refl

-- --***proof that ProbLift is a monad***--

--bindDL and nowDL need to be natural transformations
nattrans-nowDL : {A B : Set} {κ : Cl} → ∀(f : A → B) → ∀(x : A) → mapDL {A}{B}{κ} f (nowDL x) ≡ nowDL (f x)
nattrans-nowDL f x = refl

-- -- TODO: bindDL

-- bindDL and nowDL also need to satisfy three monad laws:
-- unit is a left-identity for bind
unitlawDL1 : {A B : Set} {κ : Cl} → ∀ (f : A → (ProbLift B κ)) → ∀ (x : A) → (bindDL f (nowDL x)) ≡ f x
unitlawDL1 f x = refl

-- unit is a right-identity for bind
unitlawDL2 : {A : Set}{κ : Cl} → ∀(x : (ProbLift A κ)) → (bindDL nowDL x) ≡ x
unitlawDL2 x = elimDL ((λ y → ((bindDL nowDL y) ≡ y) , truncDL (bindDL nowDL y) y))
                      (λ x → refl)
                      (λ p → cong conDL (cong η (cong inr (later-ext (λ β → p β)))))
                      (λ {x y} → λ eq1 eq2 → λ q → cong₂ (λ x y → chooseDL x y q) eq1 eq2 )
                      x 

-- bind is associative
assoclawDL : {A B C : Set}{κ : Cl} → ∀(f : A → (ProbLift B κ)) → ∀ (g : B → (ProbLift C κ)) → ∀ (x : (ProbLift A κ))
                                   → (bindDL (\ y → (bindDL g (f y))) x) ≡ (bindDL g (bindDL f x))
assoclawDL f g x = elimDL ((λ z → ((bindDL (\ y → (bindDL g (f y))) z) ≡ (bindDL g (bindDL f z)))
                                   , truncDL ((bindDL (\ y → (bindDL g (f y))) z)) (bindDL g (bindDL f z))))
                          (λ y → refl) 
                          (λ p → cong conDL (cong η (cong inr (later-ext (λ α → p α)))))
                          (λ {x y} → λ eq1 eq2 → λ q → chooseDL (bindDL (λ y₁ → bindDL g (f y₁)) (conDL x))
                                                                 (bindDL (λ y₁ → bindDL g (f y₁)) (conDL y)) q
                                                        ≡⟨ cong₂ (λ x y → chooseDL x y q) eq1 eq2 ⟩
                                                        chooseDL (bindDL g (bindDL f (conDL x))) (bindDL g (bindDL f (conDL y))) q
                                                        ≡⟨ sym (bindDL-choose g (bindDL f (conDL x)) (bindDL f (conDL y)) q) ⟩
                                                        bindDL g (chooseDL (bindDL f (conDL x)) (bindDL f (conDL y)) q) ∎ )
                          x 


--************************************************************************************--
-- Step 3: The ProbLift monad as the free delay-algebra and barycentric algebra monad --
--************************************************************************************--

-- We already know that (ProbLift, stepPL) forms a delay algebra structure,
-- and (Problift, chooseDL) forms a Barycentric algebra.
-- What we need to show is that ProbLift is the free monad with these properties.
-- That is, for a set A, and any other structure (B, δ, chooseB) where (B, δ) is a delay algebra and (B, chooseB) a barycentric algebra,
-- given a function f : A → B, there is a unique function ProbLift A → B extending f that preserves the algebra structures.

record IsBCA {A : Set} (chooseA : A → A → ℚ → A) : Set where
  constructor isbca

  field
    commu : (x y : A) → (q : ℚ) → chooseA x y q ≡ chooseA y x (1 - q)
    idemp : (x : A) → (q : ℚ) → chooseA x x q ≡ x
    asso : (x y z : A) → (p q r : ℚ) → (eq : r · (1 - (p · q)) ≡ q · (1 - p)) → chooseA (chooseA x y p) z q ≡ chooseA x (chooseA y z r) (p · q)
    
record DelayBCAData (A : Set) (κ : Cl) : Set where
  constructor dbca-data
  field
    nextA : ▹ κ A → A
    chooseA : A → A → ℚ → A

record IsDelayBCA {A : Set}{κ : Cl} (dbca : DelayBCAData A κ) : Set where
  constructor isdelaybca

  open DelayBCAData dbca
  field
    isBCA : IsBCA chooseA
    isDelayalg : IsDelayalg κ nextA

  open IsBCA isBCA public
  open IsDelayalg isDelayalg public

record IsPreservingDL {A B : Set}{κ : Cl} dbcaA dbcaB (g : A → B) : Set where
  constructor ispreservingDL

  open DelayBCAData dbcaA
  open DelayBCAData dbcaB renaming (nextA to nextB; chooseA to chooseB)
  field
    next-preserve : (x : ▹ κ A) → g (nextA x) ≡ nextB (\ α → g (x α))
    choose-preserve : (x y : A) → (q : ℚ) → g (chooseA x y q) ≡ chooseB (g x) (g y) q

record IsExtendingDL {A B : Set}{κ : Cl} (f : A → B) (h : (ProbLift A κ) → B) : Set where
  constructor isextendingDL

  field
    extends : (x : A) → h (nowDL x) ≡ (f x)

--foldDL defines the function we are after
foldDL : {A B : Set}{κ : Cl} → isSet A → isSet B → ∀ dbca → IsDelayBCA {B} dbca → (A → B) → (ProbLift A κ) → B
foldDL setA setB dbca@(dbca-data nextB chooseB) isDBCA f (conDL (η (inl x))) = f x
foldDL setA setB dbca@(dbca-data nextB chooseB) isDBCA f (conDL (η (inr x))) = nextB (λ α → foldDL setA setB dbca isDBCA f (x α))
foldDL setA setB dbca@(dbca-data nextB chooseB) isDBCA f (conDL (choose x y q)) = chooseB (foldDL setA setB dbca isDBCA f (conDL x)) (foldDL setA setB dbca isDBCA f (conDL y)) q
foldDL setA setB dbca@(dbca-data nextB chooseB) isDBCA f (conDL (comm x y q i)) = IsDelayBCA.commu isDBCA (foldDL setA setB dbca isDBCA f (conDL x))
                                                                                                          (foldDL setA setB dbca isDBCA f (conDL y)) q i
foldDL setA setB dbca@(dbca-data nextB chooseB) isDBCA f (conDL (idem x q i)) = IsDelayBCA.idemp isDBCA (foldDL setA setB dbca isDBCA f (conDL x)) q i
foldDL setA setB dbca@(dbca-data nextB chooseB) isDBCA f (conDL (Dfin.assoc x y z q p r eq i)) = IsDelayBCA.asso isDBCA (foldDL setA setB dbca isDBCA f (conDL x))
                                                                                                     (foldDL setA setB dbca isDBCA f (conDL y))
                                                                                                     (foldDL setA setB dbca isDBCA f (conDL z)) q p r eq i
foldDL setA setB dbca@(dbca-data nextB chooseB) isDBCA f (conDL (trunc x y x₁ y₁ i i₁)) = setB (foldDL setA setB dbca isDBCA f (conDL x))
                                                                                          (foldDL setA setB dbca isDBCA f (conDL y))
                                                                                          (λ j → (foldDL setA setB dbca isDBCA f (conDL (x₁ j))))
                                                                                          (λ j → (foldDL setA setB dbca isDBCA f (conDL (y₁ j))))
                                                                                          i i₁

--foldDL extends the function f : A → B
foldDL-extends : {A B : Set}{κ : Cl} → ∀(setA : isSet A) → ∀(setB : isSet B) → ∀ dbca → ∀(isDBCA : IsDelayBCA {B}{κ} dbca) →
                   ∀ (f : A → B) → IsExtendingDL f (foldDL setA setB dbca isDBCA f)
IsExtendingDL.extends (foldDL-extends setA setB dbca isDBCA f) x = refl

--foldDL preseves the DelayMonoid structure
 
module _ {A B : Set}{κ : Cl} (setA : isSet A) (setB : isSet B) (dbca : _) (isDBCA : IsDelayBCA {B} {κ} dbca)
         (f : A → B)
 where
  open IsPreservingDL
  open DelayBCAData dbca renaming (nextA to nextB; chooseA to chooseB )

  foldDL-preserves : IsPreservingDL {ProbLift A κ}{B}{κ} (dbca-data (stepDL) chooseDL) dbca (foldDL setA setB dbca isDBCA f)
  next-preserve foldDL-preserves x = cong nextB (later-ext (λ α → refl))
  choose-preserve foldDL-preserves (conDL x) (conDL y) q = refl

--and foldDL is unique in doing so.
--That is, for any function h that both preserves the algebra structure
--and extends the function f : A → B,
-- h is equivalent to fold.

module _ {A B : Set} {κ : Cl} (h : ProbLift A κ → B)
                       (setA : isSet A) (setB : isSet B) (dbca : _) (isDBCA : IsDelayBCA {B}{κ} dbca)
                       (f : A → B) (isPDL : IsPreservingDL {ProbLift A κ}{B}{κ} (dbca-data (stepDL) chooseDL) dbca h)
                       (isExt : IsExtendingDL f h) where

  open DelayBCAData dbca renaming (nextA to nextB; chooseA to chooseB)

  fold-uniquenessDL : (x : (ProbLift A κ)) → h x ≡ (foldDL setA setB dbca isDBCA f x)
  fold-uniquenessDL x = elimDL ((λ x → (h x ≡ (foldDL setA setB dbca isDBCA f x)) , setB (h x) ((foldDL setA setB dbca isDBCA f x))))
                               (λ a → h (conDL (η (inl a)))
                                       ≡⟨ refl ⟩
                                       h (nowDL a)
                                       ≡⟨ IsExtendingDL.extends isExt a ⟩
                                       f a ∎)
                               (λ {x} → λ eq → h (conDL (η (inr x)))
                                               ≡⟨ refl ⟩
                                               h (stepDL x)
                                               ≡⟨ IsPreservingDL.next-preserve isPDL x ⟩
                                               nextB (λ α → h (x α)) 
                                               ≡⟨ cong nextB (later-ext (λ α → (eq α)))  ⟩ 
                                               nextB (λ α → foldDL setA setB (dbca-data nextB chooseB) isDBCA f (x α)) ∎)
                               (λ {x y} → λ eqx eqy → λ q →  h (conDL (choose x y q))
                                                              ≡⟨ refl ⟩
                                                              h (chooseDL (conDL x) (conDL y) q)
                                                              ≡⟨ IsPreservingDL.choose-preserve isPDL (conDL x) (conDL y) q ⟩
                                                              (chooseB (h (conDL x)) (h (conDL y)) q)
                                                              ≡⟨ cong₂ (λ x y → chooseB x y q) eqx eqy ⟩
                                                              chooseB (foldDL setA setB (dbca-data nextB chooseB) isDBCA f (conDL x))
                                                                      (foldDL setA setB (dbca-data nextB chooseB) isDBCA f (conDL y)) q ∎)
                               x
