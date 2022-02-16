{-# OPTIONS --cubical --guarded -W ignore #-}
module combinations-of-lift-and-multiset where

open import Clocked.Primitives
open import Cubical.Foundations.Everything
open import Cubical.Data.List as List
open import Cubical.Data.List.Properties
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import combinations-of-lift-and-list

--**************************************************************************--
--**************************************************************************--
-- Combining the monads Lift and Multiset freely and via a distributive law --
--**************************************************************************--
--**************************************************************************--

-- In this document I want to define a monad, called MultiLift, that is the free combination of the Lift monad and the Multiset monad.
-- In order to do so, I will first define the the Multiset monad, and check that it is indeed a monad (Step 1).
-- Then I define the LiftMulti monad, check that it is a monad (Step 2), and finally check that it is the free monad on the algebra
-- structures of a delay algebra and a monoid (Step 3).
-- The Lift monad has aleady been defined in my earlier work, combinations-of-lift-and-list.
-- In the same file I check that lift is indeed a monad, and define various usefull functions, such as a map function for Lift.

-- In addition to the free combination of the Multiset and the Lift monads, I also compose the two monads to form the monad
-- LcM : A → Lift(Multiset A). This composition uses a distributive law, which I prove does indeed satisfy all the axioms for a
-- distributive law.


--****************************--
-- Step 1: The Multiset monad --
--****************************--

--This code is based on the finite powerset example from:
--https://github.com/niccoloveltri/final-pfin/blob/main/Pfin/AsFreeJoinSemilattice.agda

--We define the multiset monad as the free commutative monoid monad on A.
--This is a HIT.

data Multiset {ℓ} (A : Type ℓ) : Type ℓ where
  m∅        : Multiset A
  unitM     : A → Multiset A
  _∪ₘ_      : Multiset A → Multiset A → Multiset A
  ass       : ∀ x y z → x ∪ₘ (y ∪ₘ z) ≡ (x ∪ₘ y) ∪ₘ z
  com       : ∀ x y → x ∪ₘ y ≡ y ∪ₘ x
  unitr     : ∀ x → x ∪ₘ m∅ ≡ x
  trunc     : isSet (Multiset A)


-- map function for Multiset
mapM : {A B : Set} → (A → B) → Multiset A → Multiset B
mapM f m∅ = m∅
mapM f (unitM x) = unitM (f x)
mapM f (M ∪ₘ N) = (mapM f M) ∪ₘ (mapM f N)
mapM f (ass M M₁ M₂ i) = ass (mapM f M) (mapM f M₁) (mapM f M₂) i
mapM f (com M N i) = com (mapM f M) (mapM f N) i
mapM f (unitr M i) = unitr (mapM f M) i
mapM f (trunc M N x y i i₁) = trunc (mapM f M) (mapM f N) (λ j → mapM f (x j)) (λ j → mapM f (y j)) i i₁

-- Bind an multiplication functions for Multiset
Multiset-bind : {A B : Set} → (A → Multiset B) → Multiset A → Multiset B
Multiset-bind f m∅ = m∅
Multiset-bind f (unitM a) = f a
Multiset-bind f (x ∪ₘ y) = (Multiset-bind f x) ∪ₘ (Multiset-bind f y)
Multiset-bind f (ass x y z i) = ass (Multiset-bind f x) (Multiset-bind f y) (Multiset-bind f z) i
Multiset-bind f (com x y i) = com (Multiset-bind f x) (Multiset-bind f y) i
Multiset-bind f (unitr x i) = unitr (Multiset-bind f x) i
Multiset-bind f (trunc s₁ s₂ x y i i₁) = trunc (Multiset-bind f s₁) (Multiset-bind f s₂) (\ j → Multiset-bind f (x j)) (\ j → Multiset-bind f (y j)) i i₁

Multiset-mult : {A : Set} → Multiset (Multiset A) → Multiset A
Multiset-mult m∅ = m∅
Multiset-mult (unitM x) = x
Multiset-mult (x ∪ₘ y) = (Multiset-mult x) ∪ₘ (Multiset-mult y)
Multiset-mult (ass x y z i) = ass (Multiset-mult x) (Multiset-mult y) (Multiset-mult z) i
Multiset-mult (com x y i) = com (Multiset-mult x) (Multiset-mult y) i
Multiset-mult (unitr x i) = unitr (Multiset-mult x) i
Multiset-mult (trunc s₁ s₂ x y i i₁) = trunc (Multiset-mult s₁) (Multiset-mult s₂) (\ j → Multiset-mult (x j)) (\ j → Multiset-mult (y j)) i i₁

-- Elimination principle for Multiset

-- module to make the inputs more readable
-- no name for the module to make the use of it more readable
module _ {ℓ}{A : Type ℓ}
         (P : Multiset A → hProp ℓ)
         (P∅ : fst (P m∅))
         (Pη : ∀ m → fst (P (unitM m)))
         (P∪ : ∀ {m n} → fst(P m) → fst(P n) → fst(P (m ∪ₘ n)))
         where

  elimM : ∀ M → fst(P M)
  elimM m∅ = P∅
  elimM (unitM x) = Pη x
  elimM (M ∪ₘ N) = P∪ (elimM M) (elimM N)
  elimM (ass M N O i) = isProp→PathP (λ j → snd (P (ass M N O j)))
                               ((P∪ (elimM M) (P∪ (elimM N) (elimM O))))
                               ((P∪ (P∪ (elimM M) (elimM N)) (elimM O) ))
                               i
  elimM (com M N i) = isProp→PathP (λ j → snd (P (com M N j))) (P∪ (elimM M) (elimM N)) (P∪ (elimM N) (elimM M)) i
  elimM (unitr M i) = isProp→PathP (λ j → snd (P (unitr M j))) (P∪ (elimM M) (P∅)) (elimM M) i
  elimM (trunc M N x y i j) = isOfHLevel→isOfHLevelDep 2 (λ k → isProp→isSet (snd (P k))) (elimM M) (elimM N) (cong elimM x) (cong elimM y)
                                      (trunc M N x y) i j


-- Proving that the Multiset forms a monad

-- Multiset-mult (unitM M) = M
Multiset-unitlaw1 : {A : Set} → ∀(M : Multiset A) → Multiset-mult (unitM M) ≡ M
Multiset-unitlaw1 M = refl

-- Multiset-mult (map unitM M) = M
Multiset-unitlaw2 : {A : Set} → ∀(M : Multiset A) → Multiset-mult (mapM unitM M) ≡ M
Multiset-unitlaw2 m∅ = refl
Multiset-unitlaw2 (unitM x) = refl
Multiset-unitlaw2 (M ∪ₘ N) = cong₂ (_∪ₘ_) (Multiset-unitlaw2 M) (Multiset-unitlaw2 N)
Multiset-unitlaw2 (ass M N P i) = λ j → ass (Multiset-unitlaw2 M j) (Multiset-unitlaw2 N j) (Multiset-unitlaw2 P j) i
Multiset-unitlaw2 (com M N i) = λ j → com (Multiset-unitlaw2 M j) (Multiset-unitlaw2 N j) i
Multiset-unitlaw2 (unitr M i) = λ j → unitr (Multiset-unitlaw2 M j) i
Multiset-unitlaw2 (trunc M N x y i i₁) = λ k → trunc (Multiset-unitlaw2 M k) (Multiset-unitlaw2 N k) (λ j → (Multiset-unitlaw2 (x j)) k) ((λ j → (Multiset-unitlaw2 (y j)) k)) i i₁

--proving the same with elimM:
Multiset-unitlaw2' : {A : Set} → ∀(M : Multiset A) → Multiset-mult (mapM unitM M) ≡ M
Multiset-unitlaw2' M = elimM
                        (λ N → (Multiset-mult (mapM unitM N) ≡ N) , trunc (Multiset-mult (mapM unitM N)) N)
                        refl
                        (λ N → refl)
                        (λ eq1 → λ eq2 → cong₂ _∪ₘ_ eq1 eq2 )
                        M

-- Multiset-mult (Multiset-mult M) = Multiset-mult (map Multiset-mult M) 
Multiset-multlaw : {A : Set} → ∀(M : Multiset (Multiset (Multiset A))) →  Multiset-mult (Multiset-mult M) ≡ Multiset-mult (mapM Multiset-mult M)
Multiset-multlaw m∅ = refl
Multiset-multlaw (unitM M) = refl
Multiset-multlaw (M ∪ₘ N) = cong₂ (_∪ₘ_) (Multiset-multlaw M) (Multiset-multlaw N)
Multiset-multlaw (ass M N P i) = λ j → ass (Multiset-multlaw M j) (Multiset-multlaw N j) (Multiset-multlaw P j) i
Multiset-multlaw (com M N i) = λ j → com (Multiset-multlaw M j) (Multiset-multlaw N j) i
Multiset-multlaw (unitr M i) = λ j → unitr (Multiset-multlaw M j) i
Multiset-multlaw (trunc M N x y i i₁) = λ k → trunc (Multiset-multlaw M k) (Multiset-multlaw N k) (λ j → (Multiset-multlaw (x j)) k) ((λ j → (Multiset-multlaw (y j)) k)) i i₁

--proving the same with Elim:
Multiset-multlaw' :  {A : Set} → ∀(M : Multiset (Multiset (Multiset A))) →  Multiset-mult (Multiset-mult M) ≡ Multiset-mult (mapM Multiset-mult M)
Multiset-multlaw' M = elimM
                        (λ N → (Multiset-mult (Multiset-mult N) ≡ Multiset-mult (mapM Multiset-mult N))
                              , trunc (Multiset-mult (Multiset-mult N)) (Multiset-mult (mapM Multiset-mult N)))
                        refl
                        (λ N → refl)
                        (λ eq1 → λ eq2 → cong₂ (_∪ₘ_) eq1 eq2)
                        M


-- the unit is a natural transformation:
nattrans-Multunit : {A B : Set} → ∀(f : A → B) → ∀(x : A) → mapM f (unitM x) ≡ unitM (f x)
nattrans-Multunit f x = refl

-- the multiplication is a natural transformation:
nattrans-MultisetMult : {A B : Set} → ∀(f : A → B) → ∀(MM : Multiset (Multiset A)) → mapM f (Multiset-mult MM) ≡ Multiset-mult (mapM (mapM f) MM)
nattrans-MultisetMult f MM = elimM
                               ((λ NN →  (mapM f (Multiset-mult NN) ≡ Multiset-mult (mapM (mapM f) NN))
                                      , trunc (mapM f (Multiset-mult NN)) (Multiset-mult (mapM (mapM f) NN))))
                               refl
                               (λ M → refl)
                               (λ eq1 → λ eq2 → cong₂ (_∪ₘ_) eq1 eq2)
                               MM 

--*****************************--
-- Step 2: The MultiLift monad --
--*****************************--

--Now that we have a multiset monad and a lift monad, I want to show that the following combination of the two is again a monad:
--MultiLift : (A : Set) → (κ : Cl) → Set
--MultiLift A κ = Multiset (A ⊎ (▹ κ (MultiLift A κ)))

data MultiLift (A : Set) (κ : Cl) : Set where
  conML : Multiset (A ⊎ (▹ κ (MultiLift A κ))) -> MultiLift A κ

--***algebraic structure for ListLift***--

--nowML and stepML turn MultiLift into a delay algebra structure:
nowML : {A : Set} (κ : Cl) → A → (MultiLift A κ)
nowML κ a = conML (unitM (inl a))

stepML : {A : Set} (κ : Cl) → ▹ κ (MultiLift A κ) → (MultiLift A κ)
stepML κ a = conML (unitM (inr a))

--the union is derived from the multiset union, and turns MultiLift into a monoid:
_∪ₘₗ_ : {A : Set} {κ : Cl} → (MultiLift A κ) → (MultiLift A κ) → (MultiLift A κ)
_∪ₘₗ_ {A} {κ} (conML m) (conML n) = conML (m ∪ₘ n)

--proof that this union does indeed provide a commutative monoid structure: 
assoc∪ₘₗ : {A : Set} {κ : Cl} → ∀(ml nl ol : (MultiLift A κ)) → (ml ∪ₘₗ nl) ∪ₘₗ ol ≡ ml ∪ₘₗ (nl ∪ₘₗ ol)
assoc∪ₘₗ {A} {κ} (conML m) (conML n) (conML o) = cong conML (sym (ass m n o))

comm∪ₘₗ : {A : Set} {κ : Cl} → ∀(ml nl : (MultiLift A κ)) → ml ∪ₘₗ nl ≡ nl ∪ₘₗ ml
comm∪ₘₗ {A} {κ} (conML m) (conML n) = cong conML (com m n)

unitr∪ₘₗ : {A : Set} {κ : Cl} → ∀ (ml : (MultiLift A κ)) → ml ∪ₘₗ conML m∅ ≡ ml
unitr∪ₘₗ {A} {κ} (conML m) = cong conML (unitr m )

-- Elimination principle for MultiLift

-- module to make the inputs more readable
-- no name for the module to make the use of it more readable
module _ {ℓ}{A : Set}{κ : Cl}
         (P : MultiLift A κ → hProp ℓ)
         (P∅ : fst (P (conML m∅)))
         (Pη1 : ∀ x → fst (P (conML (unitM (inl x)))))
         (Pη2 : ∀ {x} → (∀ α → fst (P (x α))) → fst (P (conML (unitM (inr x)))))
         (P∪ : ∀ {m n} → fst(P (conML m)) → fst(P (conML n)) → fst(P (conML (m ∪ₘ n))))
         where

  elimML : ∀ M → fst(P M)
  elimML (conML m∅) = P∅
  elimML (conML (unitM (inl x))) = Pη1 x
  elimML (conML (unitM (inr x))) = Pη2 λ α → elimML (x α) 
  elimML (conML (x ∪ₘ y)) = P∪ (elimML (conML x)) (elimML (conML y))
  elimML (conML (ass M N O i)) = isProp→PathP (λ j → snd (P (conML (ass M N O j))))
                               ((P∪ (elimML (conML M)) (P∪ (elimML (conML N)) (elimML (conML O)))))
                               ((P∪ (P∪ (elimML (conML M)) (elimML (conML N))) (elimML (conML O)) ))
                               i
  elimML (conML (com M N i)) = isProp→PathP (λ j → snd (P (conML (com M N j)))) (P∪ (elimML (conML M)) (elimML (conML N))) (P∪ (elimML (conML N)) (elimML (conML M))) i
  elimML (conML (unitr M i)) = isProp→PathP (λ j → snd (P (conML (unitr M j)))) (P∪ (elimML (conML M)) (P∅)) (elimML (conML M)) i
  elimML (conML (trunc M N x y i j)) = isOfHLevel→isOfHLevelDep 2 (λ z → isProp→isSet (snd (P (conML z)))) (elimML (conML M)) (elimML (conML N))
                                        (cong elimML (cong conML x)) (cong elimML (cong conML y)) (trunc M N x y ) i j



--and proof that MultiLift is a set:
--strategy: build isomorphism, then make equavalence, then use univalence to turn equivalence into equality, then transport.

isoML :  {A : Set}{κ : Cl} → Iso (Multiset (A ⊎ (▹ κ (MultiLift A κ)))) (MultiLift A κ)  
Iso.fun isoML = conML
Iso.inv isoML (conML x) = x
Iso.rightInv isoML (conML x) = refl
Iso.leftInv isoML a = refl

equivML :  {A : Set}{κ : Cl} → (Multiset (A ⊎ (▹ κ (MultiLift A κ)))) ≃ (MultiLift A κ)
equivML = isoToEquiv isoML

equalML : {A : Set}{κ : Cl} → (Multiset (A ⊎ (▹ κ (MultiLift A κ)))) ≡ (MultiLift A κ)
equalML = ua equivML

lemma0 : {A : Set}{κ : Cl} → isSet (Multiset (A ⊎ (▹ κ (MultiLift A κ)))) → isSet (MultiLift A κ)
lemma0 setM = subst⁻ isSet (sym equalML) setM

truncML : {A : Set} {κ : Cl} → isSet (MultiLift A κ)
truncML = lemma0 trunc

--a map function to turn MultiLift into a functor
mapML : {A B : Set} (κ : Cl) → (f : A → B) → (MultiLift A κ) → (MultiLift B κ)
mapML κ f (conML m∅) = conML m∅
mapML κ f (conML (unitM (inl x))) = conML (unitM (inl (f x)))
mapML κ f (conML (unitM (inr x))) = stepML κ (λ α → mapML κ f (x α))
mapML κ f (conML (x ∪ₘ y)) = (mapML κ f (conML x)) ∪ₘₗ (mapML κ f (conML y))
mapML κ f (conML (ass x y z i)) = sym (assoc∪ₘₗ (mapML κ f (conML x)) (mapML κ f (conML y)) (mapML κ f (conML z))) i
mapML κ f (conML (com x y i)) = comm∪ₘₗ (mapML κ f (conML x)) (mapML κ f (conML y)) i 
mapML κ f (conML (unitr x i)) = unitr∪ₘₗ (mapML κ f (conML x)) i
mapML κ f (conML (trunc x y z w i i₁)) = truncML (mapML κ f (conML x)) (mapML κ f (conML y)) (\ j → mapML κ f (conML (z j))) (\ j → mapML κ f (conML (w j))) i i₁

--a bind operator to make MultiLift into a monad
bindML : {A B : Set} (κ : Cl) → (A → (MultiLift B κ)) → MultiLift A κ → MultiLift B κ
bindML κ f (conML m∅) = conML m∅
bindML κ f (conML (unitM (inl x))) = f x
bindML κ f (conML (unitM (inr x))) = stepML κ (\ α → bindML κ f (x α))
bindML κ f (conML (x ∪ₘ y)) = (bindML κ f (conML x)) ∪ₘₗ (bindML κ f (conML y))
bindML κ f (conML (ass x y z i)) = sym (assoc∪ₘₗ (bindML κ f (conML x)) (bindML κ f (conML y)) (bindML κ f (conML z))) i
bindML κ f (conML (com x y i)) = comm∪ₘₗ (bindML κ f (conML x)) (bindML κ f (conML y)) i
bindML κ f (conML (unitr x i)) = unitr∪ₘₗ (bindML κ f (conML x)) i
bindML κ f (conML (trunc x y z w i i₁)) = truncML (bindML κ f (conML x)) (bindML κ f (conML y)) (\ j → bindML κ f (conML (z j))) (\ j → bindML κ f (conML (w j))) i i₁

--bindML commutes with ∪ₘₗ
bindML-∪ₘₗ : {A B : Set} (κ : Cl) → ∀(f : A → (MultiLift B κ)) → ∀(ml nl : (MultiLift A κ)) → bindML κ f (ml ∪ₘₗ nl) ≡ (bindML κ f ml) ∪ₘₗ (bindML κ f nl)
bindML-∪ₘₗ κ f (conML x) (conML y) = refl

--***proving that MultiLift is a monad***--

--bindML and nowML need to be natural transformations
nattrans-nowML : {A B : Set} (κ : Cl) → ∀(f : A → B) → ∀(x : A) → mapML κ f (nowML κ x) ≡ nowML κ (f x)
nattrans-nowML {A}{B} κ f x = refl

-- TODO: bindML

-- bindML and nowML also need to satisfy three monad laws:
-- unit is a left-identity for bind: bindML (f, nowML) = f
-- unit is a right-identity for bind: bindML (nowML, x) = x
-- bind is associative: bindML (\x ­> bindML (g, f(x)), x) = bindML(g,bindML(f, x))

-- unit is a left-identity for bind
unitlawML1 : {A B : Set} (κ : Cl) → ∀ (f : A → (MultiLift B κ)) → ∀ (x : A) → (bindML {A} κ f (nowML κ x)) ≡ f x
unitlawML1 κ f x = refl

-- unit is a right-identity for bind
unitlawML2 : {A : Set}(κ : Cl) → ∀(x : (MultiLift A κ)) → (bindML κ (nowML κ) x) ≡ x
unitlawML2 κ x = elimML ((λ y → ((bindML κ (nowML κ) y) ≡ y)
                           , truncML (bindML κ (nowML κ) y) y)) 
                         refl
                         (λ y → refl)
                         (λ p → cong conML (cong unitM (cong inr (later-ext (λ β → p β))))) 
                         (λ eq1 → λ eq2 → cong₂ _∪ₘₗ_ eq1 eq2)
                         x
-- bind is associative
assoclawML : {A B C : Set}(κ : Cl) → ∀(f : A → (MultiLift B κ)) → ∀ (g : B → (MultiLift C κ)) → ∀ (x : (MultiLift A κ))
                     → (bindML κ (\ y → (bindML κ g (f y))) x) ≡ (bindML κ g (bindML κ f x))
assoclawML {A} {B} {C} κ f g x = elimML ((λ z → ((bindML κ (\ y → (bindML κ g (f y))) z) ≡ (bindML κ g (bindML κ f z)))
                                           , truncML ((bindML κ (\ y → (bindML κ g (f y))) z)) (bindML κ g (bindML κ f z))))
                                        refl
                                        (λ y → refl)
                                        (λ p → cong conML (cong unitM (cong inr (later-ext (λ α → p α)))))
                                        (λ {m n} → λ eq1 → λ eq2 → (bindML κ (λ y → bindML κ g (f y)) (conML m) ∪ₘₗ
                                                           bindML κ (λ y → bindML κ g (f y)) (conML n))
                                                           ≡⟨ cong₂ (_∪ₘₗ_) eq1 eq2 ⟩
                                                           (bindML κ g (bindML κ f (conML m)) ∪ₘₗ bindML κ g (bindML κ f (conML n)))
                                                           ≡⟨ sym (bindML-∪ₘₗ κ g (bindML κ f (conML m)) (bindML κ f (conML n))) ⟩
                                                            bindML κ g (bindML κ f (conML m) ∪ₘₗ bindML κ f (conML n)) ∎)
                                        x