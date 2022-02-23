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

--***proof that MultiLift is a set***--
-- strategy: build isomorphism, then make equivalence, then use univalence to turn equivalence into equality, then transport.

isoML :  {A : Set}{κ : Cl} → Iso (Multiset (A ⊎ (▹ κ (MultiLift A κ)))) (MultiLift A κ)  
Iso.fun isoML = conML
Iso.inv isoML (conML x) = x
Iso.rightInv isoML (conML x) = refl
Iso.leftInv isoML a = refl

equivML :  {A : Set}{κ : Cl} → (Multiset (A ⊎ (▹ κ (MultiLift A κ)))) ≃ (MultiLift A κ)
equivML = isoToEquiv isoML

equalML : {A : Set}{κ : Cl} → (Multiset (A ⊎ (▹ κ (MultiLift A κ)))) ≡ (MultiLift A κ)
equalML = ua equivML

truncML : {A : Set} {κ : Cl} → isSet (MultiLift A κ)
truncML = subst⁻ isSet (sym equalML) trunc

--***algebraic structure for MultiLift***--

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

--***monadic structure for MultiLift***--

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

--***proof that MultiLift is a monad***--

--bindML and nowML need to be natural transformations
nattrans-nowML : {A B : Set} (κ : Cl) → ∀(f : A → B) → ∀(x : A) → mapML κ f (nowML κ x) ≡ nowML κ (f x)
nattrans-nowML {A}{B} κ f x = refl

-- TODO: bindML

-- bindML and nowML also need to satisfy three monad laws:
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


--*************************************************************************************--
-- Step 3: The MultiLift monad as the free delay-algebra and commutiative monoid monad --
--*************************************************************************************--

-- We already know that (MultiLift, stepML) forms a delay algebra structure,
-- and (Multilift, conML m∅ ,  ∪ₘₗ) forms a commutative monoid.
-- What we need to show is that MultiLift is the free monad with these properties.
-- That is, for a set A, and any other structure (B, δ, ε, _·_) where (B, δ) is a delay algebra and (B, ε, _·_) a commutative monoid
-- given a function f : A → B, there is a unique function MultiLift A → B extending f that preserves the algebra structures.

record IsComMonoid {A : Set} (ε : A) (_·_ : A → A → A) : Set where
  constructor iscommonoid

  field
    asso : (x y z : A) → (x · y) · z ≡ x · (y · z)
    comm : (x y : A) → (x · y) ≡ (y · x)
    uniteq : (x : A) → x · ε ≡ x

record IsDelayComMonoid {A : Set}(κ : Cl) (dm : DelayMonoidData A κ) : Set where
  constructor isdelaycommonoid

  open DelayMonoidData dm
  field
    isComMonoid : IsComMonoid (ε) (_·_)
    isDelayalg : IsDelayalg κ (nextA)

  open IsComMonoid isComMonoid public
  open IsDelayalg isDelayalg public


record IsExtendingML {A B : Set}{κ : Cl} (f : A → B) (h : (MultiLift A κ) → B) : Set where
  constructor isextendingML

  field
    extends : (x : A) → h (nowML κ x) ≡ (f x)

--foldML defines the function we are after
foldML : {A B : Set}{κ : Cl} → isSet A → isSet B → ∀ dm → IsDelayComMonoid {B} κ dm → (A → B) → (MultiLift A κ) → B
foldML setA setB (dmdata nextB ε _·_) isDMB f (conML m∅) = ε
foldML setA setB (dmdata nextB ε _·_) isDMB f (conML (unitM (inl x))) = f x
foldML setA setB dm@(dmdata nextB ε _·_) isDMB f (conML (unitM (inr x))) = nextB (λ α → foldML setA setB dm isDMB f (x α))
foldML setA setB dm@(dmdata nextB ε _·_) isDMB f (conML (x ∪ₘ y)) = (foldML setA setB dm isDMB f (conML x)) · (foldML setA setB dm isDMB f (conML y))
foldML setA setB dm@(dmdata nextB ε _·_) isDMB f (conML (ass x y z i)) = sym (IsDelayComMonoid.asso isDMB (foldML setA setB dm isDMB f (conML x))
                                                                                                     (foldML setA setB dm isDMB f (conML y))
                                                                                                     (foldML setA setB dm isDMB f (conML z))) i
foldML setA setB dm@(dmdata nextB ε _·_) isDMB f (conML (com x y i)) = IsDelayComMonoid.comm isDMB (foldML setA setB dm isDMB f (conML x)) (foldML setA setB dm isDMB f (conML y)) i
foldML setA setB dm@(dmdata nextB ε _·_) isDMB f (conML (unitr x i)) = IsDelayComMonoid.uniteq isDMB (foldML setA setB dm isDMB f (conML x)) i
foldML setA setB dm@(dmdata nextB ε _·_) isDMB f (conML (trunc x y x₁ y₁ i i₁)) = setB (foldML setA setB dm isDMB f (conML x))
                                                                                      (foldML setA setB dm isDMB f (conML y))
                                                                                      (λ j → (foldML setA setB dm isDMB f (conML (x₁ j))))
                                                                                      (λ j → (foldML setA setB dm isDMB f (conML (y₁ j))))
                                                                                      i i₁


--foldML extends the function f : A → B
foldML-extends : {A B : Set}{κ : Cl} → ∀(setA : isSet A) → ∀(setB : isSet B) → ∀ dm → ∀(isDMB : IsDelayComMonoid {B} κ dm) →
                   ∀ (f : A → B) → IsExtendingML f (foldML setA setB dm isDMB f)
IsExtendingML.extends (foldML-extends setA setB dm isDMB f) x = refl

-- or a more direct proof of the same fact:
foldML-extends-f : {A B : Set}{κ : Cl} → ∀(setA : isSet A) → ∀(setB : isSet B) → ∀ dm → ∀(isDMB : IsDelayComMonoid {B} κ dm) →
                   ∀ (f : A → B) → ∀ (x : A) → foldML setA setB dm isDMB f (nowML κ x) ≡ f x
foldML-extends-f setA setB dm isDMB f x = refl

--foldML preseves the DelayMonoid structure
 
module _ {A B : Set}{κ : Cl} (setA : isSet A) (setB : isSet B) (dm : _) (isDMB : IsDelayComMonoid {B} κ dm)
         (f : A → B)
 where
  open IsPreservingDM
  open DelayMonoidData dm renaming (nextA to nextB)

  foldML-preserves : IsPreservingDM {MultiLift A κ}{B} κ (dmdata (stepML κ) (conML m∅) _∪ₘₗ_) dm (foldML setA setB dm isDMB f)
  unit-preserve foldML-preserves = refl
  next-preserve foldML-preserves x = cong nextB (later-ext (λ α → refl))
  union-preserve foldML-preserves (conML x) (conML y) = refl

--and foldML is unique in doing so.
--That is, for any function h that both preserves the algebra structure
--and extends the function f : A → B,
-- h is equivalent to fold.

module _ {A B : Set} {κ : Cl} (h : MultiLift A κ → B)
                       (setA : isSet A) (setB : isSet B) (dm : _) (isDMB : IsDelayComMonoid {B} κ dm)
                       (f : A → B) (isPDM : IsPreservingDM {MultiLift A κ}{B} κ (dmdata (stepML κ) (conML m∅) _∪ₘₗ_ ) dm h)
                       (isExt : IsExtendingML f h) where

  open DelayMonoidData dm renaming (nextA to nextB)

  fold-uniquenessML : (x : (MultiLift A κ)) → h x ≡ (foldML setA setB dm isDMB f x)
  fold-uniquenessML x = elimML
                           ((λ x → (h x ≡ (foldML setA setB dm isDMB f x)) , setB (h x) ((foldML setA setB dm isDMB f x))))
                           (IsPreservingDM.unit-preserve isPDM)
                           (λ a →  h (conML (unitM (inl a)))
                                    ≡⟨ refl ⟩
                                    h (nowML κ a)
                                    ≡⟨ IsExtendingML.extends isExt a ⟩
                                    f a ∎)
                           (λ {x} → λ eq → h (conML (unitM (inr x)))
                                            ≡⟨ refl ⟩
                                            h (stepML κ x)
                                            ≡⟨ IsPreservingDM.next-preserve isPDM x ⟩
                                            nextB (λ α → h (x α)) 
                                            ≡⟨ cong nextB (later-ext (λ α → (eq α)))  ⟩ 
                                            nextB (λ α → foldML setA setB (dmdata nextB ε _·_) isDMB f (x α)) ∎)
                           (λ {x y} → λ eqx eqy → h (conML (x ∪ₘ y))
                                                   ≡⟨ refl ⟩
                                                   h ((conML x) ∪ₘₗ (conML y))
                                                   ≡⟨ IsPreservingDM.union-preserve isPDM (conML x) (conML y) ⟩
                                                   (h (conML x) · h (conML y))
                                                   ≡⟨ cong₂ _·_ eqx eqy ⟩
                                                   (foldML setA setB (dmdata nextB ε _·_) isDMB f (conML x) ·
                                                   foldML setA setB (dmdata nextB ε _·_) isDMB f (conML y)) ∎)
                           x


--****************************************************--
-- Composing Lift and Multiset via a distributive law --
--****************************************************--

--We now define a composite monad of the Multiset and Lift monads, formed via a distributive law.
LcM : (A : Set) → (κ : Cl) → Set
LcM A κ = myLift (Multiset A) κ

-- the unit of this monad is simply the composit of the units for Lift (nowL x) and Multiset (unitM)
nowLcM : {A : Set} {κ : Cl} → A → (LcM A κ) 
nowLcM x = nowL (unitM x)

--LcM is a set.

truncLcM : {A : Set} {κ : Cl} → isSet (LcM A κ)
truncLcM = {!!}

-- we define a union on LcM, which will help in defining the distributive law.
_l∪m_ : {A : Set} {κ : Cl} → (LcM A κ) → (LcM A κ) → (LcM A κ)
nowL x l∪m nowL y = nowL (x ∪ₘ y)
nowL x l∪m stepL y = stepL (λ α → (nowL x l∪m (y α)))
stepL x l∪m y = stepL (λ α → ((x α) l∪m y))

--l∪m is associative, commutative, and nowL m∅ is a unit for l∪l
assoc-l∪m : {A : Set} {κ : Cl} → ∀(x y z : LcM A κ) → (x l∪m y) l∪m z ≡ x l∪m (y l∪m z)
assoc-l∪m (nowL x) (nowL y) (nowL z) = cong nowL (sym (ass x y z))
assoc-l∪m (nowL x) (nowL y) (stepL z) = cong stepL (later-ext λ α → assoc-l∪m (nowL x) (nowL y) (z α))
assoc-l∪m (nowL x) (stepL y) z = cong stepL (later-ext λ α → assoc-l∪m (nowL x) (y α) z)
assoc-l∪m (stepL x) y z = cong stepL (later-ext λ α → assoc-l∪m (x α) y z)

comm-l∪m : {A : Set} {κ : Cl} → ∀(x y : LcM A κ) → (x l∪m y) ≡ y l∪m x
comm-l∪m (nowL x) (nowL y) = cong nowL (com x y)
comm-l∪m (nowL x) (stepL y) = cong stepL (later-ext λ α → comm-l∪m (nowL x) (y α))
comm-l∪m (stepL x) (nowL y) = cong stepL (later-ext λ α → comm-l∪m (x α) (nowL y))
comm-l∪m (stepL x) (stepL y) = stepL (λ α → x α l∪m stepL y)
                                 ≡⟨ cong stepL (later-ext λ α → comm-l∪m (x α) (stepL y))  ⟩
                                 stepL (λ α → stepL y l∪m x α)
                                 ≡⟨ refl ⟩
                                 stepL (λ α → stepL (λ β → (y β) l∪m (x α)))
                                 ≡⟨ cong stepL (later-ext λ α → cong stepL (later-ext λ β → cong₂ _l∪m_ (sym (tick-irr y α β)) (tick-irr x α β) )) ⟩
                                 stepL (λ α → stepL (λ β → (y α) l∪m (x β)))
                                 ≡⟨ cong stepL (later-ext λ α → cong stepL (later-ext λ β → comm-l∪m (y α) (x β))) ⟩
                                 stepL (λ α → stepL (λ β → (x β) l∪m (y α)))
                                 ≡⟨ refl ⟩
                                 stepL (λ α → (stepL x) l∪m (y α))
                                 ≡⟨ cong stepL (later-ext λ α → comm-l∪m (stepL x) (y α)) ⟩
                                 stepL (λ α → y α l∪m stepL x) ∎


unit-l∪m : {A : Set} {κ : Cl} → ∀(x : LcM A κ) → x l∪m (nowL m∅) ≡ x
unit-l∪m (nowL x) = cong nowL (unitr x)
unit-l∪m (stepL x) = cong stepL (later-ext λ α → unit-l∪m (x α))

--mapL κ f distributes over l∪m if f distributes over ∪ₘ
dist-mapL-l∪m : {A B : Set} {κ : Cl} → ∀(f : (Multiset A) → (Multiset B)) → ∀(fdist : ∀(m n : Multiset A) → f (m ∪ₘ n) ≡ f m ∪ₘ f n)
                                     → ∀(x y : (LcM A κ)) → mapL κ f (x l∪m y) ≡ (mapL κ f x) l∪m (mapL κ f y)
dist-mapL-l∪m f fdist (nowL x) (nowL y) = cong nowL (fdist x y)
dist-mapL-l∪m f fdist (nowL x) (stepL y) = cong stepL (later-ext λ α → dist-mapL-l∪m f fdist (nowL x) (y α))
dist-mapL-l∪m f fdist (stepL x) y = cong stepL (later-ext λ α → dist-mapL-l∪m f fdist (x α) y)

-- LcM is a monad via a distributive law, distributing Multiset over Lift.
-- Here is the distributive law:
distlawLcM : {A : Set} {κ : Cl} → Multiset (myLift A κ) → (LcM A κ)
distlawLcM m∅ = nowL m∅
distlawLcM (unitM (nowL x)) = nowL (unitM x)
distlawLcM (unitM (stepL x)) = stepL (λ α → distlawLcM (unitM (x α)))
distlawLcM (x ∪ₘ y) = (distlawLcM x) l∪m (distlawLcM y)
distlawLcM (ass x y z i) = assoc-l∪m (distlawLcM x) (distlawLcM y) (distlawLcM z) (~ i)
distlawLcM (com x y i) = comm-l∪m (distlawLcM x) (distlawLcM y) i
distlawLcM (unitr x i) = unit-l∪m (distlawLcM x) i
distlawLcM (trunc x y x₁ y₁ i i₁) = truncLcM (distlawLcM x) (distlawLcM y) (λ j → distlawLcM (x₁ j)) (λ j → distlawLcM (y₁ j)) i i₁

--proof that distlawLcL is indeed a distributive law:
--unit laws:
unitlawLcM1 : {A : Set} {κ : Cl} → ∀(x : myLift A κ) → (distlawLcM (unitM x)) ≡  mapL κ unitM x
unitlawLcM1 (nowL x) = refl
unitlawLcM1 (stepL x) = cong stepL (later-ext λ α → unitlawLcM1 (x α))

unitlawLcM2 : {A : Set} {κ : Cl} → ∀(M : Multiset A) → (distlawLcM (mapM nowL M)) ≡ nowL M
unitlawLcM2 M = elimM
                 (λ N → ((distlawLcM (mapM nowL N) ≡ nowL N) , truncLcM (distlawLcM (mapM nowL N)) (nowL N)))
                 refl
                 (λ N → refl)
                 (λ {M N} → λ eqM eqN → distlawLcM (mapM nowL M) l∪m distlawLcM (mapM nowL N)
                                         ≡⟨ cong₂ (_l∪m_) eqM eqN ⟩
                                         ((nowL M) l∪m (nowL N))
                                         ≡⟨ refl ⟩
                                         nowL (M ∪ₘ N) ∎ )
                 M


--multiplication laws:

mapL-identity : {A : Set} {κ : Cl} → ∀ (x : myLift A κ) → mapL κ (λ y → y) x ≡ x
mapL-identity (nowL x) = refl
mapL-identity (stepL x) = cong stepL (later-ext λ α → mapL-identity (x α))


multlawLcM1 : {A : Set} (κ : Cl) → ∀(M : Multiset (Multiset (myLift A κ))) → distlawLcM (Multiset-mult M) ≡
                                                                             mapL κ Multiset-mult (distlawLcM (mapM distlawLcM M))
multlawLcM1 κ M = elimM
                    (λ N → ((distlawLcM (Multiset-mult N) ≡ mapL κ Multiset-mult (distlawLcM (mapM distlawLcM N))) ,
                     truncLcM (distlawLcM (Multiset-mult N)) (mapL κ Multiset-mult (distlawLcM (mapM distlawLcM N))) ))
                    refl
                    (λ N → distlawLcM N
                            ≡⟨ sym (mapL-identity (distlawLcM N)) ⟩
                            mapL κ (λ y → y) (distlawLcM N)
                            ≡⟨ cong₂ (mapL κ) (funExt (λ y → sym (Multiset-unitlaw1 y))) refl ⟩
                            mapL κ (λ y → Multiset-mult (unitM y)) (distlawLcM N)
                            ≡⟨ sym (mapmapL κ unitM Multiset-mult (distlawLcM N)) ⟩
                            mapL κ Multiset-mult (mapL κ unitM (distlawLcM N)) 
                            ≡⟨ cong (mapL κ Multiset-mult) (sym (unitlawLcM1 (distlawLcM N)))  ⟩
                            mapL κ Multiset-mult (distlawLcM (unitM (distlawLcM N))) ∎)
                    (λ {M N} → λ eqM eqN → (distlawLcM (Multiset-mult M) l∪m distlawLcM (Multiset-mult N))
                              ≡⟨ cong₂ _l∪m_ eqM eqN ⟩
                              (mapL κ Multiset-mult (distlawLcM (mapM distlawLcM M)) l∪m mapL κ Multiset-mult (distlawLcM (mapM distlawLcM N)))
                              ≡⟨ sym (dist-mapL-l∪m Multiset-mult (λ x y → refl) (distlawLcM (mapM distlawLcM M)) (distlawLcM (mapM distlawLcM N))) ⟩
                              mapL κ Multiset-mult (distlawLcM (mapM distlawLcM M) l∪m distlawLcM (mapM distlawLcM N)) ∎)
                    M 


lemma-multlawLcM2-unitMcase-unitMcase : {A : Set} (κ : Cl) → ∀(x : (myLift A κ)) → ∀(y : (myLift (myLift A κ) κ)) → 
                                          (MultL κ (mapL κ distlawLcM (distlawLcM (unitM (nowL x)))) l∪m MultL κ (mapL κ distlawLcM (distlawLcM (unitM y))))
                                           ≡ MultL κ (mapL κ distlawLcM (distlawLcM (unitM (nowL x)) l∪m distlawLcM (unitM y)))
lemma-multlawLcM2-unitMcase-unitMcase κ x (nowL y) = refl
lemma-multlawLcM2-unitMcase-unitMcase κ x (stepL y) = (distlawLcM (unitM x) l∪m
                                                        stepL (λ α → MultL κ (mapL κ distlawLcM (distlawLcM (unitM (y α))))))
                                                        ≡⟨ comm-l∪m (distlawLcM (unitM x))
                                                                    (stepL (λ α → MultL κ (mapL κ distlawLcM (distlawLcM (unitM (y α)))))) ⟩
                                                        (stepL (λ α → MultL κ (mapL κ distlawLcM (distlawLcM (unitM (y α))))) l∪m
                                                         distlawLcM (unitM x))
                                                        ≡⟨ refl ⟩
                                                        stepL (λ α → (MultL κ (mapL κ distlawLcM (distlawLcM (unitM (y α)))) l∪m
                                                        distlawLcM (unitM x)))
                                                        ≡⟨ cong stepL (later-ext λ α → comm-l∪m (MultL κ (mapL κ distlawLcM (distlawLcM (unitM (y α)))))
                                                                                                (distlawLcM (unitM x)) ) ⟩
                                                        stepL (λ α → (distlawLcM (unitM x) l∪m
                                                        (MultL κ (mapL κ distlawLcM (distlawLcM (unitM (y α)))))))
                                                        ≡⟨ refl ⟩
                                                        stepL (λ α → (MultL κ (mapL κ distlawLcM (distlawLcM (unitM (nowL x))))) l∪m
                                                        (MultL κ (mapL κ distlawLcM (distlawLcM (unitM (y α))))))
                                                        ≡⟨ cong stepL (later-ext λ α → lemma-multlawLcM2-unitMcase-unitMcase κ x (y α)) ⟩
                                                        stepL (λ α → MultL κ (mapL κ distlawLcM (nowL (unitM x) l∪m distlawLcM (unitM (y α))))) ∎

lemma-multlawLcM2-unitMcase : {A : Set} (κ : Cl) → ∀(x : (myLift (myLift A κ) κ)) → ∀ (N : Multiset (myLift (myLift A κ) κ)) →
                                 (MultL κ (mapL κ distlawLcM (distlawLcM (unitM x))) l∪m MultL κ (mapL κ distlawLcM (distlawLcM N)))
                                  ≡ MultL κ (mapL κ distlawLcM (distlawLcM (unitM x) l∪m distlawLcM N))
lemma-multlawLcM2-unitMcase κ (nowL x) N = elimM
                                            (λ N → (((MultL κ (mapL κ distlawLcM (distlawLcM (unitM (nowL x)))) l∪m MultL κ (mapL κ distlawLcM (distlawLcM N)))
                                                   ≡ (MultL κ (mapL κ distlawLcM (distlawLcM (unitM (nowL x)) l∪m distlawLcM N)))) ,
                                                   truncLcM (MultL κ (mapL κ distlawLcM (distlawLcM (unitM (nowL x)))) l∪m MultL κ (mapL κ distlawLcM (distlawLcM N)))
                                                            (MultL κ (mapL κ distlawLcM (distlawLcM (unitM (nowL x)) l∪m distlawLcM N)))
                                                    ))
                                            refl
                                            (λ y → lemma-multlawLcM2-unitMcase-unitMcase κ x y)
                                            (λ {M N} → λ eqM eqN →
                                               {!MultL κ (mapL κ distlawLcM (distlawLcM (unitM (nowL x)))) l∪m
                                                MultL κ (mapL κ distlawLcM (distlawLcM M l∪m distlawLcM N))
                                                ≡⟨ cong (MultL κ (mapL κ distlawLcM (distlawLcM (unitM (nowL x)))) l∪m_)
                                                        (sym (lemma-lum κ M N)) ⟩
                                                (MultL κ (mapL κ distlawLcM (distlawLcM (unitM (nowL x)))) l∪m
                                                (MultL κ (mapL κ distlawLcM (distlawLcM M)) l∪m
                                                 MultL κ (mapL κ distlawLcM (distlawLcM N))))
                                                ≡⟨ sym (assoc-l∪m (MultL κ (mapL κ distlawLcM (distlawLcM (unitM (nowL x)))))
                                                                  (MultL κ (mapL κ distlawLcM (distlawLcM M)))
                                                                  (MultL κ (mapL κ distlawLcM (distlawLcM N)))) ⟩
                                                ((MultL κ (mapL κ distlawLcM (distlawLcM (unitM (nowL x)))) l∪m
                                                  MultL κ (mapL κ distlawLcM (distlawLcM M))) l∪m
                                                  MultL κ (mapL κ distlawLcM (distlawLcM N)))
                                                ≡⟨ cong (_l∪m MultL κ (mapL κ distlawLcM (distlawLcM N)))
                                                        (lemma-lum κ (unitM (nowL x)) M) ⟩
                                                (MultL κ (mapL κ distlawLcM (nowL (unitM x) l∪m (distlawLcM M))) l∪m
                                                 MultL κ (mapL κ distlawLcM (distlawLcM N)))
                                                ≡⟨ refl ⟩
                                                (MultL κ (mapL κ distlawLcM (distlawLcM (unitM (nowL x)) l∪m (distlawLcM M))) l∪m
                                                 MultL κ (mapL κ distlawLcM (distlawLcM N)))
                                                ≡⟨ refl ⟩
                                                (MultL κ (mapL κ distlawLcM (distlawLcM (unitM (nowL x) ∪ₘ M))) l∪m
                                                 MultL κ (mapL κ distlawLcM (distlawLcM N)))
                                                ≡⟨ lemma-lum κ (unitM (nowL x) ∪ₘ M) N ⟩
                                                MultL κ (mapL κ distlawLcM ((distlawLcM (unitM (nowL x) ∪ₘ M)) l∪m distlawLcM N))
                                                ≡⟨ refl ⟩
                                                MultL κ (mapL κ distlawLcM ((nowL (unitM x) l∪m distlawLcM M) l∪m distlawLcM N))
                                                ≡⟨ cong (MultL κ) (cong (mapL κ distlawLcM)
                                                                        (assoc-l∪m (nowL (unitM x)) (distlawLcM M) (distlawLcM N))) ⟩
                                                MultL κ (mapL κ distlawLcM (nowL (unitM x) l∪m (distlawLcM M l∪m distlawLcM N))) ∎!})
                                            N
lemma-multlawLcM2-unitMcase κ (stepL x) N = cong stepL (later-ext λ α → lemma-multlawLcM2-unitMcase κ (x α) N)

lemma-multlawLcM2 : {A : Set} (κ : Cl) → ∀(M N : Multiset (myLift (myLift A κ) κ)) →
                                 (MultL κ (mapL κ distlawLcM (distlawLcM M)) l∪m MultL κ (mapL κ distlawLcM (distlawLcM N)))
                                  ≡ MultL κ (mapL κ distlawLcM (distlawLcM M l∪m distlawLcM N))

lemma-multlawLcM2 κ M N = elimM
                          (λ M → ((MultL κ (mapL κ distlawLcM (distlawLcM M)) l∪m MultL κ (mapL κ distlawLcM (distlawLcM N)))
                                  ≡ MultL κ (mapL κ distlawLcM (distlawLcM M l∪m distlawLcM N))) ,
                                  truncLcM (MultL κ (mapL κ distlawLcM (distlawLcM M)) l∪m MultL κ (mapL κ distlawLcM (distlawLcM N)))
                                            (MultL κ (mapL κ distlawLcM (distlawLcM M l∪m distlawLcM N)))  )
                          (nowL m∅ l∪m MultL κ (mapL κ distlawLcM (distlawLcM N))
                             ≡⟨ comm-l∪m (nowL m∅) (MultL κ (mapL κ distlawLcM (distlawLcM N))) ⟩
                             (MultL κ (mapL κ distlawLcM (distlawLcM N)) l∪m nowL m∅)
                             ≡⟨ unit-l∪m (MultL κ (mapL κ distlawLcM (distlawLcM N))) ⟩
                             MultL κ (mapL κ distlawLcM (distlawLcM N))
                             ≡⟨ cong (MultL κ) (cong (mapL κ distlawLcM) (sym (unit-l∪m (distlawLcM N)))) ⟩
                             MultL κ (mapL κ distlawLcM (distlawLcM N l∪m nowL m∅ ))
                             ≡⟨ cong (MultL κ) (cong (mapL κ distlawLcM) (comm-l∪m (distlawLcM N) (nowL m∅))) ⟩
                             MultL κ (mapL κ distlawLcM (nowL m∅ l∪m distlawLcM N)) ∎ )
                          (λ x → lemma-multlawLcM2-unitMcase κ x N )
                          {!!}
                          M

-- lemma-lum κ (unitM (nowL x)) (M ∪ₘ N) = MultL κ (mapL κ distlawLcM (distlawLcM (unitM (nowL x)))) l∪m MultL κ (mapL κ distlawLcM (distlawLcM M l∪m distlawLcM N))
--                                          ≡⟨ cong (MultL κ (mapL κ distlawLcM (distlawLcM (unitM (nowL x)))) l∪m_) (sym (lemma-lum κ M N)) ⟩
--                                          (MultL κ (mapL κ distlawLcM (distlawLcM (unitM (nowL x)))) l∪m
--                                          (MultL κ (mapL κ distlawLcM (distlawLcM M)) l∪m
--                                           MultL κ (mapL κ distlawLcM (distlawLcM N))))
--                                          ≡⟨ sym (assoc-l∪m (MultL κ (mapL κ distlawLcM (distlawLcM (unitM (nowL x)))))
--                                                            (MultL κ (mapL κ distlawLcM (distlawLcM M)))
--                                                            (MultL κ (mapL κ distlawLcM (distlawLcM N)))) ⟩
--                                          ((MultL κ (mapL κ distlawLcM (distlawLcM (unitM (nowL x)))) l∪m
--                                            MultL κ (mapL κ distlawLcM (distlawLcM M))) l∪m
--                                           MultL κ (mapL κ distlawLcM (distlawLcM N)))
--                                          ≡⟨ cong (_l∪m MultL κ (mapL κ distlawLcM (distlawLcM N))) (lemma-lum κ (unitM (nowL x)) M) ⟩
--                                          (MultL κ (mapL κ distlawLcM (nowL (unitM x) l∪m (distlawLcM M))) l∪m MultL κ (mapL κ distlawLcM (distlawLcM N)))
--                                          ≡⟨ refl ⟩
--                                          (MultL κ (mapL κ distlawLcM (distlawLcM (unitM (nowL x)) l∪m (distlawLcM M))) l∪m MultL κ (mapL κ distlawLcM (distlawLcM N)))
--                                          ≡⟨ refl ⟩
--                                          (MultL κ (mapL κ distlawLcM (distlawLcM (unitM (nowL x) ∪ₘ M))) l∪m MultL κ (mapL κ distlawLcM (distlawLcM N)))
--                                          ≡⟨ lemma-lum κ (unitM (nowL x) ∪ₘ M) N ⟩
--                                          MultL κ (mapL κ distlawLcM ((distlawLcM (unitM (nowL x) ∪ₘ M)) l∪m distlawLcM N))
--                                          ≡⟨ refl ⟩
--                                          MultL κ (mapL κ distlawLcM ((nowL (unitM x) l∪m distlawLcM M) l∪m distlawLcM N))
--                                          ≡⟨ cong (MultL κ) (cong (mapL κ distlawLcM) (assoc-l∪m (nowL (unitM x)) (distlawLcM M) (distlawLcM N))) ⟩
--                                          MultL κ (mapL κ distlawLcM (nowL (unitM x) l∪m (distlawLcM M l∪m distlawLcM N))) ∎
-- lemma-lum κ (unitM (nowL x)) (ass M N O i) = {!!}
-- lemma-lum κ (unitM (nowL x)) (com M N i) = {!!}
-- lemma-lum κ (unitM (nowL x)) (unitr M i) = {!!}
-- lemma-lum κ (unitM (nowL x)) (trunc M N y z i i₁) = {!!}
-- lemma-lum κ (unitM (stepL x)) N = cong stepL (later-ext λ α → lemma-lum κ (unitM (x α)) N  )
-- lemma-lum κ (M ∪ₘ M₁) N = {!!}

-- I don't know how to split cases within elimM, so here a lemma for the unitM case of elimM for multlawLcM2, split into nowL and stepL:
multlawLcM2-unitMcase : {A : Set} {κ : Cl} → ∀(x : (myLift (myLift A κ) κ)) →
                                     distlawLcM (mapM (MultL κ) (unitM x)) ≡ MultL κ (mapL κ distlawLcM (distlawLcM (unitM x)))
multlawLcM2-unitMcase (nowL x) = refl
multlawLcM2-unitMcase (stepL x) = cong stepL (later-ext λ α → multlawLcM2-unitMcase (x α))

-- and here the full proof of the second multiplication law:
multlawLcM2 : {A : Set} (κ : Cl) → ∀(M : Multiset (myLift (myLift A κ) κ)) →
                                     distlawLcM (mapM (MultL κ) M) ≡ MultL κ (mapL κ distlawLcM (distlawLcM M))
multlawLcM2 κ M = elimM
                   (λ N → ((distlawLcM (mapM (MultL κ) N) ≡ MultL κ (mapL κ distlawLcM (distlawLcM N))) ,
                          truncLcM (distlawLcM (mapM (MultL κ) N)) (MultL κ (mapL κ distlawLcM (distlawLcM N)))))
                   refl
                   (λ x → multlawLcM2-unitMcase x )
                   (λ {M N} → λ eqM eqN → distlawLcM (mapM (MultL κ) M) l∪m distlawLcM (mapM (MultL κ) N)
                                           ≡⟨ cong₂ (_l∪m_) eqM eqN ⟩
                                           (MultL κ (mapL κ distlawLcM (distlawLcM M)) l∪m MultL κ (mapL κ distlawLcM (distlawLcM N)))
                                           ≡⟨ lemma-multlawLcM2 κ M N ⟩
                                           MultL κ (mapL κ distlawLcM (distlawLcM M l∪m distlawLcM N)) ∎)
                   M


