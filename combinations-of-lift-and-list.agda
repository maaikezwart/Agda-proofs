{-# OPTIONS --cubical --guarded -W ignore #-}
module combinations-of-lift-and-list where

open import Clocked.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Data.List as List
open import Cubical.Data.List.Properties
open import Cubical.Data.Sum using (_⊎_; inl; inr)

--**********************************************************************--
--**********************************************************************--
-- Combining the monads Lift and List freely and via a distributive law --
--**********************************************************************--
--**********************************************************************--

-- In this document I want to define a monad, called ListLift, that is the free combination of the Lift monad and the List monad.
-- In order to do so, I will first define the Lift monad and the List monad, and check that they are indeed monads (Step 1 and 2).
-- Then I define the LiftList monad, check that it is a monad (Step 3), and finally check that it is the free monad on the algebra
-- structures of a delay algebra and a monoid (Step 4).

-- In addition to the free combination of the List and the Lift monads, I also compose the two monads to form the monad
-- LcL : A → Lift(List A). This composition uses a distributive law, which I prove does indeed satisfy all the axioms for a
-- distributive law.


--************************--
-- Step 1: The Lift monad --
--************************--

-- Defining the monad myLift.
--(note that the return/unit is just x → nowL x)

data myLift (A : Set) (κ : Cl) : Set where
 nowL : A → (myLift A κ)
 stepL : ▹ κ (myLift A κ) → (myLift A κ) 

bindL : {A B : Set} (κ : Cl) → (A → (myLift B κ)) → myLift A κ → myLift B κ
bindL κ f (nowL a) = f a
bindL κ f (stepL x) = stepL \(α) → bindL κ f (x α)

identity : {A : Set} → A → A
identity x = x

MultL : {A : Set} (κ : Cl) → (myLift (myLift A κ) κ) → (myLift A κ)
MultL κ = bindL κ identity

mapL : {A B : Set} (κ : Cl) → (A → B) → (myLift A κ) → (myLift B κ)
mapL κ f (nowL x) = nowL (f x)
mapL κ f (stepL x) = stepL (\ α →  mapL κ f (x α))

--checking that it is indeed a monad
-- needs to satisfy three monad laws:

-- unit is a left-identity for bind: bind (f, return) = f
-- unit is a right-identity for bind: bind (return, x) = x
-- bind is associative: bind (\x ­> bind (g, f(x)), x) = bind(g,bind(f, x))

-- The first of these is satisfied by definition
-- The other two laws we check here below

-- unit law, two versions to learn and remember to ways of doing guarded recursion in agda:
unitlawL : {A : Set}(κ : Cl) → ∀(x : (myLift A κ)) → (bindL {A} κ nowL x) ≡ x
unitlawL κ (nowL x) = refl
unitlawL κ (stepL x) = cong stepL (later-ext (\ α → unitlawL κ (x α)))

unitlawL' : {A : Set}(κ : Cl) → ∀(x : (myLift A κ)) → (bindL {A} κ nowL x) ≡ x
unitlawL' κ (nowL x) = refl
unitlawL' κ (stepL x) = \ i → stepL (\ α → unitlawL' κ (x α) i )

-- associative law:
associativelawL : {A B C : Set}(κ : Cl) → ∀(f : A → (myLift B κ)) → ∀ (g : B → (myLift C κ)) →
                                                ∀ (y : (myLift A κ)) → (bindL κ (\ x → (bindL κ g (f x))) y) ≡ (bindL κ g (bindL κ f y))
associativelawL κ f g (nowL x) = refl
associativelawL κ f g (stepL x) = cong stepL (((later-ext (\ α → associativelawL κ f g (x α)))))

-- Some properties that will be useful later:

-- interaction of mapL and MultL:
MultMap : {A B : Set} (κ : Cl) → ∀(x : myLift (myLift A κ) κ) → ∀(f : A → B) → mapL κ f (MultL κ x) ≡ MultL κ (mapL κ (mapL κ f) x)
MultMap κ (nowL x) f = refl
MultMap κ (stepL x) f = \ i → stepL (\ α → MultMap κ (x α) f i)

-- mapmap for mapL
mapmapL : {A B C : Set} (κ : Cl) → ∀(f : A → B) → ∀(g : B → C) → ∀(x : myLift A κ) → mapL κ g (mapL κ f x) ≡ mapL κ (\ y → g(f y)) x
mapmapL κ f g (nowL x) = refl
mapmapL κ f g (stepL x) =  (\ i → stepL (\ α → mapmapL κ f g (x α) i ))


--************************--
-- Step 2: The List monad --
--************************--

-- Defining the monad List
--List is already defined, but we define a unit and multiplication for it, so it becomes a monad

List-unit : {A : Set} → A → List A
List-unit x = [ x ]

List-mult : {A : Set} → List (List A) → List A
List-mult {A} = foldr _++_ []

List-bind : {A B : Set} → (A → List B) → List A → List B
List-bind f [] = []
List-bind f (x ∷ xs) = (f x) ++ (List-bind f xs)

-- and some other useful functions for later
safe-head : {A : Set} → A → List A → A
safe-head x []      = x
safe-head _ (x ∷ _) = x

tail : {A : Set} → List A → List A
tail [] = []
tail (x ∷ xs) = xs

-- Proving that this forms a monad
-- satisfying the laws:
-- List-mult (List-unit L) = L
-- List-mult (map List-unit L) = L
-- List-mult (List-Mult L) = List-mult (map List-mult L)
-- and both the unit and the multiplication are natural transformations

-- List-mult (List-unit L) = L
List-unitlaw1 : {A : Set} → ∀(L : List A) → List-mult (List-unit L) ≡ L
List-unitlaw1 [] = refl
List-unitlaw1 (x ∷ L) = cong (_++_ [ x ]) (List-unitlaw1 L)

-- List-mult (map List-unit L) = L
List-unitlaw2 : {A : Set} → ∀(L : List A) → List-mult (map List-unit L) ≡ L
List-unitlaw2 [] = refl
List-unitlaw2 (x ∷ L) = cong (_++_ [ x ]) (List-unitlaw2 L )


-- List-mult (List-Mult L) = List-mult (map List-mult L)
lemma : {A : Set} → ∀(L₁ L₂ : List (List A)) -> List-mult (L₁ ++ L₂) ≡ (List-mult L₁) ++ (List-mult L₂)
lemma [] L₂ = refl
lemma (L₁ ∷ L₃) L₂ = L₁ ++ List-mult (L₃ ++ L₂)
                     ≡⟨ cong (L₁ ++_) (lemma L₃ L₂) ⟩
                     L₁ ++ ((List-mult L₃) ++ (List-mult L₂))
                     ≡⟨ sym (++-assoc L₁ (List-mult L₃) (List-mult L₂)) ⟩
                     (L₁ ++ List-mult L₃) ++ List-mult L₂
                     ≡⟨ refl ⟩
                     (List-mult (L₁ ∷ L₃)) ++ (List-mult L₂) ∎

List-multlaw : {A : Set} -> ∀(L : List (List (List A))) -> List-mult (List-mult L) ≡ List-mult (map List-mult L)
List-multlaw [] = refl
List-multlaw (L ∷ L₁) = List-mult (L ++ List-mult L₁)
                        ≡⟨ lemma L (List-mult L₁) ⟩
                        (List-mult L ++ List-mult (List-mult L₁))
                        ≡⟨ cong (List-mult L ++_) (List-multlaw L₁) ⟩
                        List-mult L ++ List-mult (map List-mult L₁) ∎

-- the unit is a natural transformation:
nattrans-Listunit : {A B : Set} → ∀(f : A → B) → ∀(x : A) → map f (List-unit x) ≡ List-unit (f x)
nattrans-Listunit f x = refl

-- the multiplication is a natural transformation:
lemma-map++ : {A B : Set} → ∀(f : A → B) → ∀(xs ys : List A) → map f (xs ++ ys) ≡ (map f xs) ++ (map f ys)
lemma-map++ f [] ys = refl
lemma-map++ f (x ∷ xs) ys = cong ((f x) ∷_) (lemma-map++ f xs ys)

nattrans-Listmult : {A B : Set} → ∀(f : A → B) → ∀(xss : List (List A)) → map f (List-mult xss) ≡ List-mult (map (map f) xss)
nattrans-Listmult f [] = refl
nattrans-Listmult f (xs ∷ xss) = map f (xs ++ List-mult xss)
                                  ≡⟨ lemma-map++ f xs (List-mult xss) ⟩
                                  map f xs ++ map f (List-mult xss) 
                                  ≡⟨ cong (map f xs ++_) (nattrans-Listmult f xss) ⟩
                                  map f xs ++ List-mult (map (map f) xss) ∎


--****************************--
-- Step 3: The ListLift monad --
--****************************--

--Now that we have a list monad and a lift monad, I want to show that the following combination of the two is again a monad:
--ListLift : (A : Set) → (κ : Cl) → Set
--ListLift A κ = List (A ⊎ (▹ κ (ListLift A κ)))

data ListLift (A : Set) (κ : Cl) : Set where
  conLL : List (A ⊎ (▹ κ (ListLift A κ))) -> ListLift A κ

--***algebraic structure for ListLift***--

--nowLL and stepLL turn ListLift into a delay algebra structure:
nowLL : {A : Set} (κ : Cl) → A → (ListLift A κ)
nowLL κ a = conLL [ (inl a) ]

stepLL : {A : Set} (κ : Cl) → ▹ κ (ListLift A κ) → (ListLift A κ)
stepLL κ a = conLL [ (inr a) ]

--union, derived from list concatenation, turns ListLift into a monoid:
_∪_ : {A : Set} {κ : Cl} → (ListLift A κ) → (ListLift A κ) → (ListLift A κ)
_∪_ {A} {κ} (conLL x) (conLL y) = conLL (x ++ y)

--proof that this union does indeed provide a monoid structure: 
conLLempty-rightunit : {A : Set} (κ : Cl) → ∀ (xs : (ListLift A κ)) → xs ∪ conLL [] ≡ xs
conLLempty-rightunit κ (conLL x) = conLL (x ++ []) ≡⟨ cong conLL (++-unit-r x) ⟩ conLL x ∎

conLLempty-leftunit : {A : Set} (κ : Cl) → ∀ (xs : (ListLift A κ)) → conLL [] ∪ xs ≡ xs
conLLempty-leftunit κ (conLL x) = refl

assoc∪ : {A : Set} {κ : Cl} → ∀(xs ys zs : (ListLift A κ)) → (xs ∪ ys) ∪ zs ≡ xs ∪ (ys ∪ zs)
assoc∪ {A} {κ} (conLL x) (conLL x₁) (conLL x₂) = cong conLL (++-assoc x x₁ x₂)

--a bind operator to make ListLift into a monad
bindLL : {A B : Set} (κ : Cl) → (A → (ListLift B κ)) → ListLift A κ → ListLift B κ
bindLL κ f (conLL []) = conLL []
bindLL κ f (conLL (inl x ∷ x₁)) = (f x) ∪ bindLL κ f (conLL x₁)
bindLL κ f (conLL (inr x ∷ x₁)) = (stepLL κ (\ α → bindLL κ f (x α))) ∪ bindLL κ f (conLL x₁)

--bind commutes with ∪
bindLL∪ : {A B : Set} (κ : Cl) → ∀(f : A → (ListLift B κ)) → ∀(xs ys : (ListLift A κ)) → bindLL κ f (xs ∪ ys) ≡ (bindLL κ f xs) ∪ (bindLL κ f ys)
bindLL∪ κ f xs (conLL []) =  bindLL κ f (xs ∪ conLL []) ≡⟨ cong (bindLL κ f) (conLLempty-rightunit κ xs)  ⟩
                                     bindLL κ f xs ≡⟨ sym (conLLempty-rightunit κ (bindLL κ f xs)) ⟩
                                     (bindLL κ f xs ∪ conLL [])∎
bindLL∪ κ f (conLL []) (conLL (x ∷ x₁)) = bindLL κ f (conLL (x ∷ x₁))
                                                 ≡⟨ sym (conLLempty-leftunit κ (bindLL κ f (conLL (x ∷ x₁)))) ⟩
                                                 (conLL [] ∪ bindLL κ f (conLL (x ∷ x₁))) ∎
bindLL∪ κ f (conLL (inl x₂ ∷ x₃)) (conLL (x ∷ x₁)) = (f x₂ ∪ bindLL κ f ((conLL x₃) ∪ (conLL (x ∷ x₁)))) ≡⟨ cong (f x₂ ∪_) (bindLL∪ κ f (conLL x₃) (conLL (x ∷ x₁))) ⟩
                                                           (f x₂ ∪ (bindLL κ f (conLL x₃) ∪ bindLL κ f (conLL (x ∷ x₁))))
                                                           ≡⟨ sym (assoc∪ (f x₂) (bindLL κ f (conLL x₃)) (bindLL κ f (conLL (x ∷ x₁))))  ⟩
                                                           ((f x₂ ∪ bindLL κ f (conLL x₃)) ∪ bindLL κ f (conLL (x ∷ x₁))) ∎
bindLL∪ κ f (conLL (inr x₂ ∷ x₃)) (conLL (x ∷ x₁)) = (conLL (inr (λ α → bindLL κ f (x₂ α)) ∷ []) ∪ bindLL κ f ((conLL x₃) ∪ (conLL (x ∷ x₁))))
                                                           ≡⟨ cong (conLL (inr (λ α → bindLL κ f (x₂ α)) ∷ []) ∪_) (bindLL∪ κ f (conLL x₃) (conLL (x ∷ x₁))) ⟩
                                                           (conLL (inr (λ α → bindLL κ f (x₂ α)) ∷ []) ∪ ((bindLL κ f (conLL x₃) ∪ bindLL κ f (conLL (x ∷ x₁)))))
                                                           ≡⟨  sym (assoc∪ (conLL (inr (λ α → bindLL κ f (x₂ α)) ∷ [])) (bindLL κ f (conLL x₃)) (bindLL κ f (conLL (x ∷ x₁))))  ⟩
                                                           ((conLL (inr (λ α → bindLL κ f (x₂ α)) ∷ []) ∪ bindLL κ f (conLL x₃)) ∪ bindLL κ f (conLL (x ∷ x₁))) ∎


--and a map function to prove naturality of bind and now
mapLL : {A B : Set} (κ : Cl) → (f : A → B) → (ListLift A κ) → (ListLift B κ)
mapLL κ f (conLL []) = conLL []
mapLL κ f (conLL (inl x ∷ x₁)) = conLL ([ inl (f x) ]) ∪ mapLL κ f (conLL x₁)
mapLL κ f (conLL (inr x ∷ x₁)) = (stepLL κ (\ α → mapLL κ f (x α))) ∪ mapLL κ f (conLL x₁)


--***proving that ListLift is a monad***--

--bindLL and nowLL need to be natural transformations
nattrans-nowLL : {A B : Set} (κ : Cl) → ∀(f : A → B) → ∀(x : A) → mapLL κ f (nowLL κ x) ≡ nowLL κ (f x)
nattrans-nowLL {A}{B} κ f x = refl

--TODO: bind is a natural transformation

-- bindLL and nowLL also need to satisfy three monad laws:
-- unit is a left-identity for bind: bind (f, nowLL) = f
-- unit is a right-identity for bind: bind (nowLL, x) = x
-- bind is associative: bind (\x ­> bind (g, f(x)), x) = bind(g,bind(f, x))

-- unit is a left-identity for bind
unitlawLL1 :  {A B : Set} (κ : Cl) → ∀ (f : A → (ListLift B κ)) → ∀ (x : A) → (bindLL {A} κ f (nowLL κ x)) ≡ f x
unitlawLL1 κ f x = (f x ∪ conLL []) ≡⟨ conLLempty-rightunit κ (f x) ⟩ f x ∎

-- unit is a right-identity for bind
unitlawLL2 : {A : Set}(κ : Cl) → ∀(x : (ListLift A κ)) → (bindLL κ (nowLL κ) x) ≡ x
unitlawLL2 κ (conLL []) = refl
unitlawLL2 κ (conLL (inl x ∷ x₁)) = (conLL ([ inl x ]) ∪ bindLL κ (nowLL κ) (conLL x₁)) ≡⟨ cong (conLL ([ inl x ]) ∪_ ) (unitlawLL2 κ (conLL x₁)) ⟩
                                          (conLL ([ inl x ]) ∪ conLL x₁) ≡⟨ refl ⟩
                                          conLL (inl x ∷ x₁) ∎
unitlawLL2 κ (conLL (inr x ∷ x₁)) = (stepLL κ (\ α → bindLL κ (nowLL κ) (x α))) ∪ bindLL κ (nowLL κ) (conLL x₁)
                                          ≡⟨ cong ((stepLL κ (\ α → bindLL κ (nowLL κ) (x α))) ∪_) (unitlawLL2 κ (conLL x₁))  ⟩
                                          (stepLL κ (\ α → bindLL κ (nowLL κ) (x α))) ∪ conLL x₁
                                          ≡⟨  cong (_∪ conLL x₁) (\ i → stepLL κ (\ α → unitlawLL2 κ (x α) i ) )   ⟩
                                          conLL ([ inr x ]) ∪ conLL x₁
                                          ≡⟨ refl ⟩
                                          conLL (inr x ∷ x₁) ∎

-- bind is associative
assoclawLL : {A B C : Set}(κ : Cl) → ∀(f : A → (ListLift B κ)) → ∀ (g : B → (ListLift C κ)) → ∀ (x : (ListLift A κ))
                     → (bindLL κ (\ y → (bindLL κ g (f y))) x) ≡ (bindLL κ g (bindLL κ f x))
assoclawLL {A} {B} {C} κ f g (conLL []) = refl
assoclawLL {A} {B} {C} κ f g (conLL (inl x ∷ x₁)) = (bindLL κ g (f x) ∪ bindLL κ (λ y → bindLL κ g (f y)) (conLL x₁))
                                                          ≡⟨ cong (bindLL κ g (f x) ∪_) (assoclawLL κ f g (conLL x₁)) ⟩
                                                          (bindLL κ g (f x) ∪ bindLL κ g (bindLL κ f (conLL x₁)))
                                                          ≡⟨ sym (bindLL∪ κ g (f x) (bindLL κ f (conLL x₁))) ⟩
                                                          bindLL κ g (f x ∪ bindLL κ f (conLL x₁)) ∎
assoclawLL {A} {B} {C} κ f g (conLL (inr x ∷ x₁)) =  (conLL (inr (λ α → bindLL κ (λ y → bindLL κ g (f y)) (x α)) ∷ []) ∪ bindLL κ (λ y → bindLL κ g (f y)) (conLL x₁))
                                                           ≡⟨ cong (conLL (inr (λ α → bindLL κ (λ y → bindLL κ g (f y)) (x α)) ∷ []) ∪_) (assoclawLL κ f g (conLL x₁)) ⟩
                                                           (conLL (inr (λ α → bindLL κ (λ y → bindLL κ g (f y)) (x α)) ∷ []) ∪ (bindLL κ g (bindLL κ f (conLL x₁))))
                                                           ≡⟨ cong (_∪ (bindLL κ g (bindLL κ f (conLL x₁)))) (\ i → stepLL κ (\ α → assoclawLL κ f g (x α) i ) ) ⟩
                                                           ((bindLL κ g (conLL (inr (λ α → bindLL κ f (x α)) ∷ []))) ∪ (bindLL κ g (bindLL κ f (conLL x₁))) )
                                                           ≡⟨ sym (bindLL∪ κ g (conLL (inr (λ α → bindLL κ f (x α)) ∷ [])) (bindLL κ f (conLL x₁))) ⟩
                                                           bindLL κ g (conLL (inr (λ α → bindLL κ f (x α)) ∷ []) ∪ bindLL κ f (conLL x₁)) ∎


-- If I want to do it via fixpoints instead:

module WithFix where
  LiftList : (A : Set) → (κ : Cl) → Set
  LiftList A κ = fix (\ (X : ▹ κ Set) → List(A ⊎ (▸ κ \ α → (X α))))

  nowLLfix : {A : Set} (κ : Cl) → A → (LiftList A κ)
  nowLLfix κ a = [ (inl a) ]

  stepLLfix : {A : Set} (κ : Cl) → ▹ κ (LiftList A κ) → (LiftList A κ)
  stepLLfix {A} κ a = transport
                     (λ i →
                        fix-eq (λ (X : ▹ κ Type) → List (A ⊎ (▸ κ (λ α → X α)))) (~ i))
                     [ (inr a) ]




--***********************************************************************--
-- Step 4: The ListLift monad as the free delay-algebra and monoid monad --
--***********************************************************************--

-- We already know that (ListLift, stepLL) forms a delay algebra structure
-- and (Listlift, conLL [], _∪_) forms a monoid.
-- What we need to show is that ListLift is the free monad with these properties.
-- That is, for a set A, and any other structure (B, δ, ε, _·_) where (B, δ) is a delay algebra and (B, ε, _·_) a monoid
-- given a function f : A → B, there is a unique function ListLift A → B extending f that preserves the algebra structures.

record IsDelayalg {A : Set}(κ : Cl)(nextA : ▹ κ A → A) : Set where
  constructor isdelayalg


record IsMonoid {A : Set} (ε : A) (_·_ : A → A → A) : Set where
  constructor ismonoid

  field
    assoc : (x y z : A) → (x · y) · z ≡ x · (y · z)
    leftid : (x : A) → ε · x ≡ x
    rightid : (x : A) → x · ε ≡ x

record DelayMonoidData (A : Set) (κ : Cl) : Set where
  constructor dmdata
  field
    nextA : ▹ κ A → A
    ε : A
    _·_ : A → A → A


record IsDelayMonoid {A : Set}(κ : Cl) (dm : DelayMonoidData A κ) : Set where
  constructor isdelaymonoid

  open DelayMonoidData dm
  field
    isMonoid : IsMonoid (ε) (_·_)
    isDelayalg : IsDelayalg κ (nextA)

  open IsMonoid isMonoid public
  open IsDelayalg isDelayalg public

record IsPreservingDM {A B : Set}(κ : Cl) dmA dmB (g : A → B) : Set where
  constructor ispreservingDM

  open DelayMonoidData dmA renaming (ε to εA)
  open DelayMonoidData dmB renaming (ε to εB; nextA to nextB; _·_ to _*_)
  field
    unit-preserve : g (εA) ≡ εB
    next-preserve : (x : ▹ κ A) → g (nextA x) ≡ nextB (\ α → g (x α))
    union-preserve : (x y : A) → g (x · y) ≡ (g x) * (g y)


record IsExtending {A B : Set}{κ : Cl} (f : A → B) (h : (ListLift A κ) → B) : Set where
  constructor isextending

  field
    extends : (x : A) → h (nowLL κ x) ≡ (f x)

--fold defines the function we are after
fold : {A B : Set}{κ : Cl} → isSet A → isSet B → ∀ dm → IsDelayMonoid {B} κ dm → (A → B) → (ListLift A κ) → B
fold setA setB (dmdata nextB ε _·_) isDMB f (conLL []) = ε
fold setA setB dm@(dmdata nextB ε _·_) isDMB f (conLL (inl x ∷ x₁)) = (f x) · fold setA setB dm isDMB f (conLL x₁)
fold setA setB dm@(dmdata nextB ε _·_) isDMB f (conLL (inr x ∷ x₁)) = (nextB (\ α → fold setA setB dm isDMB f (x α))) · fold setA setB dm isDMB f (conLL x₁)


--fold extends the function f : A → B
--  direct proof:
fold-extends-f : {A B : Set}{κ : Cl} → ∀(setA : isSet A) → ∀(setB : isSet B) → ∀ dm → ∀(isDMB : IsDelayMonoid {B} κ dm) →
                   ∀ (f : A → B) → ∀ (x : A) → fold setA setB dm isDMB f (nowLL κ x) ≡ f x
fold-extends-f setA setB dm isDMB f x = IsDelayMonoid.rightid isDMB (f x)

--  or via the record "IsExtending":
fold-extends : {A B : Set}{κ : Cl} → ∀(setA : isSet A) → ∀(setB : isSet B) → ∀ dm → ∀(isDMB : IsDelayMonoid {B} κ dm) →
                   ∀ (f : A → B) → IsExtending f (fold setA setB dm isDMB f)
IsExtending.extends (fold-extends setA setB dm isDMB f) x = IsDelayMonoid.rightid isDMB (f x)


module _ {A B : Set}{κ : Cl} (setA : isSet A) (setB : isSet B) (dm : _) (isDMB : IsDelayMonoid {B} κ dm)
         (f : A → B)
 where
  open IsPreservingDM
  open DelayMonoidData dm renaming (nextA to nextB)

  --fold preseves the DelayMonoid structure
  fold-preserves : IsPreservingDM {ListLift A κ}{B} κ (dmdata (stepLL κ) (conLL []) _∪_) dm (fold setA setB dm isDMB f)
  unit-preserve fold-preserves = refl
  next-preserve fold-preserves x = IsDelayMonoid.rightid isDMB (nextB (λ α → fold setA setB dm isDMB f (x α)))
  union-preserve fold-preserves (conLL xs) (conLL ys) = lemma-union xs ys
    where
      lemma-union : ∀ xs ys → fold setA setB dm isDMB f (conLL xs ∪ conLL ys) ≡
                      (fold setA setB dm isDMB f (conLL xs) ·
                      fold setA setB dm isDMB f (conLL ys))
      lemma-union [] y = sym (IsDelayMonoid.leftid isDMB
                                  (fold setA setB dm isDMB f (conLL y)))
      lemma-union (inl x ∷ x₁) y = (f x · fold setA setB dm isDMB f (conLL (x₁ ++ y)))
                                   ≡⟨ cong (f x ·_) (lemma-union x₁ y) ⟩
                                   ((f x · (fold setA setB dm isDMB f (conLL x₁) ·
                                            fold setA setB dm isDMB f (conLL y))))
                                   ≡⟨ sym (IsDelayMonoid.assoc isDMB (f x)
                                             (fold setA setB dm isDMB f (conLL x₁))
                                             (fold setA setB dm isDMB f (conLL y))) ⟩
                                   ((f x · fold setA setB dm isDMB f (conLL x₁)) ·
                                           fold setA setB dm isDMB f (conLL y)) ∎
      lemma-union (inr x ∷ x₁) y =
                                (nextB (λ α → fold setA setB dm isDMB f (x α)) ·
                                  fold setA setB dm isDMB f (conLL (x₁ ++ y)))
                                ≡⟨ cong (nextB (λ α → fold setA setB dm isDMB f (x α)) ·_)
                                    (lemma-union
                                       x₁ y) ⟩
                                ( (nextB (λ α → fold setA setB dm isDMB f (x α)) ·
                                    (fold setA setB dm isDMB f (conLL x₁) ·
                                     fold setA setB dm isDMB f (conLL y))))
                                ≡⟨ sym (IsDelayMonoid.assoc isDMB
                                    (nextB (λ α → fold setA setB dm isDMB f (x α)))
                                    (fold setA setB dm isDMB f (conLL x₁))
                                    (fold setA setB dm isDMB f (conLL y)))  ⟩
                                ((nextB (λ α → fold setA setB dm isDMB f (x α)) ·
                                  fold setA setB dm isDMB f (conLL x₁)) ·
                                  fold setA setB dm isDMB f (conLL y)) ∎


--and fold is unique in doing so. That is, for any function h that both preserves the algebra structure and extends the function f : A → B,
-- h is equivalent to fold.
module _ {A B : Set} {κ : Cl} (h : ListLift A κ → B)
                       (setA : isSet A) (setB : isSet B) (dm : _) (isDMB : IsDelayMonoid {B} κ dm)
                       (f : A → B) (isPDM : IsPreservingDM {ListLift A κ}{B} κ (dmdata (stepLL κ) (conLL []) _∪_ ) dm h)
                       (isExt : IsExtending f h) where

  open DelayMonoidData dm renaming (nextA to nextB)

  fold-uniquenessLL : (x : (ListLift A κ)) → h x ≡ (fold setA setB dm isDMB f x)
  fold-uniquenessLL (conLL []) = h (conLL [])
                                 ≡⟨ IsPreservingDM.unit-preserve isPDM ⟩
                                 ε
                                 ≡⟨ refl ⟩
                                 fold setA setB dm isDMB f (conLL []) ∎
  fold-uniquenessLL (conLL (inl x ∷ x₁)) = h (conLL (inl x ∷ x₁))
                                           ≡⟨ refl ⟩
                                           h ((conLL [ inl x ]) ∪ (conLL x₁))
                                           ≡⟨ IsPreservingDM.union-preserve isPDM (conLL [ inl x ]) (conLL x₁) ⟩
                                           ((h (conLL [ inl x ])) ·
                                             (h (conLL x₁)) )
                                           ≡⟨ cong (_· (h (conLL x₁)) ) (IsExtending.extends isExt x)  ⟩
                                           (f x · (h (conLL x₁)))
                                           ≡⟨ cong (f x ·_)(fold-uniquenessLL (conLL x₁)) ⟩
                                           (f x · fold setA setB dm isDMB f (conLL x₁)) ∎
  fold-uniquenessLL (conLL (inr x ∷ x₁)) =  h (conLL (inr x ∷ x₁))
                                            ≡⟨ cong (h ) refl ⟩
                                            h ((conLL [ inr x ]) ∪ (conLL x₁))
                                            ≡⟨ IsPreservingDM.union-preserve isPDM (conLL [ inr x ]) (conLL x₁) ⟩
                                            (h (conLL [ inr x ])) ·
                                              (h (conLL x₁))
                                            ≡⟨ cong (_· h (conLL x₁)) refl ⟩
                                            ((h (stepLL κ x)) ·
                                              (h (conLL x₁)) )
                                            ≡⟨ cong (_· h (conLL x₁)) (IsPreservingDM.next-preserve isPDM x) ⟩
                                            (((nextB (λ α → h (x α))) · (h (conLL x₁))))
                                            ≡⟨ cong (_· h (conLL x₁)) (cong (nextB)
                                               (later-ext (\ α → fold-uniquenessLL (x α)))) ⟩
                                            ((nextB (λ α → fold setA setB dm isDMB f (x α))) · (h (conLL x₁)))
                                            ≡⟨ cong (nextB (λ α → fold setA setB dm isDMB f (x α)) ·_)
                                                 (fold-uniquenessLL (conLL x₁)) ⟩
                                            (nextB (λ α → fold setA setB dm isDMB f (x α)) ·
                                                fold setA setB dm isDMB f (conLL x₁)) ∎




--************************************************--
-- Composing Lift and List via a distributive law --
--************************************************--

--We now define a composite monad of the List and Lift monads, formed via a distributive law.

LcL : (A : Set) → (κ : Cl) → Set
LcL A κ = myLift (List A) κ

-- the unit of this monad is simply the composit of the units for Lift (nowL x) and List ([x])
nowLcL : {A : Set} {κ : Cl} → A → (LcL A κ) 
nowLcL x = nowL [ x ]

-- LcL is a monad via a distributive law, distributing List over Lift.
-- Here is the distributive law:
distlawLcL : {A : Set} (κ : Cl) → List (myLift A κ) → (LcL A κ)
distlawLcL κ [] = nowL []
distlawLcL κ (nowL x ∷ xs) = MultL κ (nowL (mapL κ (([ x ]) ++_) (distlawLcL κ xs)))
distlawLcL κ (stepL x ∷ xs) = stepL (\ α → distlawLcL κ ((x α) ∷ xs))

--proof that distlawLcL is indeed a distributive law:
--unit laws:
unitlawLcL1 : {A : Set} (κ : Cl) → ∀(x : myLift A κ) → (distlawLcL κ (List-unit x )) ≡  mapL κ List-unit x
unitlawLcL1 κ (nowL x) = refl
unitlawLcL1 κ (stepL x) = (\ i → stepL (\ α → unitlawLcL1 κ (x α) i ))

unitlawLcL2 : {A : Set} (κ : Cl) → ∀(xs : List A) → (distlawLcL κ (map nowL xs)) ≡  nowL xs
unitlawLcL2 κ [] = refl
unitlawLcL2 κ (x ∷ xs) = mapL κ (λ ys → x ∷ ys) (distlawLcL κ (map nowL xs))
                          ≡⟨ cong (mapL κ (λ ys → x ∷ ys)) (unitlawLcL2 κ xs) ⟩
                          mapL κ (λ ys → x ∷ ys) (nowL xs)
                          ≡⟨ refl ⟩
                          nowL (x ∷ xs) ∎  

--multiplication laws:

-- In the proof of the first multiplication law, I need a lemma about list concatenation,
-- namely that putting a singleton list in front of a list of lists, and concatening the result
-- yields the same list as putting the element of the signleton in front of the first list in the list of lists,
-- and then concatenating the result.
-- The lemma is split into two parts, first the general result as described in words here,
-- followed by the specific situation in which I need it in the proofs below.
lemma7a : {A : Set} → ∀(x : A) → ∀(xss : (List (List A))) → List-mult ((x ∷ safe-head [] xss) ∷ tail xss ) ≡ List-mult (([ x ]) ∷ xss)
lemma7a x [] = refl
lemma7a x (xs ∷ xss) = refl

lemma7b : {A : Set} (κ : Cl) → ∀(y : myLift (List (List A)) κ) → ∀(x : A) →
           mapL κ (λ xss → List-mult ((x ∷ safe-head [] xss) ∷ tail xss)) y ≡ mapL κ (λ xss → List-mult (([ x ]) ∷ xss)) y
lemma7b κ (nowL xss) x = cong nowL (lemma7a x xss)
lemma7b κ (stepL xss) x = (\ i → stepL (\ α → lemma7b κ (xss α) x i ))

-- in addition, I need this rather technical lemma that allows me to pull a mapL through the distributive law.
-- without it, I could not finish the proof.
lemma8 :  {A : Set} (κ : Cl) → ∀(x : A) → ∀(xs : myLift (List A) κ) → ∀(xss : List (myLift (List A) κ)) →
                 mapL κ (λ yss → ((x ∷ safe-head [] yss) ∷ tail yss)) (distlawLcL κ (xs ∷ xss)) ≡ distlawLcL κ (mapL κ (λ ys → x ∷ ys) xs ∷ xss)
lemma8 κ x (nowL ys) [] = refl
lemma8 κ x (stepL ys) [] = (\ i → stepL (λ α → lemma8 κ x (ys α) [] i ))
lemma8 κ x (nowL []) (zs ∷ xss) =  mapL κ (λ yss → (x ∷ safe-head [] yss) ∷ tail yss) (mapL κ (λ zss → [] ∷ zss) (distlawLcL κ (zs ∷ xss)))
                                   ≡⟨ mapmapL κ ((λ zss → [] ∷ zss)) ((λ yss → (x ∷ safe-head [] yss) ∷ tail yss)) (distlawLcL κ (zs ∷ xss)) ⟩
                                   mapL κ (λ yss → (x ∷ safe-head [] ([] ∷ yss)) ∷ tail ([] ∷ yss)) (distlawLcL κ (zs ∷ xss))
                                   ≡⟨ refl ⟩
                                   mapL κ (λ yss → (x ∷ []) ∷ yss) (distlawLcL κ (zs ∷ xss)) ∎
lemma8 κ x (nowL (y ∷ ys)) (zs ∷ xss) = mapL κ (λ yss → (x ∷ safe-head [] yss) ∷ tail yss) (mapL κ (λ zss → (y ∷ ys) ∷ zss) (distlawLcL κ (zs ∷ xss)))
                                         ≡⟨ mapmapL κ ((λ zss → (y ∷ ys) ∷ zss)) ((λ yss → (x ∷ safe-head [] yss) ∷ tail yss)) (distlawLcL κ (zs ∷ xss)) ⟩
                                         mapL κ (λ yss → (x ∷ safe-head []((y ∷ ys) ∷ yss)) ∷ tail((y ∷ ys) ∷ yss)) (distlawLcL κ (zs ∷ xss))
                                         ≡⟨ refl ⟩
                                         mapL κ (λ yss → (x ∷ y ∷ ys) ∷ yss) (distlawLcL κ (zs ∷ xss)) ∎
lemma8 κ x (stepL ys) (zs ∷ xss) = (\ i → stepL (λ α → lemma8 κ x (ys α) (zs ∷ xss) i ))


--now we are ready to prove the multiplication laws:
multlawLcL1 : {A : Set} (κ : Cl) → ∀(xss : List (List (myLift A κ))) → distlawLcL κ (List-mult xss) ≡
                                     mapL κ List-mult (distlawLcL κ (map (distlawLcL κ) xss))
multlawLcL1 κ [] = refl
multlawLcL1 κ ([] ∷ xss) = distlawLcL κ (List-mult xss)
                            ≡⟨ multlawLcL1 κ xss ⟩
                            mapL κ List-mult (distlawLcL κ (map (distlawLcL κ) xss))
                            ≡⟨ refl ⟩
                            mapL κ (λ ys → List-mult ([] ∷ ys)) (distlawLcL κ (map (distlawLcL κ) xss))
                            ≡⟨ sym (mapmapL κ (\ ys → [] ∷ ys) List-mult ((distlawLcL κ (map (distlawLcL κ) xss)))) ⟩
                            mapL κ List-mult (mapL κ (λ ys → [] ∷ ys) (distlawLcL κ (map (distlawLcL κ) xss))) ∎ 
multlawLcL1 κ ((nowL x ∷ []) ∷ xss) =  mapL κ (λ ys → x ∷ ys) (distlawLcL κ (List-mult xss))
                                         ≡⟨ cong (mapL κ (λ ys → x ∷ ys)) (multlawLcL1 κ xss) ⟩
                                         mapL κ (λ ys → x ∷ ys) (mapL κ List-mult (distlawLcL κ (map (distlawLcL κ) xss)))
                                         ≡⟨ mapmapL κ List-mult (λ ys → x ∷ ys) (distlawLcL κ (map (distlawLcL κ) xss)) ⟩
                                         mapL κ (λ ys → x ∷ List-mult ys) (distlawLcL κ (map (distlawLcL κ) xss))
                                         ≡⟨ refl ⟩
                                         mapL κ (λ ys → List-mult (([ x ]) ∷ ys)) (distlawLcL κ (map (distlawLcL κ) xss))
                                         ≡⟨ sym( mapmapL κ (λ ys → ([ x ]) ∷ ys) List-mult (distlawLcL κ (map (distlawLcL κ) xss))) ⟩
                                         mapL κ List-mult (mapL κ (λ ys → ([ x ]) ∷ ys) (distlawLcL κ (map (distlawLcL κ) xss))) ∎
multlawLcL1 κ ((nowL x ∷ y ∷ xs) ∷ xss) = mapL κ (λ ys → x ∷ ys) (distlawLcL κ (List-mult ((y ∷ xs) ∷ xss)))
                                            ≡⟨ cong (mapL κ (λ ys → x ∷ ys)) (multlawLcL1 κ ((y ∷ xs) ∷ xss)) ⟩
                                            mapL κ (λ ys → x ∷ ys) (mapL κ List-mult (distlawLcL κ (map (distlawLcL κ) ((y ∷ xs) ∷ xss))))
                                            ≡⟨ mapmapL κ List-mult (λ ys → x ∷ ys) (distlawLcL κ (map (distlawLcL κ) ((y ∷ xs) ∷ xss))) ⟩
                                            mapL κ (λ yss → x ∷ (List-mult yss)) (distlawLcL κ (map (distlawLcL κ) ((y ∷ xs) ∷ xss)))
                                            ≡⟨ refl ⟩
                                            mapL κ (λ yss → x ∷ List-mult yss) (distlawLcL κ (distlawLcL κ (y ∷ xs) ∷ map (distlawLcL κ) xss))
                                            ≡⟨ refl ⟩
                                            mapL κ (λ yss → List-mult (([ x ]) ∷ yss)) (distlawLcL κ (distlawLcL κ (y ∷ xs) ∷ map (distlawLcL κ) xss))
                                            ≡⟨ sym (lemma7b κ ((distlawLcL κ (distlawLcL κ (y ∷ xs) ∷ map (distlawLcL κ) xss))) x) ⟩
                                            mapL κ (λ yss → List-mult ((x ∷ safe-head [] yss) ∷ tail yss)) (distlawLcL κ (distlawLcL κ (y ∷ xs) ∷ map (distlawLcL κ) xss)) 
                                            ≡⟨ sym (mapmapL κ ((λ yss → ((x ∷ safe-head [] yss) ∷ tail yss))) List-mult
                                                ((distlawLcL κ (distlawLcL κ (y ∷ xs) ∷ map (distlawLcL κ) xss)))) ⟩
                                            mapL κ List-mult (mapL κ (λ yss → ((x ∷ safe-head [] yss) ∷ tail yss)) (distlawLcL κ (distlawLcL κ (y ∷ xs) ∷ map (distlawLcL κ) xss)))
                                            ≡⟨ cong (mapL κ List-mult) (lemma8 κ x ((distlawLcL κ (y ∷ xs))) ((map (distlawLcL κ) xss))) ⟩
                                            mapL κ List-mult (distlawLcL κ (mapL κ (λ ys → x ∷ ys) (distlawLcL κ (y ∷ xs)) ∷ (map (distlawLcL κ) xss))) ∎
multlawLcL1 κ ((stepL x ∷ xs) ∷ xss) = (\ i → stepL (\ α → multlawLcL1 κ ((x α ∷ xs) ∷ xss) i ))


lemma9a : {A : Set} (κ : Cl) → ∀(x : ▹ κ (myLift A κ)) → ∀(y : ▹ κ (myLift (List (myLift A κ)) κ)) →
                   MultL κ (stepL (λ α → stepL (λ β → mapL κ (λ ys → distlawLcL κ (x α ∷ ys)) (y β)))) ≡
                   MultL κ (stepL (λ β → stepL (λ α → mapL κ (λ ys → distlawLcL κ (x α ∷ ys)) (y β))))
lemma9a κ x y = cong (MultL κ) (cong stepL (later-ext λ α → cong stepL (later-ext λ β →
                     cong₂ (mapL κ) (funExt (λ ys → cong (distlawLcL _) (cong₂ _∷_ (tick-irr x α β) refl)))
                                    (sym (tick-irr y α β)))))

lemma9 : {A : Set} (κ : Cl) → ∀(x : ▹ κ (myLift A κ)) → ∀(y : myLift (List (myLift A κ)) κ) →
            MultL κ (stepL (λ α → (mapL κ (λ ys → distlawLcL κ (x α ∷ ys)) y))) ≡ MultL κ (mapL κ (λ ys → stepL (λ α → distlawLcL κ (x α ∷ ys))) y)
lemma9 κ x (nowL y) = refl
lemma9 κ x (stepL y) = stepL (λ α → stepL (λ β → MultL κ (mapL κ (λ ys → distlawLcL κ (x α ∷ ys)) (y β))))
                        ≡⟨ lemma9a κ x y ⟩
                        stepL (λ β → stepL (λ α → MultL κ (mapL κ (λ ys → distlawLcL κ (x α ∷ ys)) (y β))))
                        ≡⟨ ( (\ i → stepL (\ β → lemma9 κ x (y β) i ))) ⟩
                        stepL (λ β → MultL κ (mapL κ (λ ys → stepL (λ α → distlawLcL κ (x α ∷ ys))) (y β))) ∎

multlawLcL2 : {A : Set} (κ : Cl) → ∀(xs : List (myLift (myLift A κ) κ)) → distlawLcL κ (map (MultL κ) xs) ≡
                                     MultL κ (mapL κ (distlawLcL κ) (distlawLcL κ xs))
multlawLcL2 κ [] = refl
multlawLcL2 κ (nowL (nowL x) ∷ xs) = distlawLcL κ ((nowL x) ∷ map (MultL κ) xs)
                                        ≡⟨ refl ⟩
                                        mapL κ (λ ys → x ∷ ys) (distlawLcL κ (map (MultL κ) xs))
                                        ≡⟨ cong (mapL κ (λ ys → x ∷ ys)) (multlawLcL2 κ xs) ⟩
                                        mapL κ (λ ys → x ∷ ys) (MultL κ (mapL κ (distlawLcL κ) (distlawLcL κ xs)))
                                        ≡⟨ MultMap κ (mapL κ (distlawLcL κ) (distlawLcL κ xs)) (λ ys → x ∷ ys)  ⟩
                                        MultL κ  (mapL κ (mapL κ (λ ys → x ∷ ys)) (mapL κ (distlawLcL κ) (distlawLcL κ xs)) )
                                        ≡⟨ cong (MultL κ) (mapmapL κ ((distlawLcL κ)) (mapL κ (λ ys → x ∷ ys)) ((distlawLcL κ xs))) ⟩
                                        MultL κ (mapL κ (λ ys → mapL κ (λ zs → x ∷ zs) (distlawLcL κ ys)) (distlawLcL κ xs))
                                        ≡⟨ refl ⟩
                                        MultL κ (mapL κ (λ ys → (distlawLcL κ) ((nowL x) ∷ ys)) (distlawLcL κ xs))
                                        ≡⟨ cong (MultL κ) (sym (mapmapL κ ((λ ys → (nowL x) ∷ ys)) ((distlawLcL κ)) ((distlawLcL κ xs)))) ⟩
                                        MultL κ (mapL κ (distlawLcL κ) (mapL κ (λ ys → (nowL x) ∷ ys) (distlawLcL κ xs))) ∎
multlawLcL2 κ (nowL (stepL x) ∷ xs) = distlawLcL κ ((stepL x) ∷ map (MultL κ) xs)
                                        ≡⟨ refl ⟩
                                        stepL (λ α → distlawLcL κ (x α ∷ map (MultL κ) xs))
                                        ≡⟨ refl ⟩
                                        stepL (λ α → distlawLcL κ (map (MultL κ) ((nowL (x α)) ∷ xs)))
                                        ≡⟨ (\ i → stepL (\ α → multlawLcL2 κ (((nowL (x α)) ∷ xs)) i )) ⟩
                                        stepL (λ α → MultL κ (mapL κ (distlawLcL κ) (distlawLcL κ ((nowL (x α) ∷ xs)))) )
                                        ≡⟨ refl ⟩
                                        MultL κ (stepL (λ α → (mapL κ (distlawLcL κ) (distlawLcL κ ((nowL (x α) ∷ xs))))))
                                        ≡⟨ refl ⟩
                                        MultL κ (stepL (λ α → (mapL κ (distlawLcL κ) (mapL κ (λ ys → x α ∷ ys) (distlawLcL κ xs)))))
                                        ≡⟨ cong (MultL κ) ((λ i → stepL (\ α → (mapmapL κ ((λ ys → x α ∷ ys)) ((distlawLcL κ)) ((distlawLcL κ xs))) i ))) ⟩
                                        MultL κ (stepL (λ α → (mapL κ (λ ys → distlawLcL κ (x α ∷ ys)) (distlawLcL κ xs))))
                                        ≡⟨ lemma9 κ x (distlawLcL κ xs) ⟩
                                        MultL κ (mapL κ (λ ys → stepL (λ α → distlawLcL κ (x α ∷ ys))) (distlawLcL κ xs))
                                        ≡⟨ refl ⟩
                                        MultL κ (mapL κ (λ ys → (distlawLcL κ) ((stepL x) ∷ ys)) (distlawLcL κ xs))
                                        ≡⟨ cong (MultL κ) (sym (mapmapL κ ((λ ys → (stepL x) ∷ ys)) ((distlawLcL κ)) ((distlawLcL κ xs)))) ⟩
                                        MultL κ (mapL κ (distlawLcL κ) (mapL κ (λ ys → (stepL x) ∷ ys) (distlawLcL κ xs))) ∎
multlawLcL2 κ (stepL x ∷ xs) = (\ i → stepL (\ α → multlawLcL2 κ ((x α ∷ xs)) i ))



-- Bonusmaterial:

-- we define a union on LcL.
_l∪l_ : {A : Set} {κ : Cl} → (LcL A κ) → (LcL A κ) → (LcL A κ)
nowL x l∪l nowL y = nowL (x ++ y)
nowL x l∪l stepL y = stepL (\ α → (nowL x l∪l (y α)))
stepL x l∪l y = stepL (\ α → ((x α) l∪l y))

--nowL [] is a unit for l∪l
left-unitl∪l : {A : Set} {κ : Cl} → ∀(x : LcL A κ) → (nowL []) l∪l x ≡ x
left-unitl∪l (nowL x) = refl
left-unitl∪l (stepL x) = stepL (λ α → nowL [] l∪l x α)
                    ≡⟨ ((\ i → stepL (\ α → left-unitl∪l (x α) i ))) ⟩
                    stepL (λ α → x α)
                    ≡⟨ refl ⟩
                    stepL x ∎

right-unitl∪l : {A : Set} {κ : Cl} → ∀(x : LcL A κ) → x l∪l (nowL []) ≡ x
right-unitl∪l (nowL x) = cong nowL (++-unit-r x)
right-unitl∪l (stepL x) = stepL (λ α →  x α l∪l nowL [])
                    ≡⟨ ((\ i → stepL (\ α → right-unitl∪l (x α) i ))) ⟩
                    stepL (λ α → x α)
                    ≡⟨ refl ⟩
                    stepL x ∎

--mapL κ f distributes over l∪l if f distributes over ++
dist-mapL-l∪l : {A B : Set} (κ : Cl) → ∀(f : (List A) → (List B)) → ∀(fcom : ∀(xs : List A) → ∀(ys : List A) → f (xs ++ ys) ≡ f xs ++ f ys) →
                                ∀(x : (LcL A κ)) → ∀(y : LcL A κ) →  mapL κ f (x l∪l y) ≡ (mapL κ f x) l∪l (mapL κ f y)
dist-mapL-l∪l κ f fcom (nowL x) (nowL y) = cong nowL (fcom x y)
dist-mapL-l∪l κ f fcom (nowL x) (stepL y) = (\ i → stepL (\ α → dist-mapL-l∪l κ f fcom (nowL x) (y α) i ))
dist-mapL-l∪l κ f fcom (stepL x) y  = \ i → stepL (\ α → dist-mapL-l∪l κ f fcom (x α) y i ) 
