{-# OPTIONS --cubical --guarded -W ignore #-}
module combinations-of-delay-and-writer where

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
-- Combining the monads Delay and Writr via a distributive law --
--**************************************************************--
--**************************************************************--

-- In this document we combine the Delay monad and the Writer monad via a distributive law.
-- In order to do so, we will first define the the Writer monad, and check that it is indeed a monad.
-- Then we define the Delay monad, and check that it is indeed a monad.
-- Finally we define the distributive law, prove that it is a distributive law.


--******************--
-- The Writer monad --
--******************--

-- First, we need a monoid M

record IsMonoid (M : Set) (ε : M) (_·_ : M → M → M) : Set where
  constructor ismonoid

  field
    assoc : (x y z : M) → (x · y) · z ≡ x · (y · z)
    leftid : (x : M) → ε · x ≡ x
    rightid : (x : M) → x · ε ≡ x


-- Then, we can define the write monad

Writer : (A M : Set) → (ε : M) → (_·_ : M → M → M) → (IsMonoid M ε _·_) → Set
Writer A M ε _·_ isMON = M × A

unitW : {A M : Set} {ε : M} {_·_ : M → M → M} {isMON : IsMonoid M ε _·_} → A → (Writer A M ε _·_ isMON)
unitW {A}{M}{ε}{_·_}{isMON} a = (ε , a)

multW : {A M : Set} {ε : M} {_·_ : M → M → M} {isMON : IsMonoid M ε _·_} → (Writer (Writer A M ε _·_ isMON) M ε _·_ isMON) → (Writer A M ε _·_ isMON)
multW {A}{M}{ε}{_·_}{isMON} (m , (n , a)) = (m · n , a)

mapW : {A B M : Set} {ε : M} {_·_ : M → M → M} {isMON : IsMonoid M ε _·_} → (A → B) → (Writer A M ε _·_ isMON) → (Writer B M ε _·_ isMON)
mapW f (m , a) = (m , (f a))

-- Proving that Writer forms a monad

-- multW (unitW x) = x
Writer-unitlaw1 : {A M : Set} → {ε : M} → {_·_ : M → M → M} → {isMON : IsMonoid M ε _·_} → ∀(x : (Writer A M ε _·_ isMON))
                              → multW {A}{M}{ε}{_·_}{isMON} (unitW {(Writer A M ε _·_ isMON)}{M}{ε}{_·_}{isMON} x) ≡ x
Writer-unitlaw1 {A}{M}{ε}{_·_}{isMON} (m , a) = cong₂ _,_ (IsMonoid.rightid isMON m) refl

-- multW (mapW unitW x) = x
Writer-unitlaw2 : {A M : Set} → {ε : M} → {_·_ : M → M → M} → {isMON : IsMonoid M ε _·_} → ∀(m : M) → ∀(a : A)
                              →  multW {A}{M}{ε}{_·_}{isMON} (mapW {A}{Writer A M ε _·_ isMON}{M}{ε}{_·_}{isMON}  (unitW {A}{M}{ε}{_·_}{isMON}) (m , a)) ≡ (m , a)
Writer-unitlaw2 {A}{M}{ε}{_·_}{isMON} m a =  multW {A}{M}{ε}{_·_}{isMON} (mapW {A}{Writer A M ε _·_ isMON}{M}{ε}{_·_}{isMON}  (unitW {A}{M}{ε}{_·_}{isMON}) (m , a))
                                              ≡⟨ refl ⟩
                                              multW {A}{M}{ε}{_·_}{isMON} (m , (ε , a))
                                              ≡⟨ refl ⟩
                                              ((m · ε) , a)
                                              ≡⟨ cong₂ (_ , _) (IsMonoid.rightid isMON m) refl ⟩
                                              (m , a) ∎

-- multW (multW f) = multW (mapW MultW f) 
Writer-multlaw : {A M : Set} → {ε : M} → {_·_ : M → M → M} → {isMON : IsMonoid M ε _·_} → ∀(x : Writer (Writer (Writer A M ε _·_ isMON) M ε _·_ isMON) M ε _·_ isMON) →
                       multW {A}{M}{ε}{_·_}{isMON} (multW {Writer A M ε _·_ isMON}{M}{ε}{_·_}{isMON} x) ≡
                       multW {A}{M}{ε}{_·_}{isMON} (mapW {Writer (Writer A M ε _·_ isMON) M ε _·_ isMON}{Writer A M ε _·_ isMON}{M}{ε}{_·_}{isMON} (multW {A}{M}{ε}{_·_}{isMON}) x)
Writer-multlaw {A}{M}{ε}{_·_}{isMON} (m , (n , (p , a))) = cong₂ _,_ (IsMonoid.assoc isMON m n p) refl

-- the unit is a natural transformation:
nattrans-unitW : {A B M : Set} → {ε : M} → {_·_ : M → M → M} → {isMON : IsMonoid M ε _·_} → ∀(f : A → B) → ∀(a : A) →
                                           mapW {A}{B}{M}{ε}{_·_}{isMON} f (unitW {A}{M}{ε}{_·_}{isMON} a) ≡ unitW {B}{M}{ε}{_·_}{isMON} (f a)
nattrans-unitW h a = refl

-- the multiplication is a natural transformation:
nattrans-multW : {A B M : Set} → {ε : M} → {_·_ : M → M → M} → {isMON : IsMonoid M ε _·_} → ∀(f : A → B) → ∀(x : Writer (Writer A M ε _·_ isMON) M ε _·_ isMON) →
                                           mapW {A}{B}{M}{ε}{_·_}{isMON} f (multW {A}{M}{ε}{_·_}{isMON} x) ≡
                                           multW {B}{M}{ε}{_·_}{isMON} (mapW {Writer A M ε _·_ isMON}{Writer B M ε _·_ isMON }{M}{ε}{_·_}{isMON} (mapW {A}{B}{M}{ε}{_·_}{isMON} f) x)
nattrans-multW f (m , (n , a)) = refl


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
-- Composing Writer and Delay via a distributive law --
--***************************************************--

-- The most logical composition of the two monads is to form the monad Delday (Writer A),
-- where first some computations are carried out by Delay and then the result is written by Writer.
DcW : (A M : Set) → (ε : M) → (_·_ : M → M → M) → (isMON : IsMonoid M ε _·_) → (κ : Cl) → Set
DcW A M ε _·_ isMON κ = (Delay (M × A) κ)

-- the unit of this monad is simply the composit of the units for Delay (nowD) and Writer (unitW)
unitDcW : {A M : Set} {ε : M} {_·_ : M → M → M} {isMON : IsMonoid M ε _·_} {κ : Cl} → A → (DcW A M ε _·_ isMON κ) 
unitDcW {A}{M}{ε}{_·_}{isMON} a = nowD (unitW {A}{M}{ε}{_·_}{isMON} a)

-- DcW is a monad via a distributive law, distributing Delay over Writer.
-- Here is the distributive law:
distlawDcW : {A M : Set} {ε : M} {_·_ : M → M → M} {isMON : IsMonoid M ε _·_} {κ : Cl} → Writer (Delay A κ) M ε _·_ isMON  → (DcW A M ε _·_ isMON κ)
distlawDcW {A}{M}{ε}{_·_}{isMON} (m , nowD a) = nowD (m ,  a)
distlawDcW {A}{M}{ε}{_·_}{isMON} (m , stepD x) = stepD (λ α → distlawDcW {A}{M}{ε}{_·_}{isMON} (m , (x α))) 

--proof that distlawRcD is indeed a distributive law:
--unit laws:
unitlawDcW1 : {A M : Set} {ε : M} {_·_ : M → M → M} {isMON : IsMonoid M ε _·_} {κ : Cl} → ∀(x : Delay A κ) → (distlawDcW {A}{M}{ε}{_·_}{isMON} (unitW {Delay A κ}{M}{ε}{_·_}{isMON} x)) ≡
                                                                                                               mapD κ (unitW {A}{M}{ε}{_·_}{isMON}) x
unitlawDcW1 (nowD a) = refl
unitlawDcW1 {A}{M}{ε}{_·_}{isMON}{κ} (stepD x) = cong stepD (later-ext (λ α → unitlawDcW1 (x α))) 


unitlawDcW2 : {A M : Set} {ε : M} {_·_ : M → M → M} {isMON : IsMonoid M ε _·_} {κ : Cl} → ∀(a : A) → ∀(m : M) →
                                  (distlawDcW {A}{M}{ε}{_·_}{isMON}{κ} (mapW {A}{Delay A κ}{M}{ε}{_·_}{isMON} nowD (m , a))) ≡ nowD (m , a)
unitlawDcW2 a m = refl

--multiplication laws:
multlawDcW1 : {A M : Set} {ε : M} {_·_ : M → M → M} {isMON : IsMonoid M ε _·_} {κ : Cl} → ∀(x : Writer (Writer (Delay A κ) M ε _·_ isMON) M ε _·_ isMON) →
                                     distlawDcW {A}{M}{ε}{_·_}{isMON}{κ} (multW {Delay A κ}{M}{ε}{_·_}{isMON} x) ≡
                                     mapD κ (multW {A}{M}{ε}{_·_}{isMON}) (distlawDcW {Writer A M ε _·_ isMON}{M}{ε}{_·_}{isMON}{κ}
                                      (mapW {Writer (Delay A κ) M ε _·_ isMON}{DcW  A M ε _·_ isMON κ}{M}{ε}{_·_}{isMON} (distlawDcW {A}{M}{ε}{_·_}{isMON}{κ}) x))
multlawDcW1 (m , (n , nowD a)) = refl
multlawDcW1 (m , (n , stepD x)) = cong stepD (later-ext(λ α → multlawDcW1 ((m , (n , (x α)))) ))


multlawDcW2 : {A M : Set} {ε : M} {_·_ : M → M → M} {isMON : IsMonoid M ε _·_} {κ : Cl} → ∀(x : Writer (Delay (Delay A κ) κ) M ε _·_ isMON) →
                                       distlawDcW {A}{M}{ε}{_·_}{isMON}{κ} (mapW {Delay (Delay A κ) κ}{Delay A κ}{M}{ε}{_·_}{isMON} (MultD κ) x)
                                       ≡ MultD κ (mapD κ (distlawDcW {A}{M}{ε}{_·_}{isMON}{κ}) (distlawDcW {Delay A κ}{M}{ε}{_·_}{isMON}{κ} x))
multlawDcW2 (m , nowD x) = refl
multlawDcW2 (m , stepD x) = cong stepD (later-ext(λ α → multlawDcW2 ((m , x α))))

-- this yields a multiplication for DcW:
multDcW : {A M : Set} {ε : M} {_·_ : M → M → M} {isMON : IsMonoid M ε _·_} {κ : Cl} → (DcW (DcW A M ε _·_ isMON κ) M ε _·_ isMON κ) → (DcW A M ε _·_ isMON κ)
multDcW {A}{M}{ε}{_·_}{isMON}{κ} X = mapD κ (multW {A}{M}{ε}{_·_}{isMON}) ((MultD κ) (mapD κ (distlawDcW {Writer A M ε _·_ isMON}{M}{ε}{_·_}{isMON}{κ}) X))


--*************************************************--
-- Combination of State and Delay via Yang-Baxter? --
--*************************************************--

-- Recall the Reader monad and the State monad:

Reader : Set → Set → Set
Reader S A = S → A

unitR : {A S : Set} → A → Reader S A
unitR a = λ s → a

multR : {A S : Set} → Reader S (Reader S A) → Reader S A
multR f = λ s → f s s

mapR : {A B S : Set} → (A → B) → Reader S A → Reader S B
mapR h f = λ s → h (f s)

State : (A S : Set) → (ε : S) → (_·_ : S → S → S) → (IsMonoid S ε _·_) → Set
State A S ε _·_ isMON = S → (S × A)

unitS : {A S : Set} {ε : S} {_·_ : S → S → S} {isMON : IsMonoid S ε _·_} → A → State A S ε _·_ isMON
unitS a = λ s → (s , a)

multS : {A S : Set} {ε : S} {_·_ : S → S → S} {isMON : IsMonoid S ε _·_} → State (State A S ε _·_ isMON) S ε _·_ isMON → State A S ε _·_ isMON
multS f = λ s → (proj₂ (f s)) (proj₁(f s))

mapS : {A B S : Set} {ε : S} {_·_ : S → S → S} {isMON : IsMonoid S ε _·_} → (A → B) → State A S ε _·_ isMON → State B S ε _·_ isMON
mapS h f = λ s → ((proj₁ (f s)) , h (proj₂ (f s)))


--There is a distributive law distributing the Writer over the Reader monad,
-- but even though it yields a monad on the State functor,
-- it is not the same monad as the state monad.

distlawRcW : {A S : Set} {ε : S} {_·_ : S → S → S} {isMON : IsMonoid S ε _·_} → Writer (Reader S A) S ε _·_ isMON → State A S ε _·_ isMON
distlawRcW (s , f) = λ t → (s , f t)

--proof that distlawRcW is indeed a distributive law:
--unit laws:
unitlawRcW1 : {A S : Set} {ε : S} {_·_ : S → S → S} {isMON : IsMonoid S ε _·_} → ∀(f : Reader S A) →
                                                    (distlawRcW {A}{S}{ε}{_·_}{isMON} (unitW {Reader S A}{S}{ε}{_·_}{isMON} f)) ≡
                                                     mapR (unitW {A}{S}{ε}{_·_}{isMON}) f
unitlawRcW1 f = refl

unitlawRcW2 : {A S : Set} {ε : S} {_·_ : S → S → S} {isMON : IsMonoid S ε _·_} → ∀(x : Writer A S ε _·_ isMON) →
                                                    (distlawRcW {A}{S}{ε}{_·_}{isMON} (mapW {A}{Reader S A}{S}{ε}{_·_}{isMON} unitR x)) ≡ unitR x
unitlawRcW2 (m , a) = refl

--multiplication laws:
multlawRcW1 : {A S : Set} {ε : S} {_·_ : S → S → S} {isMON : IsMonoid S ε _·_} → ∀(x : Writer (Writer (Reader S A) S ε _·_ isMON) S ε _·_ isMON) →
                                     distlawRcW {A}{S}{ε}{_·_}{isMON} (multW {Reader S A}{S}{ε}{_·_}{isMON} x) ≡
                                     mapR (multW {A}{S}{ε}{_·_}{isMON}) (distlawRcW {Writer A S ε _·_ isMON}{S}{ε}{_·_}{isMON}
                                      (mapW {Writer (Reader S A) S ε _·_ isMON}{State A S ε _·_ isMON}{S}{ε}{_·_}{isMON} (distlawRcW {A}{S}{ε}{_·_}{isMON}) x))
multlawRcW1 (m , (n , f)) = refl

multlawRcW2 : {A S : Set} {ε : S} {_·_ : S → S → S} {isMON : IsMonoid S ε _·_} → ∀(x : Writer (Reader S (Reader S A)) S ε _·_ isMON) →
                                       distlawRcW {A}{S}{ε}{_·_}{isMON} (mapW {Reader S (Reader S A)}{Reader S A}{S}{ε}{_·_}{isMON} multR x)
                                       ≡ multR (mapR (distlawRcW {A}{S}{ε}{_·_}{isMON}) (distlawRcW {Reader S A}{S}{ε}{_·_}{isMON} x))
multlawRcW2 (m , ff) = refl

--proof that distlawRcW does not yield the state monad: 

-- the unit of this monad is simply the composit of the units for Reader (unitR) and Writer (unitW)
unitRcW : {A S : Set} {ε : S} {_·_ : S → S → S} {isMON : IsMonoid S ε _·_} → A → (State A S ε _·_ isMON) 
unitRcW {A}{S}{ε}{_·_}{isMON} a = unitR (unitW {A}{S}{ε}{_·_}{isMON} a)

-- However, this is not the same as the unit for the state monad, unitS.
-- unitR (unitW a) = λ s → (ε , a), whereas
-- unitS = λ s → (s , a)

-- the multiplication for RcW is given by:
multRcW : {A S : Set} {ε : S} {_·_ : S → S → S} {isMON : IsMonoid S ε _·_} → (State (State A S ε _·_ isMON) S ε _·_ isMON) → (State A S ε _·_ isMON)
multRcW {A}{S}{ε}{_·_}{isMON} X = mapR (multW {A}{S}{ε}{_·_}{isMON}) (multR (mapR (distlawRcW {Writer A S ε _·_ isMON}{S}{ε}{_·_}{isMON}) X))

-- I do not know if this is equal to the multiplication of the state monad:
correctMult : {A S : Set} {ε : S} {_·_ : S → S → S} {isMON : IsMonoid S ε _·_} → ∀(X : (State (State A S ε _·_ isMON) S ε _·_ isMON))
                                                                               → multRcW {A}{S}{ε}{_·_}{isMON} X ≡ multS {A}{S}{ε}{_·_}{isMON} X
correctMult X = funExt (λ s → {!!})


-- It was my hope to recover the combation of State and Delay descibed in another document via the three distributive laws
-- Writer over Reader
-- Writer over Delay
-- Delay over Reader

-- Since Writer over Reader does not yield the State monad, this is no longer possible.
-- But we can still check if the three distributive laws given here statisfy Yang Baxter,
-- And therefore define an iterated distributive law resulting in the monad Reader(Delay(Writer A))

-- Recall the distributive law for Delay over Reader:
distlawRcD : {A S : Set} {κ : Cl} → Delay (Reader S A) κ → (Reader S (Delay A κ))
distlawRcD (nowD f) = λ s → nowD (f s)
distlawRcD (stepD x) = λ s → stepD (λ α → distlawRcD (x α) s)

-- Then, the Yang-Baxter equation is as follows:

YB-RDW :  {A S : Set} {ε : S} {_·_ : S → S → S} {isMON : IsMonoid S ε _·_} {κ : Cl} → ∀(x : Writer (Delay (Reader S A) κ) S ε _·_ isMON) →
       distlawRcD {Writer A S ε _·_ isMON}{S}{κ} (mapD κ (distlawRcW {A}{S}{ε}{_·_}{isMON}) (distlawDcW {Reader S A}{S}{ε}{_·_}{isMON}{κ} x)) ≡
       mapR (distlawDcW {A}{S}{ε}{_·_}{isMON}{κ}) (distlawRcW {Delay A κ}{S}{ε}{_·_}{isMON} (mapW {Delay (Reader S A) κ}{Reader S (Delay A κ)}{S}{ε}{_·_}{isMON} (distlawRcD {A}{S}{κ}) x))
YB-RDW (m , nowD x) = refl
YB-RDW {A}{S}{ε}{_·_}{isMON}{κ} (m , stepD x) = λ i → λ s → stepD (λ α → YB-RDW {A}{S}{ε}{_·_}{isMON}{κ} (m , x α) i s)

