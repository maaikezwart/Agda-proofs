{-# OPTIONS --cubical --guarded --rewriting -W ignore #-}

import Agda.Builtin.Equality as R
import Agda.Builtin.Equality.Rewrite as R

open import Agda.Primitive
open import Clocked.Primitives
open import Cubical.Foundations.Prelude hiding (Lift)
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.ListedFiniteSet
open import Cubical.Foundations.HLevels
open import Cubical.HITs.Rationals.QuoQ as ℚ
open import Cubical.Data.Nat as ℕ using (discreteℕ) renaming (_+_ to _+ℕ_)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Int.MoreInts.QuoInt
  renaming (_·_ to _·ℤ_; _+_ to _+ℤ_; -_ to -ℤ_)

-- Some rational constants
1ℚ : ℚ
1ℚ = [ pos 1 , 1 ]

0ℚ : ℚ
0ℚ = [ pos 0 , 1 ]

½ : ℚ
½ = [ pos 1 , 2 ]

¼ : ℚ
¼ = [ pos 1 , 4 ]

¼≡½·½ : ¼ ≡ ½ · ½
¼≡½·½ = refl

-invol : ∀ x y → x - (x - y) ≡ y
-invol x y = 
  x - (x - y)
    ≡⟨ (λ i → x + ℚ.·-distribˡ -1 x (- y) (~ i)) ⟩
  x + ((- x) - (- y))
    ≡⟨ ℚ.+-assoc x (- x) (- (- y)) ⟩
  (x - x) + - (- y)
    ≡⟨ (λ i → ℚ.+-inverseʳ x i + ℚ.negate-invol y i) ⟩
  0ℚ + y
    ≡⟨ ℚ.+-identityˡ y ⟩
  y
    ∎

-- The line between x and y at time p
line : (x y : ℚ) (q : ℚ) → ℚ
line x y q = q · x + (1ℚ - q) · y

-- Some basic properties of lines
line-idem : ∀ x q → line x x q ≡ x
line-idem x q =
  q · x + (1ℚ - q) · x
   ≡⟨ ℚ.·-distribʳ q (1ℚ - q) x ⟩
  (q + (1ℚ - q)) · x
   ≡⟨ (λ i → (q + ℚ.+-comm 1ℚ (- q) i) · x) ⟩
  (q + (- q + 1ℚ)) · x
   ≡⟨ (λ i → ℚ.+-assoc q (- q) 1ℚ i · x) ⟩           
  (q - q + 1ℚ) · x
   ≡⟨ (λ i → (ℚ.+-inverseʳ q i + 1ℚ) · x) ⟩           
  (0ℚ + 1ℚ) · x
   ≡⟨ (λ i → +-identityˡ 1ℚ i · x) ⟩           
  1ℚ · x
   ≡⟨ ℚ.·-identityˡ x ⟩
  x
    ∎

line-comm : ∀ x y q → line x y q ≡ line y x (1ℚ - q)
line-comm x y q = 
  q · x + (1ℚ - q) · y
    ≡⟨ ℚ.+-comm (q · x) ((1ℚ - q) · y) ⟩
  (1ℚ - q) · y + q · x
    ≡⟨ (λ i → (1ℚ - q) · y + -invol 1ℚ q (~ i) · x) ⟩
  (1ℚ - q) · y + (1ℚ - (1ℚ - q)) · x
    ∎

line-assoc : ∀ x y z p q r
  → r · (1ℚ - (p · q)) ≡ q · (1ℚ - p)
  → line (line x y p) z q ≡ line x (line y z r) (p · q)
line-assoc x y z p q r eq = 
  q · (p · x + (1ℚ - p) · y) + (1ℚ - q) · z
    ≡⟨ (λ i → ℚ.·-distribˡ q (p · x) ((1ℚ - p) · y) (~ i) + ℚ.·-distribʳ 1ℚ (- q) z (~ i)) ⟩ 
  q · (p · x) + q · ((1ℚ - p) · y) + (1ℚ · z + - q · z)
    ≡⟨ sym (ℚ.+-assoc (q · (p · x)) (q · ((1ℚ - p) · y)) (1ℚ · z + - q · z))  ⟩ 
  q · (p · x) + (q · ((1ℚ - p) · y) + (1ℚ · z + - q · z))
    ≡⟨ cong (q · (p · x) +_) lem ⟩ 
  q · (p · x) + ((r · (1ℚ - (p · q)) · y) + ((1ℚ - r) · (1ℚ - (p · q)) · z))
    ≡⟨ (λ i → ℚ.·-assoc q p x i
              +
              ((cong (_· y) (ℚ.·-comm r (1ℚ - (p · q))) ∙ sym (ℚ.·-assoc (1ℚ - (p · q)) r y)) i
               +
               (cong (_· z) (ℚ.·-comm (1ℚ - r) (1ℚ - (p · q)))
                 ∙ sym (ℚ.·-assoc (1ℚ - (p · q)) (1ℚ - r) z)) i)) ⟩ 
  q · p · x + ((1ℚ - (p · q)) · (r · y) + (1ℚ - (p · q)) · ((1ℚ - r) · z))
    ≡⟨ (λ i → ℚ.·-comm q p i · x + ℚ.·-distribˡ (1ℚ - (p · q)) (r · y) ((1ℚ - r) · z) i) ⟩ 
  p · q · x + (1ℚ - (p · q)) · (r · y + (1ℚ - r) · z)
    ∎
  where
    lem'' =
      (- (p · q)) + q
        ≡⟨ ℚ.+-comm (- (p · q)) q ⟩ 
      q + (- (p · q))
        ≡⟨ cong (q +_) (ℚ.·-assoc -1 p q) ⟩ 
      q + (- p · q)
        ≡⟨ cong (q +_) (ℚ.·-comm (- p) q) ⟩ 
      q + q · - p
        ≡⟨ cong (λ x → x + q · - p) (sym (ℚ.·-identityʳ q)) ⟩ 
      q · 1ℚ + q · - p
        ∎
  
    lem' = 
      1ℚ - q
        ≡⟨ cong (1ℚ +_) (sym (ℚ.+-identityˡ (- q))) ⟩ 
      1ℚ + (0ℚ + - q)
        ≡⟨ cong (λ x → 1ℚ + (x + - q)) (sym (+-inverseʳ (- (q · p)))) ⟩ 
      1ℚ + (- (q · p) + (- - (q · p)) + - q)
        ≡⟨ cong (1ℚ +_) (sym (ℚ.+-assoc (- (q · p)) (- - (q · p)) (- q))) ⟩ 
      1ℚ + ((- (q · p)) + ((- (- (q · p))) + (- q)))
        ≡⟨ cong (λ x → 1ℚ + (- (q · p) + x)) (ℚ.·-distribˡ -1 (- (q · p)) q) ⟩ 
      1ℚ + (- (q · p) + - (- (q · p) + q))
        ≡⟨ ℚ.+-assoc 1ℚ (- (q · p)) (- (- (q · p) + q)) ⟩ 
      (1ℚ - (q · p)) - (- (q · p) + q)
        ≡⟨ cong₂ (λ x y → (1ℚ - x) - y) (ℚ.·-comm q p) (cong (λ x → - x + q) (ℚ.·-comm q p)) ⟩ 
      (1ℚ - (p · q)) - (- (p · q) + q)
        ≡⟨ cong (λ x → (1ℚ - (p · q)) - x) lem'' ⟩ 
      (1ℚ - (p · q)) - (q · 1ℚ + q · - p)
        ∎
      
    lem =
      q · ((1ℚ - p) · y) + (1ℚ · z + (- q) · z)
        ≡⟨ cong (q · ((1ℚ - p) · y) +_) (ℚ.·-distribʳ 1ℚ (- q) z) ⟩ 
      q · ((1ℚ - p) · y) + (1ℚ - q) · z
        ≡⟨ cong (q · ((1ℚ - p) · y) +_) (cong (_· z) lem') ⟩ 
      q · ((1ℚ - p) · y) + ((1ℚ - (p · q)) - (q · 1ℚ + q · - p)) · z
        ≡⟨ (λ i → ℚ.·-assoc q (1ℚ - p) y i
                    + (ℚ.·-identityˡ (1ℚ - (p · q)) (~ i) - ℚ.·-distribˡ q 1ℚ (- p) i) · z) ⟩ 
      q · (1ℚ - p) · y + ((1ℚ · (1ℚ - (p · q))) - (q · (1ℚ - p))) · z
        ≡⟨ (λ i → eq (~ i) · y + ((1ℚ · (1ℚ - (p · q))) - eq (~ i)) · z) ⟩ 
      r · (1ℚ - (p · q)) · y + ((1ℚ · (1ℚ - (p · q))) - (r · (1ℚ - (p · q)))) · z
        ≡⟨ cong (r · (1ℚ - (p · q)) · y +_)
                (λ i → (1ℚ · (1ℚ - (p · q)) + ℚ.·-assoc -1 r (1ℚ - (p · q)) i) · z) ⟩ 
      r · (1ℚ - (p · q)) · y + (1ℚ · (1ℚ - (p · q)) + - r · (1ℚ - (p · q))) · z
        ≡⟨ cong (r · (1ℚ - (p · q)) · y +_) (λ i → ℚ.·-distribʳ 1ℚ (- r) (1ℚ - (p · q)) i · z) ⟩ 
      r · (1ℚ - (p · q)) · y + (1ℚ - r) · (1ℚ - (p · q)) · z
        ∎
