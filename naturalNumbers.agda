module naturalNumbers where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

Rel : Set → Set1
Rel A = A → A → Set0

Op₁ : Set → Set
Op₁ A = A → A

Op₂ : Set → Set
Op₂ A = A → A → A

-- evenness stuff

data even : Nat → Set where
    ZERO : even 0
    STEP : (x : Nat) → even x → even (suc (suc x))

x2Even : (x : Nat) → even (x * 2) 
x2Even 0 = ZERO
x2Even (suc n) = STEP (n * 2) (x2Even n)

-- Equality in Nat

data _='_ : Rel Nat where
    ZERO : 0 =' 0
    STEP : (m n : Nat) → m =' n → (suc m) =' (suc n) 

-- Relation Properties

Reflexive : {A : Set} → Rel A → Set
Reflexive {A} rel = ∀ {a : A} → rel a a

Symmetric : {A : Set} → Rel A → Set
Symmetric {A} rel = {a b : A} → rel a b → rel b a

Transitive : {A : Set} → Rel A → Set
Transitive {A} rel = {a b c : A} → rel a b → rel b c → rel a c

Antisymmetric : {A : Set} → Rel A → Rel A → Set
Antisymmetric {A} _≡_ _≦_ = {a b : A} → a ≦ b → b ≦ a → a ≡ b

-- Operation Properties

Commutes : {A : Set} → Rel A → Op₂ A → Set
Commutes {A} _≡_ _⊕_ = {a b : A} → (a ⊕ b) ≡ (b ⊕ a)

Associative : {A : Set} → Rel A → Op₂ A → Set
Associative {A} _≡_ _o_ = {a b c : A} → ((a o b) o c) ≡ (a o (b o c))

-- Proofs about equality

equalsRefl : Reflexive _='_ 
equalsRefl {0} = ZERO 
equalsRefl {suc n} = STEP n n equalsRefl

equalsSym : Symmetric _='_
equalsSym ZERO = ZERO
equalsSym (STEP m n p) = STEP n m (equalsSym p)

equalsTrans : Transitive _='_
equalsTrans ZERO ZERO = ZERO
equalsTrans (STEP n m p) (STEP a b q) = STEP n b (equalsTrans p q)

-- Proofs about Addition
addLeftSucFactor : (m n : Nat) → ((suc m) + n) =' suc (m + n)
addLeftSucFactor m n = equalsRefl

addRightSucFactor : (m n : Nat) → (m + (suc n)) =' suc (m + n)
addRightSucFactor 0 0 = STEP zero zero ZERO
addRightSucFactor 0 (suc n) = STEP (suc n) (suc n) (addRightSucFactor zero n)
addRightSucFactor (suc m) n = STEP (m + suc n) (suc (m + n)) (addRightSucFactor m n)

addCommutes : Commutes _='_ _+_
addCommutes {0} {0} = ZERO
addCommutes {0} {suc n} = STEP n (n + zero) (addCommutes {0} {n})
addCommutes {suc m} {n} = equalsTrans (STEP (m + n) (n + m) (addCommutes {m} {n})) (equalsSym (addRightSucFactor n m))

addPreservesEqR : (n a b : Nat) → a =' b → (n + a) =' (n + b)
addPreservesEqR 0 a b ZERO = ZERO
addPreservesEqR (suc n) a b ZERO = STEP (n + zero) (n + zero) (addPreservesEqR n zero zero ZERO)
addPreservesEqR 0 a b (STEP c d p) = STEP c d p
addPreservesEqR (suc n) a b (STEP c d p) = STEP (n + suc c) (n + suc d) (addPreservesEqR n (suc c) (suc d) (STEP c d p))

addPreservesEq : {n m a b : Nat} → n =' m → a =' b → (n + a) =' (m + b)
addPreservesEq ZERO ZERO = ZERO
addPreservesEq (STEP x y p) ZERO = STEP (x + zero) (y + zero) (addPreservesEq p ZERO)
addPreservesEq ZERO (STEP c d q) = STEP c d q
addPreservesEq (STEP x y p) (STEP c d q) = STEP (x + suc c) (y + suc d) (addPreservesEq p (STEP c d q))

-- Proofs about Multiplication
multPreservesEqR : (n a b : Nat) → a =' b → (n * a) =' (n * b) 
multPreservesEqR 0 a b ZERO = ZERO
multPreservesEqR (suc n) a b ZERO = multPreservesEqR n zero zero ZERO
multPreservesEqR 0 a b (STEP c d p) = ZERO
multPreservesEqR (suc n) a b (STEP c d p) = {!  !}

multPreservesEqL : (n a b : Nat) → a =' b → (a * n) =' (b * n) 
multPreservesEqL n a b ZERO = ZERO
multPreservesEqL 0 a b (STEP c d p) = multPreservesEqL zero c d p
multPreservesEqL (suc n) a b (STEP c d p) = {!   !}

multPreservesEq : {n m a b : Nat} → m =' n → a =' b → (m * a) =' (n * b)
multPreservesEq ZERO q = ZERO
multPreservesEq (STEP x y p) ZERO = multPreservesEq p ZERO
multPreservesEq (STEP x y p) (STEP c d q) = {!   !} 

n0is0 : (n : Nat) → (n * 0) =' 0
n0is0 0 = ZERO
n0is0 (suc n) = n0is0 n

multRightAddFactor : (m n : Nat) → (m * (suc n)) =' ((m * n) + m)
multRightAddFactor 0 n = ZERO
multRightAddFactor (suc m) n = equalsTrans {!   !} {!   !}