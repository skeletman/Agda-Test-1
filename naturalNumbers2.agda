module naturalNumbers2 where

-- open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

data _∧_ (A B : Set) : Set where
  <_,_> : A → B → A ∧ B

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)

_*_ : Nat → Nat → Nat
zero  * m = zero
suc n * m = (n * m) + m

Rel : Set → Set1
Rel A = A → A → Set0

Op₁ : Set → Set
Op₁ A = A → A

Op₂ : Set → Set
Op₂ A = A → A → A

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

IdentityL : {A : Set} → Rel A → Op₂ A → A → Set
IdentityL {A} _≡_ _⊕_ e = {a : A} → (e ⊕ a) ≡ a 

IdentityR : {A : Set} → Rel A → Op₂ A → A → Set
IdentityR {A} _≡_ _⊕_ e = {a : A} → (a ⊕ e) ≡ a 

Identity : {A : Set} → Rel A → Op₂ A → A → Set 
Identity eq m e = (IdentityL eq m e) ∧ (IdentityR eq m e)

Commutes : {A : Set} → Rel A → Op₂ A → Set
Commutes {A} _≡_ _⊕_ = {a b : A} → (a ⊕ b) ≡ (b ⊕ a)

Associative : {A : Set} → Rel A → Op₂ A → Set
Associative {A} _≡_ _o_ = {a b c : A} → ((a o b) o c) ≡ (a o (b o c))

DistributesL : {A : Set} → Rel A → Op₂ A → Op₂ A → Set
DistributesL {A} _≡_ _⊗_ _⊕_ = {a b c : A} → (a ⊗ (b ⊕ c)) ≡ ((a ⊗ b) ⊕ (a ⊗ c))

DistributesR : {A : Set} → Rel A → Op₂ A → Op₂ A → Set
DistributesR {A} _≡_ _⊗_ _⊕_ = {a b c : A} → ((a ⊕ b) ⊗ c) ≡ ((a ⊗ c) ⊕ (b ⊗ c))

-- Proofs about ≡

congruence : {A B : Set} → (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
congruence f refl = refl

app-congruence : {A B : Set} → {f g : A → B} → f ≡ g → (x : A) → f x ≡ f x
app-congruence refl x = refl 

substitution : {A : Set} → {x y : A} → (P : A → Set) → x ≡ y → P x → P y
substitution P refl px = px

sym : {A : Set} → Symmetric {A} _≡_
sym refl = refl

trans : {A : Set} → Transitive {A} _≡_
trans refl refl = refl

-- Proofs about ='

equalsRefl : Reflexive _='_ 
equalsRefl {0} = ZERO 
equalsRefl {suc n} = STEP n n equalsRefl

equalsSym : Symmetric _='_
equalsSym ZERO = ZERO
equalsSym (STEP m n p) = STEP n m (equalsSym p)

equalsTrans : Transitive _='_
equalsTrans ZERO ZERO = ZERO
equalsTrans (STEP n m p) (STEP a b q) = STEP n b (equalsTrans p q)

equalsImpliesEqq : {a b : Nat} → a ≡ b → a =' b
equalsImpliesEqq refl = equalsRefl

eqqImpliesEquals : {a b : Nat} → a =' b → a ≡ b
eqqImpliesEquals ZERO = refl
eqqImpliesEquals (STEP n m p) = congruence suc (eqqImpliesEquals p)

-- Proofs about Addition

addRightSucFactor : (m n : Nat) → m + (suc n) ≡ suc (m + n)
addRightSucFactor 0 0 = refl
addRightSucFactor 0 (suc n) = congruence suc refl
addRightSucFactor (suc m) n = congruence suc (addRightSucFactor m n)

addCommutes : Commutes _≡_ _+_ 
addCommutes {0} {0} = refl
addCommutes {0} {suc n} = congruence suc (addCommutes {0} {n}) 
addCommutes {suc m} {n} = trans {Nat} (congruence suc (addCommutes {m} {n})) (sym (addRightSucFactor n m)) 

addAssoc : Associative _≡_ _+_
addAssoc {0} {m} {n} = refl
addAssoc {suc l} {m} {n} = congruence suc (addAssoc {l} {m} {n})

addIdentity : Identity _≡_ _+_ 0
addIdentity = < (λ {a} → refl) , (λ {a} → addCommutes {a} {zero}) >
-- Proofs about Mult

multRightSucFactor : (m n : Nat) → m * (suc n) ≡ (m * n) + m
multRightSucFactor 0 n = refl
multRightSucFactor (suc m) n = trans (congruence (λ x → x + suc n) (multRightSucFactor m n)) (trans (addAssoc {m * n} {m} {suc n}) (trans (congruence (λ x → (m * n) + x) (trans (addRightSucFactor m n) ( addCommutes {suc m} {n} ))) (sym (addAssoc {m * n} {n} {suc m}))))

multCommutes : Commutes _≡_ _*_
multCommutes {0} {0} = refl
multCommutes {suc m} {0} = trans (addCommutes {m * 0} {0}) (multCommutes {m} {0})
multCommutes {m} {suc n} = trans (multRightSucFactor m n) (congruence (λ x → x + m) (multCommutes {m} {n}))

multDistOverAddL : DistributesL _≡_ _*_ _+_
multDistOverAddL {0} {m} {n} = refl
multDistOverAddL {suc l} {m} {n} = trans (congruence (λ x → x + (m + n)) {l * (m + n)} {(l * m) + (l * n)} (multDistOverAddL {l} {m} {n})) (trans (trans (trans (trans (trans (addAssoc {l * m} {l * n} {m + n}) (sym (congruence (λ x → (l * m) + x) {((l * n) + m) + n} {(l * n) + (m + n)} (addAssoc {l * n} {m} {n})))) (sym (addAssoc {l * m} {(l * n) + m} {n}))) (sym (congruence (λ x → ((l * m) + x) + n) {m + (l * n)} {(l * n) + m} (addCommutes {m} {l * n})))) (sym ((congruence (λ x → x + n) {((l * m) + m) + (l * n)} {(l * m) + (m + (l * n))} (addAssoc {l * m} {m} {l * n}))))) (addAssoc {(l * m) + m} {l * n} {n}))

multDistOverAddR : DistributesR _≡_ _*_ _+_
multDistOverAddR {l} {m} {n} = trans (multCommutes {l + m} {n}) (trans (trans (multDistOverAddL {n} {l} {m}) (sym (congruence (λ x → (n * l) + x) {m * n} {n * m} (multCommutes {m} {n})))) (sym (congruence (λ x → x + (m * n)) {l * n} {n * l} (multCommutes {l} {n}))))

multAssoc : Associative _≡_ _*_
multAssoc {0} {m} {n} = refl
multAssoc {suc l} {m} {n} = trans (multDistOverAddR {l * m} {m} {n}) (congruence (λ x → x + (m * n)) {(l * m) * n} {l * (m * n)} (multAssoc {l} {m} {n}))

multIdentity : Identity _≡_ _*_ 1
multIdentity = < (λ {a} → refl) , (λ {a} → multCommutes {a} {1}) >