module leftGroup where

Rel : Set → Set1
Rel A = A → A → Set0

Op₁ : Set → Set
Op₁ A = A → A

Op₂ : Set → Set
Op₂ A = A → A → A

Reflexive : {A : Set} → Rel A → Set
Reflexive {A} rel = ∀ {a : A} → rel a a

Symmetric : {A : Set} → Rel A → Set
Symmetric {A} rel = {a b : A} → rel a b → rel b a

Transitive : {A : Set} → Rel A → Set
Transitive {A} rel = {a b c : A} → rel a b → rel b c → rel a c

Antisymmetric : {A : Set} → Rel A → Rel A → Set
Antisymmetric {A} _≡_ _≦_ = {a b : A} → a ≦ b → b ≦ a → a ≡ b

Associative : {A : Set} → Rel A → Op₂ A → Set
Associative {A} _≡_ _o_ = {a b c : A} → ((a o b) o c) ≡ (a o (b o c))

IdentityL : {A : Set} → Rel A → Op₂ A → A → Set
IdentityL {A} _≡_ _+_ ε = {a : A} → (ε + a) ≡ a

IdentityR : {A : Set} → Rel A → Op₂ A → A → Set
IdentityR {A} _≡_ _+_ ε = {a : A} → (a + ε) ≡ a

InverseR : {A : Set} → Rel A → Op₂ A → Op₁ A → A → Set
InverseR {A} _≡_ _+_ i ε = {a : A} → (a + i a) ≡ ε

InverseL : {A : Set} → Rel A → Op₂ A → Op₁ A → A → Set
InverseL {A} _≡_ _+_ i ε = {a : A} → (i a + a) ≡ ε

Application₂ : {A : Set} → Rel A → Op₂ A → Set
Application₂ {A} eq m = {a b c d : A} → eq a c → eq b d → eq (m a b) (m c d)

Application₁ : {A : Set} → Rel A → Op₁ A → Set
Application₁ {A} eq f = {a b : A} → eq a b → eq (f a) (f b)

record IsEquivalence {A : Set} (_≡_ : Rel A) : Set where
  field
    reflexive  : Reflexive  _≡_
    symmetric  : Symmetric  _≡_
    transitive : Transitive _≡_

record IsGroupL {A : Set} (_≡_ : Rel A) (_⊗_ : Op₂ A) (i : A → A) (ε : A) : Set where
  field
    reflexive  : Reflexive  _≡_
    symmetric  : Symmetric  _≡_
    transitive : Transitive _≡_
    appinv : Application₁ _≡_ i
    appmult : Application₂ _≡_ _⊗_
    associative : Associative _≡_ _⊗_
    identityL : IdentityL _≡_ _⊗_ ε
    inverseL : InverseL _≡_ _⊗_ i ε

record IsGroupR {A : Set} (_≡_ : Rel A) (_⊗_ : Op₂ A) (i : A → A) (ε : A) : Set where
  field
    reflexive  : Reflexive  _≡_
    symmetric  : Symmetric  _≡_
    transitive : Transitive _≡_
    appinv : Application₁ _≡_ i
    appmult : Application₂ _≡_ _⊗_
    associative : Associative _≡_ _⊗_
    identityR : IdentityR _≡_ _⊗_ ε
    inverseR : InverseR _≡_ _⊗_ i ε

record IsGroup {A : Set} (_≡_ : Rel A) (_⊗_ : Op₂ A) (i : A → A) (ε : A) : Set where
  field
    reflexive  : Reflexive  _≡_
    symmetric  : Symmetric  _≡_
    transitive : Transitive _≡_
    appinv : Application₁ _≡_ i
    appmult : Application₂ _≡_ _⊗_
    associative : Associative _≡_ _⊗_
    identityL : IdentityL _≡_ _⊗_ ε
    inverseL : InverseL _≡_ _⊗_ i ε
    identityR : IdentityR _≡_ _⊗_ ε
    inverseR : InverseR _≡_ _⊗_ i ε


pf1 : {A : Set} → (_≡_ : Rel A) → (_⊕_ : Op₂ A) → (i : Op₁ A) → (e : A) → IsGroupL _≡_ _⊕_ i e → {a : A} → e ≡ (i (a ⊕ i a) ⊕ (a ⊕ i a))
pf1 {A} _≡_ _⊕_ i e g = IsGroupL.symmetric g (IsGroupL.inverseL g)

pf2 : {A : Set} → (_≡_ : Rel A) → (_⊕_ : Op₂ A) → (i : Op₁ A) → (e : A) → IsGroupL _≡_ _⊕_ i e → {a : A} → (i (a ⊕ i a) ⊕ (a ⊕ i a)) ≡ (i (a ⊕ i a) ⊕ (a ⊕ (e ⊕ i a))) 
pf2 {A} eq m i e g = IsGroupL.symmetric g (IsGroupL.appmult g (IsGroupL.reflexive g) (IsGroupL.appmult g (IsGroupL.reflexive g) (IsGroupL.identityL g)))

pf3 : {A : Set} → (_≡_ : Rel A) → (_⊕_ : Op₂ A) → (i : Op₁ A) → (e : A) → IsGroupL _≡_ _⊕_ i e → {a : A} → (i (a ⊕ i a) ⊕ (a ⊕ (e ⊕ i a))) ≡ (i (a ⊕ i a) ⊕ (a ⊕ ((i a ⊕ a) ⊕ i a)))
pf3 {A} eq m i e g = IsGroupL.symmetric g (IsGroupL.appmult g (IsGroupL.reflexive g) (IsGroupL.appmult g (IsGroupL.reflexive g)
 (IsGroupL.appmult g (IsGroupL.inverseL g) (IsGroupL.reflexive g))))

pf4 : {A : Set} → (_≡_ : Rel A) → (_⊕_ : Op₂ A) → (i : Op₁ A) → (e : A) → IsGroupL _≡_ _⊕_ i e → {a : A} → (i (a ⊕ i a) ⊕ (a ⊕ ((i a ⊕ a) ⊕ i a))) ≡ (i (a ⊕ i a) ⊕ (a ⊕ (i a ⊕ (a ⊕ i a))))
pf4 {A} _≡_ _⊕_ i e g = IsGroupL.appmult g (IsGroupL.reflexive g)
    (IsGroupL.appmult g (IsGroupL.reflexive g)
        (IsGroupL.associative g))

pf5 : {A : Set} → (_≡_ : Rel A) → (_⊕_ : Op₂ A) → (i : Op₁ A) → (e : A) → IsGroupL _≡_ _⊕_ i e → {a : A} → (i (a ⊕ i a) ⊕ (a ⊕ (i a ⊕ (a ⊕ i a)))) ≡ (i (a ⊕ i a) ⊕ ((a ⊕ i a) ⊕ (a ⊕ i a)))
pf5 {A} _≡_ _⊕_ i e g = IsGroupL.symmetric g
 (IsGroupL.appmult g (IsGroupL.reflexive g)
  (IsGroupL.associative g))

pf6 : {A : Set} → (_≡_ : Rel A) → (_⊕_ : Op₂ A) → (i : Op₁ A) → (e : A) → IsGroupL _≡_ _⊕_ i e → {a : A} → (i (a ⊕ i a) ⊕ ((a ⊕ i a) ⊕ (a ⊕ i a))) ≡ ((i (a ⊕ i a) ⊕ (a ⊕ i a)) ⊕ (a ⊕ i a))
pf6 = λ _≡_ _⊕_ i e z → IsGroupL.symmetric z (IsGroupL.associative z)

pf7 : {A : Set} → (_≡_ : Rel A) → (_⊕_ : Op₂ A) → (i : Op₁ A) → (e : A) → IsGroupL _≡_ _⊕_ i e → {a : A} → ((i (a ⊕ i a) ⊕ (a ⊕ i a)) ⊕ (a ⊕ i a)) ≡ (e ⊕ (a ⊕ i a))
pf7 = λ _≡_ _⊕_ i e z →
  IsGroupL.appmult z (IsGroupL.inverseL z) (IsGroupL.reflexive z)

pf8 : {A : Set} → (_≡_ : Rel A) → (_⊕_ : Op₂ A) → (i : Op₁ A) → (e : A) → IsGroupL _≡_ _⊕_ i e → {a : A} → (e ⊕ (a ⊕ i a)) ≡ (a ⊕ i a)
pf8 = λ _≡_ _⊕_ i e z → IsGroupL.identityL z

pf9 : {A : Set} → (_≡_ : Rel A) → (_⊕_ : Op₂ A) → (i : Op₁ A) → (e : A) → IsGroupL _≡_ _⊕_ i e → {a : A} → e ≡ (a ⊕ i a)
pf9 _≡_ _⊕_ i e g = IsGroupL.transitive g (IsGroupL.transitive g (IsGroupL.transitive g (IsGroupL.transitive g (IsGroupL.transitive g (IsGroupL.transitive g (IsGroupL.transitive g (pf1 _≡_ _⊕_ i e g) (pf2 _≡_ _⊕_ i e g)) (pf3 _≡_ _⊕_ i e g)) (pf4 _≡_ _⊕_ i e g)) (pf5 _≡_ _⊕_ i e g)) (pf6 _≡_ _⊕_ i e g)) (pf7 _≡_ _⊕_ i e g)) (pf8 _≡_ _⊕_ i e g)

GrpLImpliesInvR : {A : Set} → (_≡_ : Rel A) → (_⊕_ : Op₂ A) → (i : Op₁ A) → (e : A) → IsGroupL _≡_ _⊕_ i e → InverseR _≡_ _⊕_ i e
GrpLImpliesInvR _≡_ _⊕_ i e g = IsGroupL.symmetric g (pf9 _≡_ _⊕_ i e g)

pf₂1 : {A : Set} → (_≡_ : Rel A) → (_⊕_ : Op₂ A) → (i : Op₁ A) → (e : A) → IsGroupL _≡_ _⊕_ i e → {a : A} → (a ⊕ e) ≡ (a ⊕ (i a ⊕ a))
pf₂1 = λ _≡_ _⊕_ i e z →
  IsGroupL.symmetric z
  (IsGroupL.appmult z (IsGroupL.reflexive z) (IsGroupL.inverseL z))

pf₂2 : {A : Set} → (_≡_ : Rel A) → (_⊕_ : Op₂ A) → (i : Op₁ A) → (e : A) → IsGroupL _≡_ _⊕_ i e → {a : A} → (a ⊕ (i a ⊕ a)) ≡ ((a ⊕ i a) ⊕ a)
pf₂2 = λ _≡_ _⊕_ i e z → IsGroupL.symmetric z (IsGroupL.associative z)

pf₂3 : {A : Set} → (_≡_ : Rel A) → (_⊕_ : Op₂ A) → (i : Op₁ A) → (e : A) → IsGroupL _≡_ _⊕_ i e → {a : A} → ((a ⊕ i a) ⊕ a) ≡ (e ⊕ a)
pf₂3 _≡_ _⊕_ i e g = IsGroupL.appmult g (GrpLImpliesInvR _≡_ _⊕_ i e g) (IsGroupL.reflexive g)

pf₂4 : {A : Set} → (_≡_ : Rel A) → (_⊕_ : Op₂ A) → (i : Op₁ A) → (e : A) → IsGroupL _≡_ _⊕_ i e → {a : A} → (e ⊕ a) ≡ a
pf₂4 = λ _≡_ _⊕_ i e → IsGroupL.identityL

GrpLImpliesIdR : {A : Set} → (_≡_ : Rel A) → (_⊕_ : Op₂ A) → (i : Op₁ A) → (e : A) → IsGroupL _≡_ _⊕_ i e → IdentityR _≡_ _⊕_ e
GrpLImpliesIdR _≡_ _⊕_ i e g = IsGroupL.transitive g (IsGroupL.transitive g (IsGroupL.transitive g (pf₂1 _≡_ _⊕_ i e g) (pf₂2 _≡_ _⊕_ i e g)) (pf₂3 _≡_ _⊕_ i e g)) (pf₂4 _≡_ _⊕_ i e g)

leftGroupImpliesRightGroup : {A : Set} → (_≡_ : Rel A) → (_⊕_ : Op₂ A) → (i : Op₁ A) → (e : A) → IsGroupL _≡_ _⊕_ i e → IsGroupR _≡_ _⊕_ i e
leftGroupImpliesRightGroup _≡_ _⊕_ i e g = record
 { reflexive = IsGroupL.reflexive g
 ; symmetric = IsGroupL.symmetric g
 ; transitive = IsGroupL.transitive g
 ; appinv = IsGroupL.appinv g
 ; appmult = IsGroupL.appmult g
 ; associative = IsGroupL.associative g
 ; identityR = GrpLImpliesIdR _≡_ _⊕_ i e g
 ; inverseR = GrpLImpliesInvR _≡_ _⊕_ i e g
 }

leftGroupImpliesGroup : {A : Set} → (_≡_ : Rel A) → (_⊕_ : Op₂ A) → (i : Op₁ A) → (e : A) → IsGroupL _≡_ _⊕_ i e → IsGroup _≡_ _⊕_ i e
leftGroupImpliesGroup _≡_ _⊕_ i e g = record
 { reflexive = IsGroupL.reflexive g
 ; symmetric = IsGroupL.symmetric g
 ; transitive = IsGroupL.transitive g
 ; appinv = IsGroupL.appinv g
 ; appmult = IsGroupL.appmult g
 ; associative = IsGroupL.associative g
 ; identityL = IsGroupL.identityL g
 ; inverseL = IsGroupL.inverseL g
 ; identityR = GrpLImpliesIdR _≡_ _⊕_ i e g
 ; inverseR = GrpLImpliesInvR _≡_ _⊕_ i e g
 }
