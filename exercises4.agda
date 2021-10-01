{-# OPTIONS --without-K --exact-split --safe #-}

module exercises4 where
{-
Please rename your file to exercises4-yourusername.agda
-}

open import Agda.Primitive public
{-
open means we can access all definitions in Agda.Primitive
public means any file that imports this one gets Agda.Primitive too.
-}

UU : (i : Level) → Set (lsuc i)
UU i = Set i

-- The one-sided identity type is the type family in context of a type A and term a : A freely generated by refl_a : Id a a.
data Id {i : Level}{A : UU i}(a : A) : A → UU i where
    refl : Id a a

-- Definition 5.3.1: the application of functions on paths
ap : {i j : Level}{A : UU i}{B : UU j}{x y : A} → (f : A → B) → (Id x y) → (Id (f x) (f y))
ap f refl = refl 

-- Exercise: define a function componentwise-equality that proves that if two dependent functions
-- f g : (a : A) → B a are identifiable then for all a : A the terms f a and g a are identifiable.
-- In summary: identifiable functions are "pointwise identifiable"
-- The converse implication does not hold in dependent type theory but does hold in homotopy type theory (as we will prove soon).

data Σ {i j : Level}(A : UU i)(B : A → UU j) : UU (i ⊔ j) where
    pair : (a : A) → B a → Σ A B

pr1 : {i j : Level}{A : UU i}{B : A → UU j} → Σ A B → A
pr1 (pair x x₁) = x

pr2 : {i j : Level}{A : UU i}{B : A → UU j} → (z : Σ A B) → (B (pr1 z))
pr2 (pair x x₁) = x₁

-- product types are a special case of dependent pair types
_×_ : {i j : Level} → UU i → UU j → UU (i ⊔ j)
A × B = Σ A (λ a → B)

-- A and B are logically equivalent if the type "A ↔ B" (type "\leftrightarrow") is inhabited
_↔_ : {i j : Level} → UU i → UU j → UU (i ⊔ j)
A ↔ B = (A → B) × (B → A)

-- Exercise: prove the type theoretic "axiom of choice" by defining a function
-- choice : {i j k : Level}{A : UU i}{B : UU j}{C : A → B → UU k} → ((a : A) → Σ B (λ b → (C a b))) → Σ (A → B)(λ f → ((a : A) → (C a (f a))))

-- Challenge Exercise: state and prove a more general version of the type theoretic "axiom of choice" by defining an analogous function for types
-- {A : UU i}{B : A → UU j}{C : (a : A) → B a → UU k}

-- Exercise: define a type family that asks whether a function is surjective
-- The curly braces {A = A}{B = B} are giving agda the names for some implicit arguments you will need to define this term.
-- is-surj : {i j : Level}{A : UU i}{B : UU j} → (A → B) → UU (i ⊔ j)
-- is-surj {A = A}{B = B} f = ?

-- Exercise: define the type family that asks whether a function has a section 
-- Here f : A → B has a section if there is some s : B → A so that f (s b) = b for all b in B.
-- Warning: use the weaker "pointwise identifiable" notion to relate the functions f ∘ s and id B.
-- has-section : {i j : Level}{A : UU i}{B : UU j} → (A → B) → UU (i ⊔ j)

-- Challenge Exercise: prove the axiom of choice, showing that a function is surjective iff it has a section

-- last time we called the empty type "empty" but today I prefer "∅" (type "\emptyset")
data ∅ : UU lzero where

¬_ : {i : Level} → UU i → UU i
¬ A = A → ∅

ex-falso : {i : Level}{A : UU i} → ∅ → A
ex-falso ()

-- last time we called the unit type "unit" but today I prefer "𝟙" (type "\b1")
data 𝟙 : UU lzero where
    star : 𝟙

-- type "\sqcup" for "⊔". This is a union of universe levels defined in Agda.Primitive
data coprod {i j : Level}(A : UU i)(B : UU j) : UU (i ⊔ j) where
    inl : A → coprod A B
    inr : B → coprod A B

-- Alternate notation for coproduct types
_+_ : {i j : Level}(A : UU i)(B : UU j) → UU (i ⊔ j)
A + B = coprod A B

data bool : UU lzero where
    true false : bool

-- Exercise: show that bool is logically equivalent to the type 𝟙 + 𝟙 by defining three functions
-- bool-to-1+1 : bool → 𝟙 + 𝟙

-- 1+1-to-bool : 𝟙 + 𝟙 → bool

-- bool-iff-1+1 : bool ↔ (𝟙 + 𝟙)

-- Now we will characterize the identity type of bool
-- Exercise 6.2.a: define Eq-bool, observational equality on the booleans
-- Eq-bool : bool → bool → UU lzero

-- Exercise 6.2.b: show that Eq-bool is logically equivalent to the identity type of bool by defining three functions
-- eq-bool-to-id-bool : (s t : bool) → ((Eq-bool s t) → (Id s t))
-- id-bool-to-eq-bool : (s t : bool) → ((Id s t) → (Eq-bool s t))
-- eq-bool-iff-id-bool : (s t : bool) → ((Eq-bool s t) ↔ (Id s t))

neg-bool : bool → bool
neg-bool true = false
neg-bool false = true

-- Exercise 6.2.c: define bool-neq-neg-bool proving that b ≠ neg-bool b for all booleans b
-- bool-neq-neg-bool : (b : bool) → ¬(Id b (neg-bool b))

-- Exercise 6.2.c: define a term true-neq-false that concludes that true ≠ false

-- The transport function can be used to define a second proof that true ≠ false
tr : {i j : Level}{A : UU i}(B : A → UU j){x y : A} → (Id x y) → (B x) → (B y)
tr B refl b = b

Bool-In-World : bool → UU lzero
Bool-In-World true = 𝟙
Bool-In-World false = ∅

-- Exercise: use the transport function and the type family Bool-In-World to give a second proof that true ≠ false

-- Exercise: provide two proofs, "pf1" and "pf2", of the proposition {P Q : UU lzero} → (P × Q) → (P + Q)

-- You can prove that pf1 ≠ pf2 by solving the following exercises

-- Challenge Exercise: prove that if pf1 = pf2 then inl star = inr star as terms of type 𝟙 + 𝟙
-- Hint: a term hyp : Id pf1 pf2 is really an equality between functions pf1 pf2 : (P × Q) → (P + Q)

-- Challenge Exercise: prove that if pf1 = pf2 then true = false as terms of type bool

-- Challenge Exercise: conclude that pf1 ≠ pf2

