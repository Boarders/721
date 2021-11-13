{-# OPTIONS --without-K --exact-split --safe #-}
{-
The option --without-K disables Streicher’s K axiom, which we don’t want for univalent mathematics.

The option --exact-split makes Agda to only accept definitions with the equality sign “=” that behave like so-called judgmental or definitional equalities.

The option --safe disables features that may make Agda inconsistent, such as --type-in-type, postulates and more.
-}

module exercises1 where
{-
The filename must be module-name.agda
-}

open import Agda.Primitive public
{-
open means we can access all definitions in Agda.Primitive
public means any file that imports this one gets Agda.Primitive too.
-}

UU : (i : Level) → Set (lsuc i)
UU i = Set i
{-
This code sets up the notation for the universes "UU i" which are types of types.
Formally, "UU" is a function which takes as input a level "i : Level" and produces "UU i", the type of types of level at most i. 
To avoid Russell's paradox, the type "UU i" is a type of the next universe level.
The takeway: to declare that "A is a type of arbitrary universe level" write "A : UU i" in a context where "i : Level".
-}

-- Section 3 -- the natural numbers

{- 
We define the natural numbers as an inductive type of level lzero:
Type "slash b N" to get "ℕ"
-}
data ℕ : UU lzero where
    zero-ℕ : ℕ
    succ-ℕ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}
{-
The induction principle is automatic from this definition using data types; we'll say more about the general form of data types later. 
The following code defines the function guaranteed by the elimination rule, satisfying the two computation rules.
This is not needed to solve the following exercises but feel free to experiment with it.
-}

-- Remark 3.1.2
ind-ℕ : {i : Level} {P : ℕ → UU i} → P zero-ℕ → ((n : ℕ) → P n → P(succ-ℕ n)) → ((n : ℕ) → P n)
ind-ℕ p0 pS zero-ℕ = p0
ind-ℕ p0 pS (succ-ℕ n) = pS n (ind-ℕ p0 pS n)

-- Definition 3.2.1
add-ℕ : ℕ → ℕ → ℕ
add-ℕ m zero-ℕ = m
add-ℕ m (succ-ℕ n) = succ-ℕ (add-ℕ m n)

-- Exercise 3.1.a: define a binary function mul-ℕ
mul-ℕ : ℕ → ℕ → ℕ
mul-ℕ zero-ℕ m = zero-ℕ
mul-ℕ (succ-ℕ n) m = add-ℕ m (mul-ℕ n m)

-- Exercise 3.1.b: define a binary function exp-ℕ

exp-ℕ : ℕ → ℕ → ℕ
exp-ℕ n zero-ℕ = succ-ℕ zero-ℕ
exp-ℕ n (succ-ℕ m) = mul-ℕ n (exp-ℕ n m)

-- Exercise 3.2.a: define a binary function min-ℕ
min-ℕ : ℕ → ℕ → ℕ
min-ℕ zero-ℕ zero-ℕ = zero-ℕ
min-ℕ zero-ℕ (succ-ℕ m) = zero-ℕ
min-ℕ (succ-ℕ n) zero-ℕ = zero-ℕ
min-ℕ (succ-ℕ n) (succ-ℕ m) = succ-ℕ (min-ℕ n m)

-- Exercise 3.2.a: define a binary function max-ℕ

max-ℕ : ℕ → ℕ → ℕ
max-ℕ zero-ℕ zero-ℕ = zero-ℕ
max-ℕ zero-ℕ succ-m@(succ-ℕ m) = succ-m
max-ℕ succ-n@(succ-ℕ n) zero-ℕ = succ-n
max-ℕ (succ-ℕ n) (succ-ℕ m) = succ-ℕ (max-ℕ n m)

-- Exercise 3.3.a: define the sequence triangular-number-ℕ of triangular numbers
triangle : ℕ → ℕ
triangle zero-ℕ = zero-ℕ
triangle succ-n@(succ-ℕ n) = add-ℕ succ-n (triangle n)

-- Exercise 3.3.b: define the function factorial-ℕ = λn.n!
factorial : ℕ → ℕ
factorial zero-ℕ = 1
factorial succ-n@(succ-ℕ n) = mul-ℕ succ-n (factorial n)

-- Exercise 3.4: define the binary function _choose-ℕ_
-- here the underscore tells agda that you want to use infix notation for this function, eg "n choose-ℕ k"
_choose-ℕ_ : ℕ → ℕ → ℕ
zero-ℕ choose-ℕ zero-ℕ = 1
zero-ℕ choose-ℕ succ-ℕ _ = 0
succ-ℕ n choose-ℕ zero-ℕ = 1
succ-ℕ n choose-ℕ succ-k@(succ-ℕ k) = add-ℕ (n choose-ℕ succ-k) (n choose-ℕ k)

-- Exercise 3.5: define the Fibonacci sequence Fibonacci-ℕ
-- A lot of new ideas are needed to do this using the induction principle (see Egbert's agda formalization) so I would recommend just using pattern matching.

-- Exercise 3.6: define the function div-two-ℕ that takes a natural number n to the floor of n/2, using pattern matching

-- Challenge Exercise: For any type A, for any function A → A, and for any natural number n, there is a function A → A defined as the n-fold composition of f.
-- Define a function _fold-comp_ that encodes this construction.
_fold-comp_ : ∀ {A} → ℕ → (A → A) → (A → A)
zero-ℕ fold-comp f = λ a → a 
succ-ℕ n fold-comp f = λ a → f ((n fold-comp f) a)

-- Challenge Exercise: Define composition of dependent functions.
-- _∘_ : (f : (a : A) → B
