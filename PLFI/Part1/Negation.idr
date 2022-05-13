module PLFI.Part1.Negation

import Control.Function.FunExt

-- ¬_ : Set → Set
-- ¬ A = A → ⊥

%default total

%hide Prelude.Not

Not : Type -> Type
Not a = a -> Void

-- ¬-elim : ∀ {A : Set}
--   → ¬ A
--   → A
--     ---
--   → ⊥
-- ¬-elim ¬x x = ¬x x

notElim : (Not a) -> a -> Void
notElim = ($)
-- notElim not_x x = not_x $ x
-- notElim not_x x = not_x x

-- ¬¬-intro : ∀ {A : Set}
--   → A
--     -----
--   → ¬ ¬ A
-- ¬¬-intro x  =  λ{¬x → ¬x x}

notNotIntro : a -> (Not (Not a))
notNotIntro = flip ($)
-- notNotIntro x = \notX => notX x
-- notNotIntro x notX = notX x

-- ¬¬¬-elim : ∀ {A : Set}
--   → ¬ ¬ ¬ A
--     -------
--   → ¬ A
-- ¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)

notNotNotElim : (Not (Not (Not a))) -> Not a
notNotNotElim = flip (.) notNotIntro
-- notNotNotElim nnnx = nnnx . notNotIntro
-- notNotNotElim nnnx x = nnnx (notNotIntro x) -- (\f => f x)

nnnnElim : (Not (Not (Not (Not a)))) -> (Not (Not a))
nnnnElim = notNotNotElim

-- contraposition : ∀ {A B : Set}
--   → (A → B)
--     -----------
--   → (¬ B → ¬ A)
-- contraposition f ¬y x = ¬y (f x)

contraposition : (a -> b) -> (Not b -> Not a)
contraposition = flip (.)
-- contraposition f ny = ny (f x)

-- _≢_ : ∀ {A : Set} → A → A → Set
-- x ≢ y  =  ¬ (x ≡ y)

-- inequality
-- unequality
Neq : a -> a -> Type
Neq x y = Not (x === y)
-- Neq = (Not .) . (===)

-- _ : 1 ≢ 2
-- _ = λ()

-- PLFI.Part1.Negation.h1 : 1 = 2 -> Void
ex1 : Neq (S Z) (S (S Z))
-- ex1 = ?h1 -- x impossible
-- ex1 Refl impossible
ex1 x impossible

-- PLFI.Part1.Negation.h2 : () = Nat -> Void
ex2 : Neq Unit Nat
-- ex2 = ?h2 -- Refl impossible -- wat?
ex2 Refl impossible
-- ex2 x impossible -- ex2 x is not a valid impossible case.

Neq2 : a -> b -> Type
Neq2 x y = Not (x ~=~ y)

-- PLFI.Part1.Negation.h3 : () = 0 -> Void
ex3 : Neq2 Unit Z
ex3 = ?h3 -- x impossible

-- peano : ∀ {m : ℕ} → zero ≢ suc m
-- peano = λ()

peano : {m : Nat} -> Neq Z (S m)
peano Refl impossible

-- id : ⊥ → ⊥
-- id x = x
-- 
-- id′ : ⊥ → ⊥
-- id′ ()

id1 : Void -> Void
id1 x = x

id2 : Void -> Void
id2 x impossible

0
id1_id2 : FunExt => Negation.id1 === Negation.id2
-- id1_id2 = funExt (\x => case x of {})
id1_id2 = funExt (\x => absurd x)
-- id1_id2 = funExt absurd

0
h : FunExt => (f : Void -> a) -> (g : Void -> a) -> f === g
h f g = funExt (\x => absurd x)
