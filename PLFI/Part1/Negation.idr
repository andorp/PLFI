module PLFI.Part1.Negation

import Control.Function.FunExt
import Data.DPair

import PLFI.Part1.Relations
import PLFI.Part1.Naturals


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
ex3 x impossible

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

-- assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
-- assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

0
assimilation : FunExt => (f, g : Not a) -> f === g
assimilation f g = funExt (\x => absurd (g x))

-- <-irreflexive
-- Using negation, show that strict inequality is irreflexive, that is, n < n holds for no n.

total
ltIrreflexive0 : (n : N) -> Not (n < n)
ltIrreflexive0 (Suc _) (SucLT x) = ltIrreflexive0 _ x

ltIrreflexive1 : (n : N) -> Not (n < n)
ltIrreflexive1 Zero    ZeroLT    impossible
ltIrreflexive1 Zero    (SucLT x) impossible
ltIrreflexive1 (Suc m) (SucLT x) = ltIrreflexive1 m x

-- Exercise trichotomy (practice)
-- Show that strict inequality satisfies trichotomy, that is, for any naturals m and n exactly one of the following holds:

data Trichotomy : N -> N -> Type where
  LT : m < n -> Trichotomy m n
  EQ : m = n -> Trichotomy m n
  GT : n < m -> Trichotomy m n

uniquenessOfEq : {a : Type} -> (n,m : a) -> (x,y : n === m) -> x === y
uniquenessOfEq n n Refl Refl = Refl

uniquenessOfLT : (n,m : N) -> (x,y : n < m) -> x === y
uniquenessOfLT Zero    (Suc n) ZeroLT    ZeroLT    = Refl
uniquenessOfLT (Suc m) (Suc n) (SucLT x) (SucLT y) = cong SucLT (uniquenessOfLT m n x y)

lessNotEqualLemma : (m < n) -> (m = n) -> Void
lessNotEqualLemma ZeroLT    Refl impossible
lessNotEqualLemma (SucLT x) Refl = lessNotEqualLemma x Refl

lessNotGreaterLemma : (m < n) -> (n < m) -> Void
lessNotGreaterLemma ZeroLT    ZeroLT    impossible
lessNotGreaterLemma ZeroLT    (SucLT x) impossible
lessNotGreaterLemma (SucLT x) (SucLT y) = lessNotGreaterLemma x y

trichotomy : (m, n : N) -> (t1, t2 : Trichotomy m n) -> t1 === t2
trichotomy m n (LT x) (LT y) = cong LT (uniquenessOfLT m n x y)
trichotomy m n (LT x) (EQ p) = absurd (lessNotEqualLemma x p)
trichotomy m n (LT x) (GT y) = absurd (lessNotGreaterLemma x y)
trichotomy m n (EQ p) (LT x) = absurd (lessNotEqualLemma x p)
trichotomy m n (EQ p) (EQ q) = cong EQ (uniquenessOfEq m n p q)
trichotomy m n (EQ p) (GT x) = absurd (lessNotEqualLemma x (sym p))
trichotomy m n (GT x) (LT y) = absurd (lessNotGreaterLemma x y)
trichotomy m n (GT x) (EQ p) = absurd (lessNotEqualLemma x (sym p))
trichotomy m n (GT x) (GT y) = cong GT (uniquenessOfLT n m x y)

data Trichotomy1 : N -> N -> Type where
  LT1 :      (m < n)  -> (Not (m = n)) -> (Not (n < m)) -> Trichotomy1 m n
  EQ1 : (Not (m < n)) ->      (m = n)  -> (Not (n < m)) -> Trichotomy1 m n
  GT1 : (Not (n < m)) -> (Not (m = n)) ->      (n < m)  -> Trichotomy1 m n

lemma1 : (n < m) -> (Not (n = m), Not (m < n))
lemma2 : (m = n) -> (Not (n < m), Not (m < n))
