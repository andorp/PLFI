module PLFI.Part1.Negation

import Control.Function.FunExt
import Data.DPair

import PLFI.Part1.Relations
import PLFI.Part1.Naturals
import PLFI.Part1.Isomorphism

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

public export
data Trichotomy : N -> N -> Type where
  LT : m < n -> Trichotomy m n
  EQ : m = n -> Trichotomy m n
  GT : n < m -> Trichotomy m n

mkTrichotomy : (m, n : N) -> Trichotomy m n
mkTrichotomy Zero    Zero     = EQ Refl
mkTrichotomy Zero    (Suc _)  = LT ZeroLT
mkTrichotomy (Suc _) Zero     = GT ZeroLT
mkTrichotomy (Suc m) (Suc n)  = case (mkTrichotomy m n) of
  (LT mn) => LT (SucLT mn)
  (EQ mm) => EQ (cong Suc mm)
  (GT nm) => GT (SucLT nm)

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

public export
data Trichotomy1 : N -> N -> Type where
  LT1 :      (m < n)  -> (Not (m = n)) -> (Not (n < m)) -> Trichotomy1 m n
  EQ1 : (Not (m < n)) ->      (m = n)  -> (Not (n < m)) -> Trichotomy1 m n
  GT1 : (Not (m < n)) -> (Not (m = n)) ->      (n < m)  -> Trichotomy1 m n

{n,m : N} -> Show (Trichotomy1 n m) where
  show (LT1 x f g)   = "LT1"
  show (EQ1 f prf g) = "EQ1"
  show (GT1 f g x)   = "GT1"

-- ISSUE: No warning about this.
-- When its not referred, this was optimized away.
lemma1 : (n < m) -> (Not (n = m), Not (m < n))
lemma2 : (m = n) -> (Not (n < m), Not (m < n))
lemma3 : Void

to1 : Trichotomy n m -> Trichotomy1 n m
to1 (LT x) = LT1 x (lessNotEqualLemma x) (lessNotGreaterLemma x)
to1 (EQ x) = EQ1 (flip lessNotEqualLemma x) x (flip lessNotEqualLemma (sym x))
to1 (GT x) = GT1 (lessNotGreaterLemma x) (\y => lessNotEqualLemma x (sym y)) x

to2 : Trichotomy n m -> Trichotomy1 n m
to2 (LT x) = LT1 x (fst (lemma1 x)) (snd (lemma1 x))
to2 (EQ x) = EQ1 (snd (lemma2 x)) x (fst (lemma2 x))
to2 (GT x) = GT1 (snd (lemma1 x)) (\y => fst (lemma1 x) (sym y)) x

-- ISSUE of not reporting, even when it used.
g : N -> N

h1 : Trichotomy n m -> Trichotomy (const 1 (g n)) (const 2 (g m))
h1 (LT x) = mkTrichotomy 1 2
h1 (EQ x) = mkTrichotomy 1 2
h1 (GT x) = mkTrichotomy 1 2

export
test : IO ()
test = do
  putStrLn "to1"
  printLn $ to1 $ mkTrichotomy 3 4
  printLn $ to1 $ mkTrichotomy 4 4
  printLn $ to1 $ mkTrichotomy 3 1
  printLn $ to1 $ h1 $ mkTrichotomy 3 1
  -- putStrLn "to2"
  -- printLn $ to2 $ mkTrichotomy 3 4
  -- printLn $ to2 $ mkTrichotomy 4 4
  -- printLn $ to2 $ mkTrichotomy 3 1

-- ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
deMorganLaw1 : FunExt => Iso (Not (Either a b)) (Not a, Not b)
deMorganLaw1 = MkIso
  { to     = \f => (f . Left, f . Right)
  , from   = \(f,g) , x => case x of
                (Left y)  => f y
                (Right y) => g y
  , fromTo = \f => funExt (\case
                            (Left x)  => Refl
                            (Right x) => Refl)
  , toFrom = \(f,g) => Refl -- (\x => f x, \x => g x) = (f, g)
  }

-- ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)
deMorganLaw2 : Iso (Not (a,b)) (Either (Not a) (Not b))
deMorganLaw2 = MkIso
  { to     = \f => ?h2
    --  0 b : Type
    --  0 a : Type
    --    f : (a, b) -> Void
    -- ------------------------------
    -- h2 : Either (a -> Void) (b -> Void)  
  , from   = ?h3
  , fromTo = ?h4
  , toFrom = ?h5
  }

deMorganLaw3 : Either (Not a) (Not b) -> Not (a,b)
deMorganLaw3 (Left f) (a, b)  = f a
deMorganLaw3 (Right g) (a, b) = g b

-- postulate
--   em : ∀ {A : Set} → A ⊎ ¬ A

public export
interface ExcludedMiddle where
  em : {a : Type} -> Either a (Not a)

-- em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
emIrrefutable : {a : Type} -> Not (Not (Either a (Not a)))
emIrrefutable f = f (Right (\a => f (Left a)))
