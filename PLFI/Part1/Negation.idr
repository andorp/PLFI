module PLFI.Part1.Negation

-- ¬_ : Set → Set
-- ¬ A = A → ⊥

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
