module PLFI.Part1.Decidable

%hide Dec

T : Bool -> Type
T True = ()
T False = Void

tToEq : (b : Bool) -> T b -> b === True
tToEq True () = Refl
tToEq False x = void x

eqToT : {b : Bool} -> b === True -> T b
eqToT Refl = ()

lte : Nat -> Nat -> Bool
lte 0     y     = True
lte (S m) 0     = False
lte (S m) (S n) = lte m n

data LTE : Nat -> Nat -> Type where
  Z : {n : Nat} -> LTE Z n
  S : {m,n : Nat} -> LTE m n -> LTE (S m) (S n)

lteToLTE : (m, n : Nat) -> T (lte m n) -> LTE m n
lteToLTE 0      n     ()  = Z
lteToLTE (S m)  0     v   = void v
lteToLTE (S m)  (S n) x   = S (lteToLTE m n x)

ltFromLT : {m, n : Nat} -> LTE m n -> T (lte m n)
ltFromLT Z     = ()
ltFromLT (S x) = ltFromLT x

data Dec : Type -> Type where
  Yes : a       -> Dec a
  No  : (Not a) -> Dec a

-- absurdLT_S_Z : LTE (S n) Z -> Void
-- absurdLT_S_Z Z     impossible
-- absurdLT_S_Z (S x) impossible

Uninhabited (LTE (S n) Z) where
  uninhabited Z     impossible
  uninhabited (S x) impossible

-- ¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
notLT_S_Z : {m : Nat} -> Not (LTE (S m) Z)
notLT_S_Z = absurd {t = (LTE (S m) Z)}

-- ¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
notLT_S_S : {m, n : Nat} -> Not (LTE m n) -> Not (LTE (S m) (S n))
notLT_S_S not_mn (S mn) = not_mn mn

-- _≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
lteDec : (m, n : Nat) -> Decidable.Dec (LTE m n)
lteDec 0     n     = Yes Z
lteDec (S m) 0     = No notLT_S_Z
lteDec (S m) (S n) with (lteDec m n)
  _ | Yes mn = Yes (S mn)
  _ | No nmn = No (notLT_S_S nmn)

-- fun : {t : Type} -> List t -> List t
-- fun {t = ()} xs = []
-- fun {t = t}  xs = reverse xs

-- showA : {auto fs : a -> String} -> a -> String
-- showA {fs} x = fs x

-- fun1 : Nat -> String
-- fun1 x = showA x

-- -- let showx : Nat -> String
-- --              showx Z = "0"
-- --              showx (S n) = "1" -- ++ showx n
-- --          -- While processing right hand side of fun1. Can't find an implementation for String.
-- --          in showA x

namespace Exercise1

  -- _<?_ : ∀ (m n : ℕ) → Dec (m < n)

  public export
  data LT : Nat -> Nat -> Type where
    Z : LT Z (S n)
    S : LT n m -> LT (S n) (S m)

  injLT : LT (S n) (S m) -> LT n m
  injLT (S x) = x

  lt : Nat -> Nat -> Bool
  lt 0 0          = False
  lt 0 (S k)      = True
  lt (S k) 0      = False
  lt (S k) (S j)  = True

  ltDec : (m, n : Nat) -> Dec (LT m n)
  ltDec 0 0 = No (\case _ impossible)
  ltDec 0 (S n) = Yes Z
  ltDec (S m) 0 = No (\case _ impossible)
  ltDec (S m) (S n) with (ltDec m n)
    _ | Yes mn = Yes (S mn)
    _ | No nmn = No (nmn . injLT)

namespace Exercise2

  -- _≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)

  injS : {m,n : Nat} -> (S m === S n) -> m === n
  injS Refl = Refl

  eqS : {m, n : Nat} -> m === n -> S m === S n
  eqS Refl = Refl

  eqNat : (m, n : Nat) -> Dec (m === n)
  eqNat 0 0 = Yes Refl
  eqNat 0 (S n) = No (\case _ impossible)
  eqNat (S m) 0 = No (\case _ impossible)
  eqNat (S m) (S n) with (eqNat m n)
    _ | Yes ok = Yes (eqS ok)
    _ | No nok = No (nok . injS)

-- _≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)

lteDec2 : (m, n : Nat) -> Dec (LTE m n)
lteDec2 m n = ?lteDec2_rhs


-- lteDec2 m n with (lte m n)
--   _ | True with (lteToLTE m n)
--     _ | p = ?lteDec2_rhsa
--   _ | False = ?lteDec2_rhsb

