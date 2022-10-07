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

lteFromLTE : {m, n : Nat} -> LTE m n -> T (lte m n)
lteFromLTE Z     = ()
lteFromLTE (S x) = lteFromLTE x

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
lteDec2 m n with (lteToLTE m n, lteFromLTE {m=m} {n=n})
  _ | (p,q) with (lte m n)
    _ | True  = Yes (p ())
    _ | False = No q

-- Why do we need to spell out the 'p' in the DepPair?
lteDec3 : (m, n : Nat) -> Dec (LTE m n)
lteDec3 m n with (MkDPair
                    {p = \lte => (T lte -> LTE m n, LTE m n -> T lte)}
                    (lte m n)
                    (lteToLTE m n, lteFromLTE {m=m} {n=n}))
  _ | (True ** (p, q)) = Yes (p ())
  _ | (False ** (p, q)) = No q

lteDec4 : (m, n : Nat) -> Dec (LTE m n)
lteDec4 m n with (lteToLTE m n)
  _ | p with (lteFromLTE {m=m} {n=n})
    _ | q with (lte m n)
      _ | True  = Yes (p ())
      _ | False = No q

lteDec5 : (m, n : Nat) -> Dec (LTE m n)
lteDec5 m n with (lteToLTE m n) | (lteFromLTE {m=m} {n=n})
  _ | p | q with (lte m n)
    _ | True  = Yes (p ())
    _ | False = No q

-- * Logical connectives

and : Bool -> Bool -> Bool
and False False = False
and False True  = False
and True  False = False
and True  True  = True

and' : Bool -> Lazy Bool -> Bool
and' False y = False
and' True False = False
and' True True  = True

prodDec : Dec a -> Dec b -> Dec (a, b)
prodDec (Yes x) (Yes y) = Yes (x, y)
prodDec (Yes x) (No ny) = No (\(x0,y0) => ny y0)
prodDec (No nx) y       = No (\(x0,y0) => nx x0)

or : Bool -> Bool -> Bool
or False False = False
or False True  = True
or True  False = True
or True  True  = True

sumDec : Dec a -> Dec b -> Dec (Either a b)
sumDec (Yes x) y       = Yes (Left x)
sumDec (No nx) (Yes x) = Yes (Right x)
sumDec (No nx) (No ny) = No (either nx ny)

not : Bool -> Bool
not False = True
not True = False

negateDec : Dec a -> Dec (Not a)
negateDec (Yes a) = No (\f => f a)
negateDec (No na) = Yes na

impl : Bool -> Bool -> Bool
impl False _      = True
impl True  False  = False
impl True  True   = True

funDec : Dec a -> Dec b -> Dec (a -> b)
funDec (Yes x) (Yes y) = Yes (\_ => y)
funDec (Yes x) (No ny) = No (\f => ny (f x))
funDec (No nx) _       = Yes (\a => absurd (nx a))

isYes : Dec a -> Bool
isYes (Yes x) = True
isYes (No nx) = False

andProduct : (x : Dec a) -> (y : Dec b) -> and (isYes x) (isYes y) === isYes (prodDec x y)
andProduct (Yes x) (Yes y) = Refl
andProduct (Yes x) (No ny) = Refl
andProduct (No nx) (Yes y) = Refl
andProduct (No nx) (No ny) = Refl

orSum : (x : Dec a) -> (y : Dec b) -> or (isYes x) (isYes y) === isYes (sumDec x y)
orSum (Yes x) (Yes y) = Refl
orSum (Yes x) (No ny) = Refl
orSum (No nx) (Yes y) = Refl
orSum (No nx) (No ny) = Refl

%hide Prelude.not

notNegate : (x : Dec a) -> not (isYes x) === isYes (negateDec x)
notNegate (Yes x) = Refl
notNegate (No f) = Refl

implFun : (x : Dec a) -> (y : Dec b) -> impl (isYes x) (isYes y) === isYes (funDec x y)
implFun (Yes x) (Yes y) = Refl
implFun (Yes x) (No ny) = Refl
implFun (No nx) (Yes y) = Refl
implFun (No nx) (No ny) = Refl

iff : Bool -> Bool -> Bool
iff False False = True
iff False True  = False
iff True  False = False
iff True  True  = True

record Iff a b where
  constructor MkIff
  to   : a -> b
  from : b -> a

iffDec : Dec a -> Dec b -> Dec (Iff a b)
iffDec (Yes x) (Yes y) = Yes (MkIff (\z => y) (\z => x))
iffDec (Yes x) (No ny) = No (\i => ny (i.to x))
iffDec (No nx) (Yes y) = No (\i => nx (i.from y))
iffDec (No nx) (No ny) = Yes (MkIff (\x => absurd (nx x)) (\y => absurd (ny y)))

iffIff : (x : Dec a) -> (y : Dec b) -> iff (isYes x) (isYes y) === isYes (iffDec x y)
iffIff (Yes x) (Yes y) = Refl
iffIff (Yes x) (No ny) = Refl
iffIff (No nx) (Yes y) = Refl
iffIff (No nx) (No ny) = Refl

-- * Proof by reflection

minus : (m, n : Nat) -> (0 nm : LTE n m) -> Nat
minus m     0     Z     = m
minus (S m) (S n) (S x) = minus m n x

toWitness : {a : Type} -> {d : Dec a} -> T (isYes d) -> a
toWitness {d=Yes x} () = x
toWitness {d=No nx} x  impossible

minus' : (m, n : Nat) -> {auto nm : T (isYes (lteDec n m)) } -> Nat
minus' m n {nm} = minus m n (toWitness nm)

x : Nat
x = minus' 5 3

-- y : Nat
-- y = minus' 3 5
