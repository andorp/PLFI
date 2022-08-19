module PLFI.Part1.Quantifiers

import PLFI.Part1.Isomorphism
import Control.Function.FunExt

-- +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

addAssoc : forall m , n , p . (m + n) + p === m + (n + p)

exists : (x : Nat ** x === 4)
exists = (4 ** Refl)

data Exists : t -> (t -> Type) -> Type where
  MkExists : (x : t) -> (y : f x) -> Exists x f

-- postulate
--   ∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
--     (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)

--    a : Type
--    b : a -> Type
--    c : a -> Type
--    arg : (b x, c x)
-- ------------------------------
-- w11_0 : (b x, c x)

forallDistribProduct0
  :  {a : Type} -> {b, c : a -> Type}
  -> (forall x . (b x, c x)) ~~ (forall x . b x , forall x . c x)
forallDistribProduct0 = MkIso
  { to     = \arg => ?w11_0 -- : a -> b -- w1 : (b x, c x) -> (b x, c x)
  , from   = ?w21 -- : b -> a
  , fromTo = ?w31 -- : (x : a) -> from (to x) === x
  , toFrom = ?w41 -- : (y : b) -> to (from y) === y
  }

--    a : Type
--    b : a -> Type
--    c : a -> Type
--    arg : (b y, c y)
-- ------------------------------
-- w1_0 : (b x, c z)

--    a : Type
--    b : a -> Type
--    c : a -> Type
--    arg : forall y . (b y, c y)
-- ------------------------------
-- w1_0 : forall x , z . (b x, c z)

--    a : Type
--    b : a -> Type
--    c : a -> Type
--    arg : {y : a} -> (b y, c y)
-- ------------------------------
-- w1_0 : {x, y : a} -> (b x, c z)

forallDistribProduct1
  :  {a : Type} -> {b, c : a -> Type}
  -> (forall y . (b y, c y)) ~~ (forall x . b x , forall z . c z)
forallDistribProduct1 = MkIso
  { to     = \arg => ?w1_0 -- : a -> b
  , from   = ?w2 -- : b -> a
  , fromTo = ?w3 -- : (x : a) -> from (to x) === x
  , toFrom = ?w4 -- : (y : b) -> to (from y) === y
  }

tuple1 : Type -> Type -> Type
tuple1 a b = (a,b)

tuple2 : Type -> Type -> (Type, Type)
tuple2 ty1 ty2 = (ty1,ty2)

eta : (f : a -> b) -> ((\x => f x) === f)
eta f = Refl

-- Universal property of tuple.
tupleUP : (t : (a,b)) -> ((fst t, snd t) === t)
tupleUP (x, y) = Refl

alpha : (f : a -> b -> c) -> ((\x , y => f x y) === (\y , x => f y x))
alpha f = Refl

forallDistribProduct
  :  FunExt
  => {a : Type} -> {b, c : a -> Type}
  -> ((x : a) -> (b x, c x)) ~~ ((x : a) -> b x , (x : a) -> c x)
forallDistribProduct = MkIso
  { to     = \fg => (\x => fst (fg x) , \x => snd (fg x))
  , from   = \(f , g) , x => (f x, g x)
  , fromTo = \fg => funExt (\x => tupleUP (fg x))
  , toFrom = \(f,g) => Refl
  }

-- postulate
--   ⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
--     (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x

sumForallImpliesForallSum : {b,c : a -> Type} -> (Either ((x : a) -> b x) ((x : a) -> c x)) -> ((x : a) -> Either (b x) (c x))
sumForallImpliesForallSum (Left  f) x = Left (f x)
sumForallImpliesForallSum (Right f) x = Right (f x)

data Sigma : (a : Type) -> (b : a -> Type) -> Type where
  MkSigma : (x : a) -> b x -> Sigma a b

record Sigma' (a : Type) (b : a -> Type) where
  constructor MkSigma'
  proj1 : a
  proj2 : b proj1

Ex : {a : Type} -> (b : a -> Type) -> Type
Ex {a} b = Sigma a b

eElim
  :  ((x : a) -> (b x) -> c)
  -> Ex b
  --------------------------
  -> c
eElim f (MkSigma x y) = f x y

toF : ((x : a) -> b x -> c) -> (Sigma a b) -> c
toF f = \(MkSigma x y) => f x y

fromF : (Sigma a b -> c) -> (x : a) -> b x -> c
fromF f = \x , y => f (MkSigma x y)

toFromF : FunExt => (f : (Sigma a b -> c)) -> toF (fromF f) === f
toFromF f = funExt (\(MkSigma x y) => Refl)

fromToF : FunExt => {b : a -> Type} -> (f : ((x : a) -> b x -> c)) -> fromF (toF f) === f
fromToF f = funExt (\x => funExt (\y => Refl))

forallExsist : FunExt => {b : a -> Type} -> Iso ((x : a) -> b x -> c) (Ex b -> c)
forallExsist = MkIso
  { to     = toF
  , from   = fromF
  , toFrom = toFromF
  , fromTo = fromToF
  }

-- postulate
--   ∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
--     ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)

existsDistribEither
  :  {a : Type} -> {b, c : a -> Type}
  -> Iso (Ex (\x => Either (b x) (c x))) (Either (Ex (\x => b x)) (Ex (\x => c x)))
existsDistribEither = MkIso
  { to = \case
          (MkSigma a (Left x)) => Left (MkSigma a x)
          (MkSigma a (Right x)) => Right (MkSigma a x)
  , from = \case
            (Left (MkSigma x y)) => MkSigma x (Left y)
            (Right (MkSigma x y)) => MkSigma x (Right y)
  , toFrom = \case
              (Left (MkSigma x y)) => Refl
              (Right (MkSigma x y)) => Refl
  , fromTo = \case
              (MkSigma x (Left y)) => Refl
              (MkSigma x (Right y)) => Refl
  }

-- postulate
--   ∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
--     ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)

existsImpliesExists
  :  {a : Type} -> {b,c : a -> Type}
  -> Iso (Ex (\x => (b x, c x))) (Ex (\x => (b x)), Ex (\x => (c x)))
existsImpliesExists = MkIso
  { to = \case
            (MkSigma a (x, y)) => (MkSigma a x, MkSigma a y)
  , from = \case
            ((MkSigma a1 x), (MkSigma a2 y)) => MkSigma a2 (?x, ?eie2_7)
    -- This does not hold, because when we have a1 and a2 they are not necessary the same
    -- meaning that we can not create the ∃[ x ] (B x × C x) part.
  , toFrom = ?eie3
  , fromTo = ?eie4
  }

mutual

  data Even : Nat -> Type where
    EZ : Even Z
    ES : Odd n -> Even (S n)
  
  data Odd : Nat -> Type where
    OS : Even n -> Odd (S n)

mutual
  evenEx : {n : Nat} -> Even n -> Ex (\m => (m * 2 === n))
  evenEx EZ = MkSigma 0 Refl
  evenEx (ES x) with (oddEx x)
    _ | MkSigma m Refl = MkSigma (S m) Refl
  
  oddEx : {n : Nat} -> Odd n -> Ex (\m => (1 + m * 2 === n))
  oddEx (OS x) with (evenEx x)
    _ | MkSigma m Refl = MkSigma m Refl
  
mutual
  exEven : {n : Nat} -> Ex (\m => m * 2 === n) -> Even n
  exEven (MkSigma 0     Refl) = EZ
  exEven (MkSigma (S m) Refl) = ES (exOdd (MkSigma m Refl))

  exOdd  : {n : Nat} -> Ex (\m => 1 + (m * 2) === n) -> Odd n
  exOdd (MkSigma m Refl) = OS (exEven (MkSigma m Refl))

-- ¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
--   → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x

notExIsoAllNot
  :  FunExt
  => {a : Type} -> {b : a -> Type}
  -> Iso (Not (Ex (\x => b x))) ((x : a) -> Not (b x))
notExIsoAllNot = MkIso
  { to = \ nExy , x , y => nExy (MkSigma x y)
  , from = \ anxy , (MkSigma x y) => anxy x y
  , fromTo = \ nExy => funExt (\ (MkSigma x y) => Refl)
  , toFrom = \ anxy => Refl
  }

-- postulate
--   ∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
--     → ∃[ x ] (¬ B x)
--       --------------
--     → ¬ (∀ x → B x)

exNotImpliesNotAll
  :  {a : Type} -> {b : a -> Type}
  -> (Ex (\x => (Not (b x))))
  -> Not ((x : a) -> b x)
exNotImpliesNotAll (MkSigma x y) fx = y (fx x)
