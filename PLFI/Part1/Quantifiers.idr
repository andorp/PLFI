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

