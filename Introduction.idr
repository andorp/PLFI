module Introduction

-- This is a simple comment

-- Import statements
import Data.Vect
import public Syntax.PreorderReasoning


-- All the functions/definitions in this module must be total.
-- Total definitions can be safely used in proofs and type level programming
%default total

-- Hide the name IsJust from Prelude as we are going to redefine and
-- use it in this module. Hiding things are not necessary, shadowing
-- works nice.
%hide IsJust
-- %hide Maybe.IsJust

-- Simple ADT style data definition
||| This is a documentational comment for Maybe1
data Maybe1 a
  = Nothing1
  | Just1 a

-- Laziness introduced explictely
fromMaybe1 : Lazy a -> Maybe1 a -> a
fromMaybe1 x Nothing1  = x
fromMaybe1 _ (Just1 x) = x

-- All the three arguments will be evalauted here as Idris strict.
maybe : b -> (a -> b) -> Maybe1 a -> b
maybe y f Nothing1  = y
maybe _ f (Just1 x) = f x

-- If a function needs to be non-total it could be partial
partial
fromJust0 : Maybe1 a -> a
fromJust0 (Just1 o) = o

interface MyClass t where
  myType  : Type
  myType2 : Type -> Type
  myFunction : myType -> myType2 myType -> Nat

MyClass Nat where
  -- myType = String
  -- myType2 = Maybe1
--  myFunction True (Just1 True) = 1
  myFunction _ _ = 0

MyClass Bool where
  myType = String
  myType2 = Maybe1
  myFunction "hello" Nothing1 = 1
  myFunction _ _ = 0

-- Type class instances doesn't require the 'instance' keyword
Functor Maybe1 where
  map f Nothing1  = Nothing1
  map f (Just1 x) = Just1 (f x)

-- GADT style data definition
data Maybe2 : Type -> Type where
  Nothing2 : Maybe2 a
  Just2    : a -> Maybe2 a

Functor Maybe2 where
  map f x = ?m2F1

Foldable Maybe2 where
  foldl = ?m2Fl

Traversable Maybe2 where
  traverse f x = ?m2T

-- This is dense, but we can use simple values in the parameters of GADTs
-- These are indices of the datatype. We call these kind of construction as
-- indexed datatypes.
data IsJust : Maybe a -> Type where
  IsJustPrf : IsJust (Just a)

-- This is dense too. But this is one way how to create an optional
-- IsJustPrf value, this kind of construction will play a huge role in
-- dependently type programming.
mkIsJustProof : (x : Maybe a) -> Maybe (IsJust x)
mkIsJustProof (Just o) = Just IsJustPrf
mkIsJustProof Nothing  = Nothing

-- We can write the safe version of fromJust, which requires a proof
-- that the passed value can not be Nothing. You can think of this
-- kind of programming, as forced assumption checks. At every place
-- where the client code wants to use the fromJust1 function, it also
-- has to provide a proof that it can't be Nothing, at this point the
-- mkIsJustProof comes handy. With this style the author of the fromJust1
-- function forces the client code to use the function accordingly.
-- But this is an oversimplified example.
fromJust1 : (x : Maybe a) -> (prf : IsJust x) -> a
fromJust1 (Just o) IsJustPrf = o
fromJust1 Nothing _ impossible

-- Impossible cases doesn't need to written out
fromJust2 : (x : Maybe a) -> (prf : IsJust x) -> a
fromJust2 (Just o) IsJustPrf = o

-- Parameters can be implicit, which are market with { }
-- auto parameters are filled by the compiler, if it can not be
-- found in the context, we will have a compilation error.
fromJust3 : (x : Maybe a) -> {auto prf : IsJust x} -> a
fromJust3 (Just o) = o

-- Non named auto implicit parameters has a nice syntactical-sugar
fromJust4 : (x : Maybe a) -> (IsJust x) => a
fromJust4 (Just o) = o

-- Idris supports linear typing, via quantitative type theory
data Maybe3 : (0 a : Type) -> Type where
  Nothing3 : {0 a : Type} -> Maybe3 a
  LinJust3 : (1 a : Type) -> Maybe3 a
  Just3    : (a : Type)   -> Maybe3 a

-- Another way to create a datatype with one constructor and some fields
-- is to define a record
record Tuple a b where
  constructor MkTuple
  fst : a
  snd : b

createTuple : a -> b -> Tuple a b
createTuple x y = MkTuple x y

sumTuple : Tuple Integer Integer -> Integer
sumTuple (MkTuple x y) = x + y

-- Section on how to use Idris to proof things from the PLFI book.

-- plusAssoc : (m, n, p : Nat) -> (m + n) + p = m + (n + p)

plusAssoc : (n, m, p : Nat) -> (n + m) + p = n + (m + p)
plusAssoc Z     m p = Refl
plusAssoc (S n) m p = cong S (plusAssoc n m p)

-- plusComm : (m, n : Nat) -> m + n = n + m

plusRightZero : (n : Nat) -> n = n + 0
plusComm : (m, n : Nat) -> m + n = n + m

-- |~ statement_1
-- ~~ statement_2 ...(proof_of_transition_from_statement1_to_statement2)

-- swap : (n, m, p : Nat) -> m + (n + p) = n + (m + p)
-- swap n m p = Calc $
--   |~ m + (n + p)
--   ~~ (m + n) + p ...(?h2)
--   ~~ (n + m) + p ...(?h3)
--   ~~ n + (m + p) ...(?h1)

swap : (n, m, p : Nat) -> m + (n + p) = n + (m + p)
swap n m p = Calc $
  |~ m + (n + p)
  ~~ (m + n) + p ...(sym $ plusAssoc m n p)
  ~~ (n + m) + p ...(cong (+p) (plusComm m n))
  ~~ n + (m + p) ...(plusAssoc n m p)

filterV : (a -> Bool) -> Vect n a -> (p ** Vect p a)
filterV p [] = (_ ** [])
filterV p (x :: xs) with (filterV p xs)
  filterV p (x :: xs) | (_ ** xs') = if (p x) then (_ ** x :: xs') else (_ ** xs')

-- missing: rewrite

main : IO ()
main = putStrLn "Hello PLFI."
