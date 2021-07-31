module PLFI.Part1.Naturals

-- https://plfa.gihub.io/Naturals

data Vect : Nat -> (t : Type) -> Type where
  Nil  : Vect 0 t
  (::) : (x : t) -> Vect n t -> Vect (1 + n) t

replicate : Nat -> t -> List t

replicateV : (n : Nat) -> t -> Vect n t
replicateV 0 x = []
replicateV (S k) x = x :: replicateV k x

%hide (+)
%hide (*)

-- %default total

-- data N0 = Zero | Suc N0

{-
----------- Zero
  Zero : N

   m : N
----------- Suc
 Suc m : N
-}

public export
data N : Type where

  -- Base case
  Zero :
    --------
       N

  -- Inductive case
  Suc :
    (m : N) ->
    ----------
         N

export
Num N where
  (*) = ?m1
  (+) = ?a1
  fromInteger n with (compare n 0)
     fromInteger n | LT = Zero
     fromInteger n | EQ = Zero
     fromInteger n | GT = Suc (assert_total (fromInteger (n-1)))

ex1 : N
ex1 = Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))

test : N
test = (-7)

total
public export
(+) : N -> N -> N
-- a + b = Zero -- ?add1
Zero    + m = m
(Suc n) + m = Suc (n + m)

export
addEquation1 : {n : N} -> (Zero + n) = n -- Refl : Equal x x
addEquation1 = Refl

export
addEquation2 : (Suc m) + n = Suc (m + n)
addEquation2 = Refl

total
public export
(*) : N -> N -> N
Zero    * n = Zero
(Suc m) * n = n + (m * n)

-- N -> Zero * ? = Zero
multEquation0 : {n : N} -> Zero * n = Zero
-- test :: Maybe (Maybe Int)
-- test : Maybe $ Maybe Int
-- test : (n : Nat) -> let m = n + n in Vect m Int


export
multEquation1 : Zero * n = Zero
multEquation1 = Refl

export
multEquation2 : (Suc m) * n = n + (m * n)
multEquation2 = Refl

infixr 8 ^

-- Exercise: recommended

total
export
(^) : N -> N -> N
m ^ Zero    = Suc Zero
m ^ (Suc n) = m * (m ^ n)

-- m ^ 0        =  1
-- m ^ (1 + n)  =  m * (m ^ n)

export
expEquation1 : m ^ Zero = Suc Zero
expEquation1 = Refl

export
expEquation2 : m ^ (Suc n) = m * (m ^ n)
expEquation2 = Refl

-- monus

infixl 6 -*

total
export
(-*) : N -> N -> N
m       -* Zero     = m
Zero    -* (Suc n)  = Zero
(Suc m) -* (Suc n)  = m -* n

-- Exercise: strech

public export
data Bin : Type where
  E : Bin
  O : Bin -> Bin
  I : Bin -> Bin

-- 1101 is encoded as
-- IOIIE this needs to be read reversed:
-- EIIOI

export
inc : Bin -> Bin

export
to : N -> Bin

export
from : Bin -> N
