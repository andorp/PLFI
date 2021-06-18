module PLFI.Part1.Naturals

-- http://plfa.gihub.io/Naturals

import Syntax.PreorderReasoning

%hide (+)
%hide (*)

{-

----------- Zero
  Zero : N

   m : N
----------- Suc
 Suc m : N

-}

namespace Take1

  data N = Zero | Suc N

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
  fromInteger n with (compare n 0)
     fromInteger n | LT = Zero
     fromInteger n | EQ = Zero
     fromInteger n | GT = Suc (fromInteger (n-1))

total
public export
(+) : N -> N -> N
-- a + b = ?add1
Zero    + m = m
(Suc n) + m = Suc (n + m)

export
addEquation1 : Zero + n = n

export
addEquation2 : (Suc m) + n = Suc (m + n)

total
public export
(*) : N -> N -> N
a * b = ?mult1

export
multEquation1 : Zero    * n = Zero

export
multEquation2 : (Suc m) * n = n + (m * n)

infixr 8 ^

-- Exercise: recommended

total
export
(^) : N -> N -> N
a ^ b = ?exp1

export
expEquation1 : m ^ Zero = Suc Zero

export
expEquation2 : m ^ (Suc n) = m * (m ^ n)

-- monus

infixl 6 -*

total
export
(-*) : N -> N -> N
a -* b = ?monus1

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
