module PLFI.Part1.Relations

import PLFI.Part1.Induction
import PLFI.Part1.Naturals
import Syntax.PreorderReasoning

%default total

%hide Prelude.(+)
%hide Prelude.(*)

-- z≤n --------
--     zero ≤ n

--     m ≤ n
-- s≤s -------------
--     suc m ≤ suc n

data LTE : N -> N -> Type where

  ZeroLTE
    : {n : N} ->
    -------------
     LTE Zero n
  
  SucLTE
      : {m, n : N} ->
        LTE m n ->
    -------------------
    LTE (Suc m) (Suc n)

--     z≤n -----
--     0 ≤ 2
-- s≤s -------
--     1 ≤ 3
-- s≤s ---------
--     2 ≤ 4

example1 : LTE 2 4
example1 = SucLTE (SucLTE ZeroLTE)

example2 : LTE 2 4
example2 = SucLTE {m=1} {n=3} $ SucLTE {m=0} {n=2} $ ZeroLTE {n=2}

invSucLTE : {n,m : N} -> LTE (Suc n) (Suc m) -> LTE n m
-- invSucLTE (SucLTE x) = x

invZeroLTE : {n : N} -> LTE n Zero -> n = Zero
-- invZeroLTE ZeroLTE = Refl

-- Exercise orderings (practice)
-- Give an example of a preorder that is not a partial order
-- Give an example of a partial order that is not a total order

-- Reflexivity

lteRefl
  : {n : N} ->
  ------------
    LTE n n
-- lteRefl {n = Zero} = ZeroLTE
-- lteRefl {n = (Suc m)} = SucLTE lteRefl

lteTrans
  : {n,m,p : N} ->
    LTE m n ->
    LTE n p ->
  ----------------
    LTE m p
lteTrans ZeroLTE y = ZeroLTE
lteTrans (SucLTE x) (SucLTE y) = SucLTE (lteTrans x y)

lteAntisym
  : {m,n : N} ->
    LTE m n ->
    LTE n m ->
  --------------
       n = m
lteAntisym ZeroLTE ZeroLTE = Refl
lteAntisym (SucLTE x) (SucLTE y) = cong Suc (lteAntisym x y)

-- Total

data Total : (m, n : N) -> Type where

  Forward
    : LTE m n ->
    ------------
      Total m n
  
  Flipped
    : LTE n m ->
    ------------
      Total m n

lteTotal : (m, n : N) -> Total m n
lteTotal Zero n = Forward ZeroLTE
lteTotal (Suc m) Zero = Flipped ZeroLTE
lteTotal (Suc m) (Suc n) with (lteTotal m n)
  lteTotal (Suc m) (Suc x) | Forward mn = Forward (SucLTE mn)
  lteTotal (Suc m) (Suc x) | Flipped nm = Flipped (SucLTE nm)

addMonoR_LTE
  : (n,p,q : N)    ->
      LTE p q      ->
  -------------------
  LTE (n + p) (n + q)
addMonoR_LTE Zero    p q lte = lte
addMonoR_LTE (Suc m) p q lte = SucLTE (addMonoR_LTE m p q lte)

addMonoL_LTE
  :   (m,n,p : N)  ->
        LTE m n    ->
  -------------------
  LTE (m + p) (n + p)
addMonoL_LTE m n p lte
  = rewrite (addComm m p) in 
    rewrite (addComm n p) in
    addMonoR_LTE p m n lte

addMono_LTE
  : (m,n,p,q : N)  ->
       LTE m n     ->
       LTE p q     ->
  -------------------
  LTE (m + p) (n + q)
addMono_LTE m n p q mn pq = lteTrans (addMonoL_LTE m n p mn) (addMonoR_LTE n p q pq)

-- Exercise (strech) *-mono-≤

multMonoLTE
  : (m,n,p,q : N)  ->
        LTE m n    ->
        LTE p q    ->
  -------------------
  LTE (m * p) (n * q)

-- Strict inequality

data LT : N -> N -> Type where
  
  ZeroLT
    :   {n : N}  -> 
    ---------------
    LT Zero (Suc n)
  
  SucLT
    :  {n, m : N}   ->
    ------------------
    LT (Suc n) (Suc m)

-- Exercise lteTrans (recommended)

ltTrans
  : (m,n,p : N) -> 
      LT m n    ->
      LT n p    ->
  ----------------
      LT m p

-- Exercise trichotomy (practice)

data Trichotomy : N -> N -> Type where

-- Exercise addMonoLT (practice)

addMonoLT
  : (m,n,p,q : N) ->
        LT m n    ->
        LT p q    -> 
  ------------------
  LT (m + p) (n + q)

-- Exercise lte iff lt (recommended)

lteIffLtL
  :   (m,n : N)   ->
    LTE (Suc m) n ->
  ------------------
       LT m n

lteIffLtR
  : (m,n : N) ->
     LT m n   ->
  --------------
   LTE (Suc n) m

-- Exercise ltTransRevisited (practice)

{-
-- This makes Idris go haywire.
ltTransRevisited
  : (m,n,p : N) ->
       LT m n   ->
       LT n p   ->
  ----------------
       LT m p
-}

-- TODO: Report this issue
-- mutual

--   namespace Even
--     public export
--     data Even : N -> Type where

--       ZeroE :
--         ---------
--         Even Zero
      
--       SucE
--         : {n : N} ->
--           Odd n   ->
--         ------------
--         Even (Suc n)

--   namespace Odd

--     public export
--     data Odd : N -> Type where

--       SucE
--         : {n : N} ->
--           Even n  ->
--         -------------
--         Odd (Suc n)

-- mutual
--   evenAddEven
--     : {m, n : N} ->
--         Even n   ->
--         Even m   ->
--     ---------------
--       Even (n + m)
--   evenAddEven ZeroE e2 = e2
--   evenAddEven (SucE x) e2 = ?e_2

--   -- oddAddEven
--   --   : {m, n : N} ->
--   --       Odd m    ->
--   --       Even n   ->
--   --   ---------------
--   --     Odd (m + n)

-- Exercise - Bin-predicates

-- Can : Bin -> Type

-- Can b
-- -----------
-- Can (inc b)

-- ----------
-- Can (to n)

--      Can b
-- ---------------
-- to (from b) = b
