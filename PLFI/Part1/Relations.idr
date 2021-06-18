module PLFI.Part1.Relations

import PLFI.Part1.Naturals
import Syntax.PreorderReasoning

%default total

%hide Prelude.(+)

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
  : (n,p,q : N) ->
      LTE p q ->
  -------------------
  LTE (n + p) (n + q)
addMonoR_LTE Zero    p q lte = lte
addMonoR_LTE (Suc m) p q lte = SucLTE (addMonoR_LTE m p q lte)
