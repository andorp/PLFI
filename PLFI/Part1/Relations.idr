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

-- z≤n -----
--     0 ≤ 2
-- s≤s -------
--     1 ≤ 3
-- s≤s ---------
--     2 ≤ 4

infix 4 <=

data (<=) : N -> N -> Type where

  Zero
    : {n : N} ->
    -------------
     Zero <= n
  
  Suc
     : {m, n : N} ->
        (m <= n) ->
    -------------------
    (Suc m) <= (Suc n)


invSucLTE : {m,n : N} -> (Suc m) <= (Suc n) -> m <= n
invSucLTE (Suc lte) = lte

invZeroLTE : {m : N} -> m <= Zero -> m = Zero
invZeroLTE Zero = Refl

-- Exercise orderings (practice)
-- Give an example of a preorder that is not a partial order
-- Give an example of a partial order that is not a total order

-- Reflexivity

-- lteRefl0 : n <= n
-- lteRefl0 {n} = ?h1

lteRefl
  : {n : N} ->
  ------------
    n <= n
lteRefl {n = Zero}    = Zero
lteRefl {n = (Suc m)} = Suc lteRefl

-- Transitivity

lteTrans
  : {m,n,p : N} ->
    m <= n ->
    n <= p ->
  ----------------
    m <= p
lteTrans Zero    y       = Zero
lteTrans (Suc x) (Suc y) = Suc (lteTrans x y)

-- lteTrans {n = n}       {m = Zero}    {p = p}       Zero    np        = Zero
-- lteTrans {n = (Suc n)} {m = (Suc m)} {p = (Suc p)} (Suc mn) (Suc np) = Suc (lteTrans mn np)


lteAntisym
  : {m,n : N} ->
    m <= n ->
    n <= m ->
  --------------
     n = m
lteAntisym Zero Zero = Refl
-- lteAntisym (Suc x) (Suc y) = rewrite (lteAntisym x y) in Refl
lteAntisym (Suc x) (Suc y) = cong Suc (lteAntisym x y)
-- lteAntisym (Suc x) (Suc y) = let Refl = lteAntisym x y in Refl

-- Total

-- data Total0 : N -> N -> Type where

--   Forward0
--     : m <= n ->
--     -----------
--       Total0 m n
  
--   Flipped0
--     : n <= m ->
--     -----------
--       Total0 m n

data Total : (m, n : N) -> Type where

  Forward
    : m <= n ->
    -----------
      Total m n
  
  Flipped
    : n <= m ->
    -----------
      Total m n

-- lteTotal : (m, n : N) -> Total m n
-- lteTotal Zero    n       = Forward Zero
-- lteTotal (Suc m) Zero    = Flipped Zero
-- lteTotal (Suc m) (Suc n) with (lteTotal m n)
--   _ | Forward mn = Forward (Suc mn)
--   _ | Flipped nm = Flipped (Suc nm)

lteTotal : (m, n : N) -> Total m n
lteTotal Zero    n       = Forward Zero
lteTotal (Suc m) Zero    = Flipped Zero
lteTotal (Suc m) (Suc n) = case lteTotal m n of
  Forward mn => Forward (Suc mn)
  Flipped nm => Flipped (Suc nm)

%hint
addMonoR_LTE
  : (n,p,q : N)    ->
       p <= q      ->
  -------------------
   (n + p) <= (n + q)
addMonoR_LTE Zero    p q pq = pq
addMonoR_LTE (Suc m) p q pq = Suc (addMonoR_LTE m p q pq)

%hint
addMonoL_LTE
  :   (m,n,p : N)  ->
        m <= n     ->
  -------------------
  (m + p) <= (n + p)
addMonoL_LTE m n p mn =
  rewrite (addComm m p) in
  rewrite (addComm n p) in
  addMonoR_LTE p m n mn

addMono_LTE
  : (m,n,p,q : N)  ->
       m <= n      ->
       p <= q      ->
  -------------------
  (m + p) <= (n + q)
addMono_LTE m n p q mn pq
  = lteTrans
      {n=(n + p)}
      (addMonoL_LTE m n p mn)
      (addMonoR_LTE n p q pq)

-- Exercise (strech) *-mono-≤

multMonoLTE
  : (m,n,p,q : N)  ->
        m <= n     ->
        p <= q     ->
  -------------------
   (m * p) <= (n * q)

-- Strict inequality

infix 4 <

data (<) : N -> N -> Type where
  
  ZeroLT
    :   {n : N}  -> 
    ---------------
    Zero < (Suc n)
  
  SucLT
    :  {m, n : N}   ->
         m < n      ->
    ------------------
     (Suc m) < (Suc n)

-- Exercise lteTrans (recommended)

ltTrans
  : {m,n,p : N} -> 
       m < n    ->
       n < p    ->
  ----------------
       m < p
ltTrans ZeroLT    (SucLT x) = ZeroLT
ltTrans (SucLT x) (SucLT y) = SucLT (ltTrans x y)

ltTrans1
  : (m,n,p : N) -> 
       m < n    ->
       n < p    ->
  ----------------
       m < p
ltTrans1 Zero    (Suc n) (Suc p) ZeroLT    (SucLT x) = ZeroLT
ltTrans1 (Suc m) (Suc n) (Suc p) (SucLT x) (SucLT y) = SucLT (ltTrans1 m n p x y)

-- Exercise trichotomy (practice)

data Trichotomy : N -> N -> Type where
  LT : m < n -> Trichotomy m n
  EQ : m = n -> Trichotomy m n
  GT : n < m -> Trichotomy m n

--  0 m : N
--  0 n : N
-- ------------------------------
-- trichotomy_rhs : Trichotomy m n
trichotomy0 : forall m , n . Trichotomy m n
trichotomy0 = ?trichotomy_rhs0


trichotomy : (m, n : N) -> Trichotomy m n
trichotomy Zero    Zero     = EQ Refl
trichotomy Zero    (Suc _)  = LT ZeroLT
trichotomy (Suc _) Zero     = GT ZeroLT
trichotomy (Suc m) (Suc n)  = case (trichotomy m n) of
  (LT mn) => LT (SucLT mn)
  (EQ mm) => EQ (cong Suc mm)
  (GT nm) => GT (SucLT nm)

-- trichotomy (Suc m) (Suc n) with (trichotomy m n)
--   _ | (LT x)   = ?trichotomy_rhs_4_rhs4_1
--   _ | (EQ prf) = ?trichotomy_rhs_4_rhs4_2
--   _ | (GT x)   = ?trichotomy_rhs_4_rhs4_3




-- Exercise addMonoLT (practice)

addMonoLT
  : (m,n,p,q : N) ->
        m < n     ->
        p < q     -> 
  ------------------
   (m + p) < (n + q)

-- Exercise lte iff lt (recommended)

lteIffLtL
  :   (m,n : N)   ->
    (Suc m) <= n  ->
  ------------------
       m < n

lteIffLtR
  : (m,n : N) ->
      m < n   ->
  --------------
    (Suc n) < m

-- Exercise ltTransRevisited (practice)

ltTransRevisited
  : (m,n,p : N) ->
       m < n   ->
       n < p   ->
  ----------------
       m < p

-- TODO: Report this issue
mutual

  namespace Even

    public export
    data Even : N -> Type where

      Zero :
        ---------
        Even Zero
      
      Suc
        : {n : N} ->
          Odd n   ->
        ------------
        Even (Suc n)

  namespace Odd

    public export
    data Odd : N -> Type where

      Suc
        : {n : N} ->
          Even n  ->
        -------------
        Odd (Suc n)

mutual
  evenAddEven
    : {m, n : N} ->
        Even n   ->
        Even m   ->
    ---------------
      Even (n + m)

  oddAddEven
    : {m, n : N} ->
        Odd m    ->
        Even n   ->
    ---------------
      Odd (m + n)

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
