module PLFI.Part1.Connectives

-- data _×_ (A B : Set) : Set where

--   ⟨_,_⟩ :
--       A
--     → B
--       -----
--     → A × B

test : (Int,Nat)
test = (0,0)

total
test2 : (Void,Nat)
test2 = (?x,0)

data TT : Type where
  MkTT : TT

data TF : Type where

test3 : TF
test3 = ?x1

test4 : (TT, TT)
test4 = (MkTT, MkTT)

test5 : (TF, TT)
test5 = (?test5_rhs_1, MkTT)

test6 : (,) Nat Nat
test6 = (3,3)

data Sx : Nat -> Type where
  MkSx : Sx n

test7 : (x : Nat ** Sx x)
test7 = (3 ** MkSx)

test8 : DPair Nat (\x => Sx x)
test8 = MkDPair 3 MkSx

-- test8 : Sigma Nat (\x => Sx x)
-- test8 = MkSigma 3 MkSx
