module PLFI.Part1.Equality

import Syntax.PreorderReasoning

data Equal0 : {t : Type} -> (x : t) -> t -> Type where
  Refl0 : Equal0 x x

{-
public export
data Equal : forall a, b . a -> b -> Type where
     [search a b]
     Refl : {0 x : a} -> Equal x x
-}

%hide sym
%hide trans
%hide cong

sym : {A : Type} -> {x, y : A} ->
    x = y ->
  ----------
    y = x
sym Refl = Refl

trans : {A : Type} -> {x,y,z : A} ->
    x = y ->
    y = z ->
  ----------
    x = z
trans Refl Refl = Refl

cong : {A, B : Type} -> (f : A -> B) -> {x, y : A} ->
    x = y  ->
  -----------
   f x = f y
cong f Refl = Refl

congApp : {A, B : Type} -> {f, g : A -> B} ->
           f = g      ->
    --------------------
    forall x . f x = g x
congApp Refl = Refl

subst : {A : Type} -> {x, y : A} -> (P : A -> Type) ->
  x = y   ->
  ----------
  P x -> P y
subst p Refl = \z => z

-- Chain of equations

{-
||| Until Idris2 starts supporting the 'syntax' keyword, here's a
||| poor-man's equational reasoning
module Syntax.PreorderReasoning

infixl 0  ~~
prefix 1  |~
infix  1  ...

|||Slightly nicer syntax for justifying equations:
|||```
||| |~ a
||| ~~ b ...( justification )
|||```
|||and we can think of the `...( justification )` as ASCII art for a thought bubble.
public export
data Step : a -> b -> Type where
  (...) : (0 y : a) -> (0 step : x ~=~ y) -> Step x y

public export
data FastDerivation : (x : a) -> (y : b) -> Type where
  (|~) : (0 x : a) -> FastDerivation x x
  (~~) : FastDerivation x y -> (step : Step y z) -> FastDerivation x z

public export
Calc : {0 x : a} -> {0 y : b} -> FastDerivation x y -> x ~=~ y
Calc (|~ x) = Refl
Calc ((~~) der (_ ...(Refl))) = Calc der

-- requires import Data.Nat
0
example : (x : Nat) -> (x + 1) + 0 = 1 + x
example x =
  Calc $
   |~ (x + 1) + 0
   ~~ x+1  ...( plusZeroRightNeutral $ x + 1 )
   ~~ 1+x  ...( plusCommutative x 1          )

-}

trans' : {a : Type} -> {x,y,z : a} ->
  x = y ->
  y = z ->
  --------
  x = z
trans' {a,x,y,z} xy yz =
  Calc $
    |~ x
    ~~ y ... ( xy )
    ~~ z ... ( yz )

-- Chain of equations another example

plusIdentity : forall m . m + Z = m
plusSucc     : forall m . forall n . m + S n = S (m + n)

plusComm : (m, n : Nat) -> m + n = n + m
plusComm m 0 = Calc $
  |~ m + Z
  ~~ m     ... (plusIdentity)
plusComm m (S k) = Calc $
  |~ m + (S k)
  ~~ S (m + k) ... (plusSucc)
  ~~ S (k + m) ... (cong S (plusComm m k))
  ~~ (S k) + m ... (Refl)

-- Exercise LTE-Reasoning (strech)

-- Rewriting

