module PLFI.Part1.Isomorphism

import Data.Nat
import Data.Vect

0
handwaving : {t : Type} -> (a : t) -> (b : t) -> (a = b)
handwaving a b = believe_me (the (a=a) Refl)

namespace Postulate

  export 0
  extensionality : {a,b : Type} -> {f,g : a -> b} -> ((x : a) -> f x = g x) -> f = g
  extensionality fg = handwaving f g

addX : (m,n : Nat) -> Nat
addX m Z = m
addX m (S n) = S (addX m n)

sameAdd : (m, n : Nat) -> addX m n = m + n
sameAdd m n = rewrite plusCommutative m n in helper m n
  where
    helper : (m, n : Nat) -> addX m n = n + m
    helper m 0     = Refl
    helper m (S n) = cong S (helper m n)

add : Nat -> Nat -> Nat
add = (+)

0
same : Isomorphism.addX = Isomorphism.add
same = extensionality (\p => extensionality (\q => sameAdd p q))

namespace Things

  interesting1 : (x : Nat) -> (y : Nat) -> Nat
  interesting1 x y = x + y

  interesting2 : Nat
  interesting2 = interesting1 {y=2} {x=1}
