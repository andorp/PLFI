module PLFI.Part1.Isomorphism

import Data.Nat
import Data.Vect
import Syntax.PreorderReasoning

0
handwaving : {t : Type} -> (a : t) -> (b : t) -> (a = b)
handwaving a b = believe_me (the (a=a) Refl)

namespace Postulate

  export 0
  extensionality : {a,b : Type} -> {f,g : a -> b} -> ((x : a) -> f x = g x) -> f = g
  extensionality _ = handwaving f g

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

-- infix 0 _≃_
-- record _≃_ (A B : Set) : Set where
--   field
--     to   : A → B
--     from : B → A
--     from∘to : ∀ (x : A) → from (to x) ≡ x
--     to∘from : ∀ (y : B) → to (from y) ≡ y
-- open _≃_

record Iso (a, b : Type) where
  constructor MkIso
  to     : a -> b
  from   : b -> a
  fromTo : (x : a) -> from (to x) = x
  toFrom : (y : b) -> to (from y) = y

-- interface IsoI a b where
--   toI   : a -> b
--   fromI : b -> a
--   fromToI : (x : a) -> fromI (toI x) = x
--   toFromI : (y : b) -> toI (fromI y) = y

-- ≃-refl : ∀ {A : Set}
--     -----
--   → A ≃ A
-- ≃-refl =
--   record
--     { to      = λ{x → x}
--     ; from    = λ{y → y}
--     ; from∘to = λ{x → refl}
--     ; to∘from = λ{y → refl}
--     }

isoRefl : {a : Type} -> Iso a a
isoRefl = MkIso
  { to     = id
  , from   = id
  , fromTo = \x => Refl
  , toFrom = \x => Refl
  }

isoTo : Iso a b -> (a -> b)
isoTo i = i.to


-- ≃-sym : ∀ {A B : Set}
--   → A ≃ B
--     -----
--   → B ≃ A
-- ≃-sym A≃B =
--   record
--     { to      = from A≃B
--     ; from    = to   A≃B
--     ; from∘to = to∘from A≃B
--     ; to∘from = from∘to A≃B
--     }

isoSym : Iso a b -> Iso b a
isoSym (MkIso to from fromTo toFrom) = MkIso from to toFrom fromTo


-- ≃-trans : ∀ {A B C : Set}
--   → A ≃ B
--   → B ≃ C
--     -----
--   → A ≃ C
-- ≃-trans A≃B B≃C =
--   record
--     { to       = to   B≃C ∘ to   A≃B
--     ; from     = from A≃B ∘ from B≃C
--     ; from∘to  = λ{x →
--         begin
--           (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x)
--         ≡⟨⟩
--           from A≃B (from B≃C (to B≃C (to A≃B x)))
--         ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
--           from A≃B (to A≃B x)
--         ≡⟨ from∘to A≃B x ⟩
--           x
--         ∎}
--     ; to∘from = λ{y →
--         begin
--           (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) y)
--         ≡⟨⟩
--           to B≃C (to A≃B (from A≃B (from B≃C y)))
--         ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
--           to B≃C (from B≃C y)
--         ≡⟨ to∘from B≃C y ⟩
--           y
--         ∎}
--      }

isoTrans : {a,b,c : Type} -> Iso a b -> Iso b c -> Iso a c
isoTrans ab bc = MkIso
  { to     = to bc . to ab
  , from   = from ab . from bc
  , fromTo = \x => Calc $
      |~ (from ab . from bc) ((to bc . to ab) x)
      -- ~~ (from ab . from bc) (to bc (to ab x))  ... (Refl)
      -- ~~ (from ab (from bc (to bc (to ab x))))  ... (Refl)
      ~~ (from ab (to ab x))                    ... (cong ab.from (bc.fromTo (ab.to x)))
      ~~ x                                      ... (ab.fromTo x)
  , toFrom = \y => rewrite ab.toFrom (bc.from y) in bc.toFrom y
--  , toFrom = \y => (?x (bc.toFrom y))
                    -- rewriteP (ab.toFrom (bc.from y)) (bc.toFrom y)

                    -- rewriteP : a = b -> P a -> P b
                    -- rewriteP Refl pa = pa
  }

