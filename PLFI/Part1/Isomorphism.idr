module PLFI.Part1.Isomorphism

import Data.Nat
import Data.Vect
import Syntax.PreorderReasoning
import Syntax.PreorderReasoning.Generic
import Control.Order
import Control.Relation

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
  fromTo : (x : a) -> from (to x) === x
  toFrom : (y : b) -> to (from y) === y

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

-- module ≃-Reasoning where

--   infix  1 ≃-begin_
--   infixr 2 _≃⟨_⟩_
--   infix  3 _≃-∎

--   ≃-begin_ : ∀ {A B : Set}
--     → A ≃ B
--       -----
--     → A ≃ B
--   ≃-begin A≃B = A≃B

--   _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
--     → A ≃ B
--     → B ≃ C
--       -----
--     → A ≃ C
--   A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

--   _≃-∎ : ∀ (A : Set)
--       -----
--     → A ≃ A
--   A ≃-∎ = ≃-refl

-- open ≃-Reasoning

Reflexive  Type Iso where reflexive = isoRefl
Transitive Type Iso where transitive = isoTrans
Preorder   Type Iso where

(~~~) : (a, b : Type) -> Type
(~~~) a b = Iso a b

-- 0
test : {a,b,c : Type} -> Iso a b -> Iso b c -> Iso a c
test ab bc = CalcWith {leq = Iso} $
  |~ a
  <~ b ... (ab)
  <~ c ... (bc)

-- [additive] Semigroup Nat where
--   a <+> b = ?h

-- [multiplicative] Semigroup Nat where
--   a <+> b = ?h2

-- infix 0 _≲_
-- record _≲_ (A B : Set) : Set where
--   field
--     to      : A → B
--     from    : B → A
--     from∘to : ∀ (x : A) → from (to x) ≡ x
-- open _≲_

-- infixr 100 <=

-- %hint -- Would be nice to have
record (<=) (a, b : Type) where
  constructor MkEmb
  to     : a -> b
  from   : b -> a
  -- %hint : Would be nice to have
  fromTo : (x : a) -> from (to x) === x

%hint
fromToX : (ab : (a <= b)) -> (x : a) -> ab.from (ab.to x) === x
fromToX ab x = ab.fromTo x

-- %hint (.to)

-- (<=) : (a,b : Type) -> Type
-- (<=) a b = Emb a b

-- -- A deep question from the audience. :)
-- embIso : {a,b : Type} -> a <= b -> b <= a -> (Iso a b)
-- embIso = ?xembIso

embRefl : {a : Type} -> a <= a
embRefl = MkEmb Prelude.id Prelude.id (\x => Refl)

-- ≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
-- ≲-trans A≲B B≲C =
--   record
--     { to      = λ{x → to   B≲C (to   A≲B x)}
--     ; from    = λ{y → from A≲B (from B≲C y)}
--     ; from∘to = λ{x →
--         begin
--           from A≲B (from B≲C (to B≲C (to A≲B x)))
--         ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
--           from A≲B (to A≲B x)
--         ≡⟨ from∘to A≲B x ⟩
--           x
--         ∎}
--      }

embTrans : {a,b,c : Type} -> a <= b -> b <= c -> a <= c
embTrans ab bc = MkEmb
  { to   = (bc.to . ab.to)
  , from = (ab.from . bc.from)
  , fromTo = \x => Calc $
      |~ ab.from (bc.from (bc.to (ab.to x)))
      ~~ ab.from (ab.to x)
          ... (cong ab.from (bc.fromTo (ab.to x)))
      ~~ x
          ... (ab.fromTo x)
--          ... (fromToX ab x)
  }

--              ab .from (bc .from (bc .to (ab .to x))) = x
--   , toFrom = \y => rewrite ab.toFrom (bc.from y) in bc.toFrom y


-- ≲-antisym : ∀ {A B : Set}
--   → (A≲B : A ≲ B)
--   → (B≲A : B ≲ A)
--   → (to A≲B ≡ from B≲A)
--   → (from A≲B ≡ to B≲A)
--     -------------------
--   → A ≃ B
-- ≲-antisym A≲B B≲A to≡from from≡to =
--   record
--     { to      = to A≲B
--     ; from    = from A≲B
--     ; from∘to = from∘to A≲B
--     ; to∘from = λ{y →
--         begin
--           to A≲B (from A≲B y)
--         ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
--           to A≲B (to B≲A y)
--         ≡⟨ cong-app to≡from (to B≲A y) ⟩
--           from B≲A (to B≲A y)
--         ≡⟨ from∘to B≲A y ⟩
--           y
--         ∎}
--     }

embAntisym
  :  {a,b : Type}
  -> (ab : (a <= b)) -> (ba : (b <= a))
  -> (to ab = from ba) -> (from ab = to ba)
  -> Iso a b
-- embAntisym (MkEmb t f ft) (MkEmb (from (MkEmb t f ft)) (to (MkEmb t f ft)) ft1) Refl Refl
embAntisym (MkEmb t f ft) (MkEmb _ _ ft1) Refl Refl
  = MkIso t f ft ft1

Reflexive  Type (<=) where reflexive = embRefl
Transitive Type (<=) where transitive = embTrans
Preorder   Type (<=) where

embFromIso : {a,b : Type} -> Iso a b -> (a <= b)
-- Issue in internel meta variable
-- embFromIso (MkIso to from fromTo toFrom) = MkEmb (\{arg:2022} => to arg) from fromTo
embFromIso (MkIso to from fromTo toFrom) = MkEmb to from fromTo

-- futumorphism

