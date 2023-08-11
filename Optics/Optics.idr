module Optics.Optics

import Syntax.PreorderReasoning

interface Profunctor (p : Type -> Type -> Type) where
  dimap : (a' -> a) -> (b -> b') -> p a b -> p a' b'

-- -- TODO: Profunctor laws
-- record ProfunctorLaws where
--   constructor MkProfunctorLaws
--   pro : (Type -> Type -> Type)
--   ins : Profunctor pro
--   dimapId : (px : pro a b) -> dimap Prelude.id Prelude.id px === px

interface Profunctor p => Cartesian p where
  constructor MkCartesian
  first  : p a b -> p (a,c) (b,c)
  second : p a b -> p (c,a) (c,b)

Profunctor (\a , b => a -> b) where
  dimap f g h = g . h . f

Optic : (Type -> Type -> Type) -> Type -> Type -> Type -> Type -> Type
Optic p a b s t = p a b -> p s t

record LensC (a,b,s,t : Type) where
  constructor MkLensC
  view   : s -> a
  update : (b,s) -> t

LensP : Type -> Type -> Type -> Type -> Type
LensP a b s t = {p : _} -> (Cartesian p) => Optic p a b s t

LensP' : Type -> Type -> Type -> Type -> Type
LensP' a b s t = (p : _) -> (Cartesian p) -> Optic p a b s t

{a,b : Type} -> 
Profunctor (LensC a b) where
  dimap f g (MkLensC view update) =
    MkLensC
      { view   = view . f
      , update = \(x,y) => g (update (x, f y))
      }

{a,b : Type} -> 
Cartesian (LensC a b) where
  first (MkLensC view update) =
    MkLensC
      { view   = view . fst
      , update = \(x,(y,z)) => (update (x, y), z)
      }
  second (MkLensC view update) =
    MkLensC
      { view   = view . snd
      , update = \(x,(y,z)) => (y, update (x, z))
      }

cartesianLens : {a,b : Type} -> (Cartesian (LensC a b))
cartesianLens = %search

lensC2P : {a,b,s,t : Type} -> LensC a b s t -> LensP a b s t
lensC2P (MkLensC view update) = dimap (\x => (view x,x)) update . first

lensC2P' : {a,b,s,t : Type} -> LensC a b s t -> LensP' a b s t
lensC2P' (MkLensC view update) p cp = dimap (\x => (view x,x)) update . first

lensP2C : {a,b,s,t : Type} -> LensP a b s t -> LensC a b s t
lensP2C f = f (MkLensC id fst)

lensP2C' : {a,b,s,t : Type} -> LensP' a b s t -> LensC a b s t
lensP2C' f = f (LensC a b) cartesianLens (MkLensC id fst)


funExt : {0 a,b : Type} -> {0 f,g : a -> b} -> ((x : a) -> (f x === g x)) -> (f === g)
funExt = ?todo1



viewLemma : (c : LensC a b s t) -> view (lensP2C (lensC2P c)) === view c
viewLemma (MkLensC view update) = Refl

updateLemma : (c : LensC a b s t) -> update (lensP2C (lensC2P c)) === update c
updateLemma (MkLensC view update) = funExt $ \(x,y) => Refl

lensLemma : (v === v') -> (u === u') -> (MkLensC v u) === (MkLensC v' u')
lensLemma Refl Refl = Refl

proof1 : (l : LensC a b s t) -> lensP2C (lensC2P l) === l
proof1 (MkLensC view update) =
  lensLemma
    (viewLemma (MkLensC view update))
    (updateLemma (MkLensC view update))

-- proof3
--   :  (l : LensP a b s t)
--   -> ({p : Type -> Type -> Type} -> (Cartesian p) => lensC2P (lensP2C l) {p} === l {p})
-- proof3 l = ?goal3

funExtDep :
  {0 a : Type}                ->
  {0 b : a -> Type}           ->
  {0 f,g : (y : a) -> b y}    ->
  ((x : a) -> (f x === g x))  ->
  ------------------------------
          (f === g)
funExtDep = ?todo2

proof2
  :  (l : LensP' a b s t)
  -> lensC2P' (lensP2C' l) === l
proof2 l = funExtDep $ \p => funExtDep $ \cp => funExt $ \k => Calc $
  |~ lensC2P' (lensP2C' l) p cp k
  ~~ lensC2P' (l (LensC a b) cartesianLens (MkLensC id fst)) p cp k ... (Refl)
  ~~ flip (\x => lensC2P' x p cp) k (l (LensC a b) cartesianLens (MkLensC id fst)) ... (Refl)

  -- ~~ l p cp (flip lensC2P' k (MkLensC id fst))
  --   ... (?g4)
  -- ~~ l p cp (lensC2P' (MkLensC id fst) k)
  --   ... (?g3)
  -- ~~ l p cp (dimap (fork (id,id)) fst (first k))
  --   ... (?g2)
  ~~ l p cp k
    ... (?g1)

-- k ~~ p a b
-- lensC2P (lensP2C l) k
-- = [[ lensP2C ]]
-- lensC2P (l (Lens id fst)) k
-- = [[ flip ]]
-- flip lensC2P k (l (Lens id fst))
-- = [[ free theorem of l, and Lemma 9 ]]
-- l (flip lensC2P k (Lens id fst))
-- = [[ flip ]]
-- l (lensC2P (Lens id fst) k)
-- = [[ lensC2P ]]
-- l (dimap (fork (id,id)) fst (first k))
-- = [[ Lemma 10 ]]
-- l k

-- Theorem 2. The functions lensC2P and lensP2C are each other’s inverses, and so the
-- types Lens A B S T and LensP A B S T are isomorphic for all type parameters A,B, S,T.

-- proof1
-- dimap f g (flip lensC2P k (Lens v u))
-- = [[ flip ]]
-- dimap f g (lensC2P (Lens v u) k)
-- = [[ lensC2P ]]
-- dimap f g (dimap (fork (v,id)) u (first k))
-- = [[ dimap composition ]]
-- dimap (fork (v,id)· f) (g · u) (first k)
-- = [[ products and fork ]]
-- dimap (cross (id,f)· fork (v · f,id)) (g · u) (first k)
-- = [[ dimap composition ]]
-- dimap (fork (v · f,id)) (g · u) (dimap (cross (id,f)) id (first k))
-- = [[ free theorem of first (Lemma 8), with g = id, h = id, and k = l ]]
-- dimap (fork (v · f,id)) (g · u) (dimap id (cross (id,f)) (first k))
-- = [[ dimap composition ]]
-- dimap (fork (v · f,id)) (g · u ·cross (id,f)) (first k)
-- = [[ lensC2P ]]
-- lensC2P (Lens (v · f) (g · u ·cross (id,f))) k
-- = [[ dimap for Lens ]]
-- lensC2P (dimap f g (Lens v u)) k
-- = [[ flip ]]
-- flip lensC2P k (dimap f g (Lens v u))

{-
lensC2P'
  (l (LensC a b)
     (Cartesian
        (\0 c, 0 b', 0 a', arg => first arg)
        (\0 c, 0 b', 0 a', arg => second arg))
     (MkLensC id fst))
    p cp pab
  ===
  l p cp pab
-}
{-
 0 t : Type
 0 s : Type
 0 b : Type
 0 a : Type
   l : (p : (Type -> Type -> Type)) -> Cartesian p -> p a b -> p s t
------------------------------
goal3 : lensC2P' (l (LensC a b) (Cartesian at Optics.Optics:15:1--17:34 (\0 c, 0 b', 0 a', arg => first arg) (\0 c, 0 b', 0 a', arg => second arg)) (MkLensC id fst)) = l
-}

