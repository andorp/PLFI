module Optics.Optics

interface Profunctor (p : Type -> Type -> Type) where
  dimap : (a' -> a) -> (b -> b') -> p a b -> p a' b'

-- TODO: Profunctor laws
record ProfunctorLaws where
  constructor MkProfunctorLaws
  pro : (Type -> Type -> Type)
  ins : Profunctor pro
  dimapId : (px : pro a b) -> dimap Prelude.id Prelude.id px === px

interface Profunctor p => Cartesian p where
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

lensC2P : {a,b,s,t : Type} -> LensC a b s t -> LensP a b s t
lensC2P (MkLensC view update) = dimap (\x => (view x,x)) update . first

lensP2C : {a,b,s,t : Type} -> LensP a b s t -> LensC a b s t
lensP2C f = f (MkLensC id fst)

funExt : {a,b : Type} -> {f,g : a -> b} -> ((x : a) -> (f x === g x)) -> (f === g)
funExt = ?todo1

proof1 : (c : LensC a b s t) -> lensP2C (lensC2P c) === c
proof1 (MkLensC view update) = ?todo_0
