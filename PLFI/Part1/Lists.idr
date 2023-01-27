module PLFI.Part1.Lists

import Syntax.PreorderReasoning
import PLFI.Part1.Induction

infixl 0 ~=
public export
(~=) : FastDerivation x y -> (0 z : dom) -> {auto xEqy : y = z} -> FastDerivation x z
(~=) deriv y {xEqy} = deriv ~~ y ...(xEqy) -- Beats writing ...(Refl) time and time again

data L : Type -> Type where
  Nil  : L a
  Cons : a -> L a -> L a

(++) : L a -> L a -> L a
Nil       ++ ys = ys
Cons x xs ++ ys = Cons x (xs ++ ys)

appendAssoc : (xs,ys,zs : L a) -> (xs ++ ys) ++ zs === xs ++ (ys ++ zs)
appendAssoc [] ys zs = Calc $
  |~ ([] ++ ys) ++ zs
  ~= (ys ++ zs)      
  ~= [] ++ (ys ++ zs)
appendAssoc (Cons x xs) ys zs = Calc $
  |~ Cons x ((xs ++ ys) ++ zs)
  ~~ Cons x (xs ++ (ys ++ zs)) ... (cong (Cons x) (appendAssoc xs ys zs))

appendIdentityLeft : (xs : L a) -> Nil ++ xs === xs
appendIdentityLeft Nil = Calc $
  |~ Nil ++ Nil 
  ~= Nil       
appendIdentityLeft (Cons x xs) = Calc $
  |~ [] ++ (Cons x xs)
  ~= Cons x xs

appendIdentityRight : (xs : L a) -> xs ++ Nil === xs
appendIdentityRight Nil = Calc $
  |~ Nil ++ Nil
  ~= Nil       
appendIdentityRight (Cons x xs) = Calc $
  |~ Cons x (xs ++ Nil)
  ~~ Cons x xs         ... (cong (Cons x) (appendIdentityRight xs))

length : L a -> Nat
length []          = 0
length (Cons x xs) = S (length xs)

lengthAppend : (xs, ys : L a) -> length (xs ++ ys) === length xs + length ys
lengthAppend Nil ys = Calc $
  |~ length (Nil ++ ys)
  ~~ length ys         ... (cong length (appendIdentityLeft ys))
lengthAppend (Cons x xs) ys = Calc $
  |~ length ((Cons x xs) ++ ys)
  ~= length (Cons x (xs ++ ys))
  ~= S (length (xs ++ ys))     
  ~~ S (length xs + length ys)      ... (cong S (lengthAppend xs ys))
  ~= length (Cons x xs) + length ys

reverse : L a -> L a
reverse Nil = Nil
reverse (Cons x xs) = reverse xs ++ (Cons x Nil)

reverseAppendDistrib : (xs, ys : L a) -> reverse (xs ++ ys) === reverse ys ++ reverse xs
reverseAppendDistrib [] ys = Calc $
  |~ (reverse ([] ++ ys))
  ~~ (reverse ys)               ... (cong reverse (appendIdentityLeft ys))
  ~~ (reverse ys ++ [])         ... (sym (appendIdentityRight (reverse ys)))
  ~= (reverse ys ++ reverse [])
reverseAppendDistrib (Cons x xs) ys = Calc $
  |~ (reverse (Cons x xs ++ ys))
  ~= (reverse (xs ++ ys) ++ Cons x [])         
  ~~ ((reverse ys ++ reverse xs) ++ Cons x []) ... (cong (\y => y ++ Cons x []) (reverseAppendDistrib xs ys))
  ~~ (reverse ys ++ (reverse xs ++ Cons x [])) ... (appendAssoc (reverse ys) (reverse xs) (Cons x []))
  ~= (reverse ys ++ (reverse (Cons x xs)))     

reverseInvolutive : (xs : L a) -> reverse (reverse xs) === xs
reverseInvolutive [] = Calc $
  |~ reverse (reverse [])
  ~= reverse []           
  ~= []                   
reverseInvolutive (Cons x y) = Calc $
  |~ reverse (reverse (Cons x y))
  ~= reverse (reverse y ++ Cons x [])
  ~~ reverse (Cons x []) ++ reverse (reverse y) ... (reverseAppendDistrib (reverse y) (Cons x []))
  ~= (reverse [] ++ Cons x []) ++ reverse (reverse y)
  ~= ([] ++ Cons x []) ++ (reverse (reverse y))
  ~= Cons x [] ++ (reverse (reverse y))
  ~~ Cons x [] ++ y ... (cong (Cons x [] ++) (reverseInvolutive y))
  ~= Cons x ([] ++ y)
  ~= Cons x y

shunt : L a -> L a -> L a
shunt []          ys = ys
shunt (Cons x xs) ys = shunt xs (Cons x ys)

shuntReverse : (xs, ys : L a) -> shunt xs ys === reverse xs ++ ys
shuntReverse [] ys = Calc $
  |~ shunt [] ys
  ~= ys
  ~= [] ++ ys
  ~= reverse [] ++ ys
shuntReverse (Cons x xs) ys = Calc $
  |~ shunt (Cons x xs) ys
  ~= shunt xs (Cons x ys)
  ~~ reverse xs ++ Cons x ys ... (shuntReverse xs (Cons x ys))
  ~= reverse xs ++ (Cons x [] ++ ys)
  ~~ (reverse xs ++ Cons x []) ++ ys ... (sym (appendAssoc (reverse xs) (Cons x []) ys))
  ~= (reverse (Cons x xs) ++ ys)

reverse2 : {a : Type} -> L a -> L a
reverse2 xs = shunt xs []

reverses : {a : Type} -> (xs : L a) -> reverse2 xs === reverse xs
reverses xs = Calc $
  |~ reverse2 xs
  ~= shunt xs []      -- Refl
  ~~ reverse xs ++ [] ... (shuntReverse xs [])
  ~~ reverse xs       ... (appendIdentityRight (reverse xs))

map : (a -> b) -> L a -> L b
map f [] = []
map f (Cons x y) = Cons (f x) (map f y)

-- map (g ∘ f) ≡ map g ∘ map f

mapCompose : (xs : L a) -> {0 f : a -> b} -> {0 g : b -> c} -> map (g . f) xs === map g (map f xs)
mapCompose [] = Calc $
  |~ map (g . f) []
  ~= []
  ~= map g []
  ~= map g (map f [])
mapCompose (Cons x xs) = Calc $
  |~ map (g . f) (Cons x xs)
  ~= Cons ((g . f) x) (map (g . f) xs)
  ~= Cons (g (f x)) (map (g . f) xs)
  ~~ Cons (g (f x)) (map g (map f xs)) ... (cong (Cons (g (f x))) (mapCompose xs))
  ~= map g (Cons (f x) (map f xs))
  ~= map g (map f (Cons x xs))

-- map f (xs ++ ys) ≡ map f xs ++ map f ys
mapAppendDistribute : (xs, ys : L a) -> {0 f : a -> b} -> map f (xs ++ ys) === map f xs ++ map f ys
mapAppendDistribute [] ys = Calc $
  |~ map f ([] ++ ys)
  ~= map f ys
  ~= [] ++ map f ys
  ~= map f [] ++ map f ys
mapAppendDistribute (Cons x xs) ys = Calc $
  |~ map f (Cons x xs ++ ys)
  ~= map f (Cons x (xs ++ ys))
  ~= Cons (f x) (map f (xs ++ ys))
  ~~ Cons (f x) (map f xs ++ map f ys) ... (cong (Cons (f x)) (mapAppendDistribute xs ys))
  ~= (Cons (f x) (map f xs)) ++ map f ys
  ~= map f (Cons x xs) ++ map f ys

foldr : (a -> b -> b) -> b -> L a -> b
foldr cons nil Nil         = nil
foldr cons nil (Cons x xs) = cons x (foldr cons nil xs)

appendFoldR : (xs, ys : L a) -> xs ++ ys === foldr Cons ys xs
appendFoldR [] ys = Calc $
  |~ [] ++ ys
  ~= ys
  ~= foldr Cons ys []
appendFoldR (Cons x xs) ys = Calc $
  |~ (Cons x xs) ++ ys
  ~= Cons x (xs ++ ys)
  ~~ Cons x (foldr Cons ys xs) ... (cong (Cons x) (appendFoldR xs ys))
  ~= foldr Cons ys (Cons x xs)

foldRAppend
  :  (xs, ys : L a)
  -> {0 f : a -> b -> b} -> {0 e : b}
  -> foldr f e (xs ++ ys) === foldr f (foldr f e ys) xs
foldRAppend [] ys = Calc $ 
  |~ foldr f e ([] ++ ys) 
  ~= foldr f e ys
  ~= foldr f (foldr f e ys) []
foldRAppend (Cons x xs) ys = Calc $
  |~ foldr f e ((Cons x xs) ++ ys)
  ~= foldr f e (Cons x (xs ++ ys))
  ~= f x (foldr f e (xs ++ ys))
  ~~ f x (foldr f (foldr f e ys) xs)    ... (cong (f x) (foldRAppend xs ys))
  ~= foldr f (foldr f e ys) (Cons x xs)

foldrEmptyUgly : (xs : L a) -> foldr Cons [] xs === xs
foldrEmptyUgly xs = (sym (appendFoldR xs [])) `trans` (appendIdentityRight xs)

foldrEmptyPretty : (xs : L a) -> foldr Cons [] xs === xs
foldrEmptyPretty xs = Calc $
  |~ foldr Cons [] xs
  ~~ (xs ++ []) ... (sym (appendFoldR xs []))
  ~~ xs         ... (appendIdentityRight xs)

-- map f ≡ foldr (λ x xs → f x ∷ xs) []
mapIsFoldr : (xs : L a) -> {f : a -> b} -> map f xs === foldr (\x , ys => Cons (f x) ys) [] xs
mapIsFoldr [] = Calc $
  |~ map f []
  ~= []
  ~= foldr (\x , ys => Cons (f x) ys) [] []
mapIsFoldr (Cons x xs) = Calc $
  |~ map f (Cons x xs)
  ~= Cons (f x) (map f xs)
  ~~ Cons (f x) (foldr (\x , ys => Cons (f x) ys) [] xs) ... (cong (Cons (f x)) (mapIsFoldr xs))
  ~= foldr (\x , ys => Cons (f x) ys) [] (Cons x xs)

{-
record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid
-}

record IsMonoid {a : Type} (append : a -> a -> a) (e : a) where
  constructor MkMonoid
  assoc     : (x,y,z : a) -> append (append x y) z === append x (append y z)
  identityL : (x : a) -> append e x === x
  identityR : (x : a) -> append x e === x


-- Report issues with this:
-- infixl 9 <>
-- data IsMonoidI : {a : Type} -> (append : a -> a -> a) -> (e : a) -> Type where
--   MkMonoidI
--     :  {(<>) : a -> a -> a} -> {e : a}
--     -> (assoc : (x,y,z : a) -> (x <> y) <> z === x <> (y <> z))
--     -> IsMonoidI (++) e

data IsMonoidI : {a : Type} -> (a -> a -> a) -> a -> Type where
  MkMonoidI
--    :  {app : a -> a -> a} -> {e : a}
    :  (assoc : (x,y,z : a) -> ((x `app` y) `app` z) === (x `app` (y `app` z)))
    -> (identityL : (x : a) -> (e `app` x) === x)
    -> (identityR : (x : a) -> (x `app` e) === x)
    -> IsMonoidI app e

plusMonoid : IsMonoid {a = N} Naturals.(+) 0
plusMonoid = MkMonoid
  { assoc     = addAssoc    
  , identityL = \x => Refl
  , identityR = addIdentityRWithRewrite
  }

-- foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
--   ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y

foldrMonoid
  :  {a : Type} -> (app : a -> a -> a) -> (e : a) -> IsMonoid app e
  -> (xs : L a) -> (y : a) -> (foldr app y xs) === (app (foldr app e xs) y)
foldrMonoid app e m Nil y = Calc $
  |~ foldr app y []
  ~= y
  ~~ (e `app` y)                ... (sym (m.identityL y))
  ~= ((foldr app e []) `app` y)
foldrMonoid app e m (Cons x xs) y = Calc $
  |~ foldr app y (Cons x xs)
  ~= app x (foldr app y xs)
  ~~ app x (foldr app e xs `app` y)      ... (cong (app x) (foldrMonoid app e m xs y))
  ~~ ((app x (foldr app e xs)) `app` y)  ... (sym (m.assoc x (foldr app e xs) y))
  ~= ((foldr app e (Cons x xs)) `app` y)

-- foldrMonoidAppend
--   :  {a : Type} -> (app : a -> a -> a) -> (e : a) -> IsMonoid app e
--   -> (xs, ys : L a) -> (foldr app e (xs ++ ys)) === (foldr app e xs `app` foldr app e ys)
-- foldrMonoidAppend app e m xs ys = Calc $
--   |~ foldr app e (xs ++ ys) 
--   ~~ foldr app (foldr app e ys) xs         ... (foldRAppend xs ys)
--   ~~ (foldr app e xs `app` foldr app e ys) ... (foldrMonoid app e m xs (foldr app e ys))

-- ⨂ U+2A02	N-Ary Circled Times Operator

foldrMonoidAppend
  :  {a : Type} -> (⨂ : a -> a -> a) -> (e : a) -> IsMonoid ⨂ e
  -> (xs, ys : L a) -> (foldr ⨂ e (xs ++ ys)) === ((foldr ⨂ e xs) `⨂` (foldr ⨂ e ys))
foldrMonoidAppend a⨂ e m xs ys = Calc $
  |~ foldr a⨂ e (xs ++ ys) 
  ~~ foldr a⨂ (foldr a⨂ e ys) xs         ... (foldRAppend xs ys)
  ~~ (foldr a⨂ e xs `a⨂` foldr a⨂ e ys) ... (foldrMonoid a⨂ e m xs (foldr a⨂ e ys))


foldl : (b -> a -> b) -> b -> L a -> b
foldl snoc nil Nil         = nil
foldl snoc nil (Cons x xs) = foldl snoc (snoc nil x) xs

foldr⨉monoid⨉foldl
  :  {a : Type} -> (⨂ : a -> a -> a) -> (e : a) -> IsMonoid ⨂ e -> (xs : L a)
  -> (foldr ⨂ e xs === foldl ⨂ e xs)
foldr⨉monoid⨉foldl a⨂ e m [] = ?todo_0
foldr⨉monoid⨉foldl a⨂ e m (Cons x y) = ?todo_1





