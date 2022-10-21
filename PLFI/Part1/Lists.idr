module PLFI.Part1.Lists

import Syntax.PreorderReasoning


data L : Type -> Type where
  Nil  : L a
  Cons : a -> L a -> L a

(++) : L a -> L a -> L a
Nil       ++ ys = ys
Cons x xs ++ ys = Cons x (xs ++ ys)

appendAssoc : (xs,ys,zs : L a) -> (xs ++ ys) ++ zs === xs ++ (ys ++ zs)
appendAssoc [] ys zs = Calc $
  |~ ([] ++ ys) ++ zs
  ~~ (ys ++ zs)        ... (Refl)
  ~~ [] ++ (ys ++ zs)  ... (Refl)
appendAssoc (Cons x xs) ys zs = Calc $
  |~ Cons x ((xs ++ ys) ++ zs)
  ~~ Cons x (xs ++ (ys ++ zs)) ... (cong (Cons x) (appendAssoc xs ys zs))

appendIdentityLeft : (xs : L a) -> Nil ++ xs === xs
appendIdentityLeft Nil = Calc $
  |~ Nil ++ Nil 
  ~~ Nil       ... (Refl)
appendIdentityLeft (Cons x xs) = Calc $
  |~ [] ++ (Cons x xs)
  ~~ Cons x xs ... (Refl)

appendIdentityRight : (xs : L a) -> xs ++ Nil === xs
appendIdentityRight Nil = Calc $
  |~ Nil ++ Nil
  ~~ Nil       ... (Refl)
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
  ~~ length (Cons x (xs ++ ys))     ... (Refl)
  ~~ S (length (xs ++ ys))          ... (Refl)
  ~~ S (length xs + length ys)      ... (cong S (lengthAppend xs ys))
  ~~ length (Cons x xs) + length ys ... (Refl)

reverse : L a -> L a
reverse Nil = Nil
reverse (Cons x xs) = reverse xs ++ (Cons x Nil)

reverseAppendDistrib : (xs, ys : L a) -> reverse (xs ++ ys) === reverse ys ++ reverse xs
reverseAppendDistrib [] ys = Calc $
  |~ (reverse ([] ++ ys))
  ~~ (reverse ys)               ... (cong reverse (appendIdentityLeft ys))
  ~~ (reverse ys ++ [])         ... (sym (appendIdentityRight (reverse ys)))
  ~~ (reverse ys ++ reverse []) ... (Refl)
reverseAppendDistrib (Cons x xs) ys = Calc $
  |~ (reverse (Cons x xs ++ ys))
  ~~ (reverse (xs ++ ys) ++ Cons x [])         ... (Refl)
  ~~ ((reverse ys ++ reverse xs) ++ Cons x []) ... (cong (\y => y ++ Cons x []) (reverseAppendDistrib xs ys))
  ~~ (reverse ys ++ (reverse xs ++ Cons x [])) ... (appendAssoc (reverse ys) (reverse xs) (Cons x []))
  ~~ (reverse ys ++ (reverse (Cons x xs)))     ... (Refl)
