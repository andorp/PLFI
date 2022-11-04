module PLFI.Part1.Lists

import Syntax.PreorderReasoning

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
