module PLFI.Part1.Induction

-- http://plfa.github.io/Induction/

import PLFI.Part1.Naturals
import public Syntax.PreorderReasoning

%hide Prelude.(+)
%hide Prelude.(*)

{-

Proof by induction

 ------
 P Zero

   P m
---------
P (Suc m)

-}

{-
Our first proof: associativity

(m + n) + p = m + (n + p)

-------------------------------
(Zero + n) + p = Zero + (n + p)

   (m + n) + p = m + (n + p)
---------------------------------
(Suc m + n) + p = suc m + (n + p)
-}

-- export
-- addAssoc : (m, n, p : N) -> (m + n) + p = m + (n + p)
-- addAssoc Zero    n p = Refl
-- addAssoc (Suc m) n p = cong Suc $ addAssoc m n p

export
addAssoc : (m, n, p : N) -> (m + n) + p = m + (n + p)
addAssoc Zero n p = Calc $
  |~ (Zero + n) + p
  ~~ n + p             ... (Refl)
  ~~ Zero + (n + p)    ... (Refl)
addAssoc (Suc m) n p = Calc $
  |~ ((Suc m) + n) + p
  ~~ Suc (m + n) + p    ... (Refl)
  ~~ Suc ((m + n) + p)  ... (Refl)
  ~~ Suc (m + (n + p))  ... (cong Suc (addAssoc m n p))
  ~~ Suc m + (n + p)    ... (Refl)

{-
addAssoc : (m, n, p : N) -> (m + n) + p = m + (n + p)
addAssoc Zero n p = Calc $
  |~ ((Zero + n) + p)
  ~~ (n + p)                ...(cong (+p) addEquation1)
  ~~ (Zero + (n + p))       ...(sym addEquation1)
addAssoc (Suc m) n p = Calc $
  |~ ((Suc m + n) + p)
  ~~ (Suc (m + n) + p)
  ~~ (Suc ((m + n) + p))
  ~~ (Suc (m + (n + p)))
  ~~ (Suc m + (n + p))
-}

{-
Our second proof: commutativity
m + n = n + m
-}

{-
The first lemma
m + zero = m
-}

export
addIdentityL : (n : N) -> Zero + n = n
addIdentityL n = Refl

-- addIdentityR1 : (n : N) -> n + Zero = n
-- addIdentityR1 Zero = Refl
-- addIdentityR1 (Suc m) = cong Suc (addIdentityR1 m)

export
addIdentityR : (n : N) -> n + Zero = n
addIdentityR Zero = Calc $
  |~ Zero + Zero
  ~~ Zero         ... (Refl)       
addIdentityR (Suc m) = Calc $
  |~ (Suc m) + Zero
  ~~ Suc (m + Zero) ... (Refl)
  ~~ Suc m          ... (cong Suc (addIdentityR m))


{-
The second lemma
m + suc n = suc (m + n)
-}

export
addSuccL : (m, n : N) -> (Suc m) + n = Suc (m + n)
addSuccL m n = Refl

export
addSucR : (m, n : N) -> m + (Suc n) = Suc (m + n)
addSucR Zero n = Calc $
  |~ Zero + (Suc n)
  ~~ Suc n           ... (Refl)
  ~~ Suc (Zero + n)  ... (Refl)
addSucR (Suc m) n = Calc $
  |~ (Suc m) + (Suc n)
  ~~ Suc (m + Suc n)   ... (Refl)
  ~~ Suc (Suc (m + n)) ... (cong Suc (addSucR m n))
  ~~ Suc ((Suc m) + n) ... (Refl)

{-
The proposition
m + n = n + m
-}

export
addComm : (n, m : N) -> n + m = m + n
addComm Zero    m = sym (addIdentityR m)
addComm (Suc x) m = Calc $
  |~ (Suc x) + m
  ~~ Suc (x + m) ... (Refl)
  ~~ Suc (m + x) ... (cong Suc (addComm x m))
  ~~ m + (Suc x) ... (sym (addSucR m x))

{-
Our first corollary: rearranging
-}

export
addRearrange : (m,n,p,q : N) -> (m + n) + (p + q) = m + (n + p) + q
addRearrange m n p q = Calc $
  |~ (m + n) + (p + q) 
  ~~ m + (n + (p + q)) ... (addAssoc m n (p + q))
  ~~ m + ((n + p) + q) ... (cong (m+) (sym (addAssoc n p q)))
  ~~ (m + (n + p)) + q ... (sym (addAssoc m (n+p) q))
  ~~ m + (n + p) + q   ... (Refl)

-- Vect m Int
-- Vect (S n) Int

-- lemmaForF : n + S m = S (n + m)

-- f : Vect n a -> Vect (S m) a -> Vect (S (n + m)) a
-- f x y = ... (rewrite lemmaForF (... x y))

{-
Associativity with rewrite
addAssocRW : (m + n) + p = m + (n + p)
-}

addAssocWithRewrite : (m,n,p : N) -> (m + n) + p = m + (n + p)
addAssocWithRewrite Zero n p
  = Refl
addAssocWithRewrite (Suc m) n p
  = rewrite (addAssocWithRewrite m n p) in
    Refl

addAssocWithRewriteN : (m,n,p : N) -> (m + n) + p = m + (n + p)
addAssocWithRewriteN m Zero p
  = rewrite (addIdentityR m) in
    Refl
addAssocWithRewriteN m (Suc x) p
  = rewrite (addSucR m x) in
    rewrite (addSucR m (x + p)) in
    rewrite (addAssocWithRewriteN m x p) in
    Refl

addIdentityRWithRewrite : (n : N) -> n + Zero = n
addIdentityRWithRewrite Zero
  = Refl
addIdentityRWithRewrite (Suc m)
  = rewrite (addIdentityRWithRewrite m) in
    Refl

addSucWithRewrite : (m, n : N) -> m + (Suc n) = Suc (m + n)
addSucWithRewrite Zero n
  = Refl
addSucWithRewrite (Suc m) n
  = rewrite (addSucWithRewrite m n) in Refl

addCommWithRewrite : (n, m : N) -> n + m = m + n
addCommWithRewrite Zero m
  = rewrite (addIdentityRWithRewrite m) in
    Refl
addCommWithRewrite (Suc x) m
  = rewrite (addCommWithRewrite x m) in
    rewrite (addSucWithRewrite m x) in
    Refl

-- Exercise (recommended)

swap : (m,n,p : N) -> m + (n + p) = n + (m + p)

-- Exercise (recommended)

multDistribAdd : (m,n,p : N) -> (m + n) * p = m * p + n * p

-- -- Exercise (recommended)

-- multAssoc : (m,n,p : N) -> (m * n) * p = m * (n * p)

-- -- Exercise (practice)

-- multComm : (m,n : N) -> m * n = n * m

-- -- Exercise (practice)

-- zeroMonus : (n : N) -> Zero -* n = Zero

-- -- Exercise (practice)

-- monusAssoc : (m,n,p : N) -> m -* n -* p = m -* (n + p)

-- -- Exercise (strech)

-- expDistribLOverMult : (m,n,p : N) -> m ^ (n + p) = (m ^ n) * (m ^ p)
-- expDistribOverMult : (m,n,p : N) -> (m * n) ^ p = (m ^ p) * (n ^ p)
-- expAssoc : (m,n,p : N) -> (m ^ n) ^ p = m ^ (n ^ p)

-- -- Exercise (strech)

-- incFrom : (b : Bin) -> from (inc b) = Suc (from b)
-- fromTo  : (b : Bin) -> to (from b) = b
-- toFrom  : (b : Bin) -> (to n) = n
