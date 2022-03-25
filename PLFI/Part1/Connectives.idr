module PLFI.Part1.Connectives

import Data.Fin
import PLFI.Part1.Isomorphism
import Syntax.PreorderReasoning.Generic

-- data _×_ (A B : Set) : Set where

--   ⟨_,_⟩ :
--       A
--     → B
--       -----
--     → A × B

test : (Int,Nat)
test = (0,0)

total
test2 : (Void,Nat)
test2 = (?x,0)

-- data TT : Type where
--   MkTT : TT

-- data TF : Type where

-- test3 : TF
-- test3 = ?x1

-- test4 : (TT, TT)
-- test4 = (MkTT, MkTT)

-- test5 : (TF, TT)
-- test5 = (?test5_rhs_1, MkTT)

-- test6 : (,) Nat Nat
-- test6 = (3,3)

data Sx : Nat -> Type where
  MkSx : Sx n

test7 : (x : Nat ** Sx x)
test7 = (3 ** MkSx)

test8 : DPair Nat (\x => Sx x)
test8 = MkDPair 3 MkSx

-- test8 : Sigma Nat (\x => Sx x)
-- test8 = MkSigma 3 MkSx

-- η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
etaTuple : {a,b : Type} -> (w : (a, b)) -> (fst w, snd w) === w
etaTuple (x, y) = Refl

-- data Bool : Set where
--   true  : Bool
--   false : Bool

-- data Tri : Set where
--   aa : Tri
--   bb : Tri
--   cc : Tri

data B : Type where
  True : B
  False : B

enumB : B -> Fin 2
enumB True = 0
enumB False = 1

-- data T : Type where
--   AA, BB, CC : T

-- enumT : T -> Fin 3
-- enumT AA = 0
-- enumT BB = 1
-- enumT CC = 2

tupleX : (a -> Fin n) -> (b -> Fin m) -> (a,b) -> Fin (n * m)
tupleX f s x = ?xy

-- timesCountBetween1and6 : (x: (Bool, Tri)) -> (timesCount x <= 6 && timesCount x >= 1) = True
-- timesCountBetween1and6 (False, Aa) = Refl
-- timesCountBetween1and6 (False, Bb) = Refl
-- timesCountBetween1and6 (False, Cc) = Refl
-- timesCountBetween1and6 (True, Aa) = Refl
-- timesCountBetween1and6 (True, Bb) = Refl
-- timesCountBetween1and6 (True, Cc) = Refl

-- ×-comm : ∀ {A B : Set} → A × B ≃ B × A
-- ×-comm =
--   record
--     { to       =  λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
--     ; from     =  λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
--     ; from∘to  =  λ{ ⟨ x , y ⟩ → refl }
--     ; to∘from  =  λ{ ⟨ y , x ⟩ → refl }
--     }

prodComm : Iso (a,b) (b,a)
prodComm =
  MkIso 
    { to     = (\(x,y) => (y,x))
    , from   = (\(y,x) => (x,y))
    , fromTo = (\(x,y) => Refl)
    , toFrom = (\(y,x) => Refl)
    }

-- ×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
-- ×-assoc =
--   record
--     { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
--     ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
--     ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
--     ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
--     }

prodAssoc : Iso ((a,b),c) (a,(b,c))
prodAssoc = MkIso
  { to      = \((x,y),z) => (x,(y,z))
  , from    = \(x,(y,z)) => ((x,y),z)
  , fromTo  = \((x,y),z) => Refl
  , toFrom  = \(x,(y,z)) => Refl
  }

-- data ⊤ : Set where
--   tt :
--     --
--     ⊤

data T : Type where
  TT : T
     
-- ------ T-I
-- TT : T

--  T , c
-- ------- T-E
--    c

-- elim:
-- c -> (T -> c)
-- c -> T -> c
-- c -> c

-- ⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
-- ⊤-identityˡ =
--   record
--     { to      = λ{ ⟨ tt , x ⟩ → x }
--     ; from    = λ{ x → ⟨ tt , x ⟩ }
--     ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
--     ; to∘from = λ{ x → refl }
--     }

ttIdentityL : {a : Type} -> Iso (T, a) a
ttIdentityL = MkIso
  { to     = \(TT,y) => y
  , from   = \x => (TT, x)
  , fromTo = \(TT,y) => Refl
  , toFrom = \y => Refl
  }

-- ⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
-- ⊤-identityʳ {A} =
--   ≃-begin
--     (A × ⊤)
--   ≃⟨ ×-comm ⟩
--     (⊤ × A)
--   ≃⟨ ⊤-identityˡ ⟩
--     A
--   ≃-∎

-- 0
test3 : {a,b,c : Type} -> Iso a b -> Iso b c -> Iso a c
test3 ab bc = CalcWith {leq = Iso} $
  |~ a
  <~ b ... (ab)
  <~ c ... (bc)

ttIdentityR : {a : Type} -> Iso (a,T) a
ttIdentityR = CalcWith {leq = Iso} $
  |~ (a, T)
  <~ (T, a)  ... prodComm
  <~ a       ... ttIdentityL

-- Same as Either, we are going to use Either
data Sum : Type -> Type -> Type where
  L : a -> Sum a b
  R : b -> Sum a b

-- the first introduces a formula for the connective, which appears in the conclusion but not in the hypotheses
--     x : a
-- ------------- Sum-I1
-- L x : Sum a b
--
--     x : b
-- ------------- Sum-I2
-- R x : Sum a b

-- the second eliminates a formula for the connective, which appears in a hypothesis but not in the conclusion
-- Sum a b , (a -> c) , (b -> c)
-- ----------------------------- Sum-E
--              c 

-- case-⊎ : ∀ {A B C : Set}
--   → (A → C)
--   → (B → C)
--   → A ⊎ B
--     -----------
--   → C
-- case-⊎ f g (inj₁ x) = f x
-- case-⊎ f g (inj₂ y) = g y

-- either

-- η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w

either2 : (b -> c) -> (a -> c) -> Either a b -> c
either2 f g (Left x) = g x
either2 f g (Right x) = f x

etaEither : {a,b : Type} -> (w : Either a b) -> either Left Right w = w
etaEither (Left x) = Refl
etaEither (Right x) = Refl


testData1 : Either () Nat
testData1 = Right 1

test1 : Bool
test1 = either Left Right testData1 == (Right 1)

testData2 : Either Nat ()
testData2 = Left 2

test4 : Bool
test4 = either Left Right testData2 == (Left 2)

-- uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
uniqEither
  :  {a,b,c : Type} -> (h : Either a b -> c) -> (w : Either a b)
  -> either (h . Left) (h . Right) w = h w
uniqEither h (Left x) = Refl
uniqEither h (Right x) = Refl

-- test5 : let t = Nat = Nat in Either t t
-- test5 = Left Refl

commEither : Iso (Either a b) (Either b a)
commEither = MkIso
  { to     = either Right Left
  , from   = either Right Left
  , fromTo = \case
                (Left x) => Refl
                (Right x) => Refl
  , toFrom = \case
                (Left x) => Refl
                (Right x) => Refl
  }

assocEither : Iso (Either (Either a b) c) (Either a (Either b c))
assocEither = MkIso
  { to     = either (either Left (Right . Left)) (Right . Right)
  , from   = either (Left . Left) (either (Left . Right) Right)
  , fromTo = \case
                (Left (Left x))   => Refl
                (Left (Right x))  => Refl
                (Right x)         => Refl
  , toFrom = \case
                (Left x)          => Refl
                (Right (Left x))  => Refl
                (Right (Right x)) => Refl
  }

-- Couldn't parse any alternatives:
-- 1: Expected name.
-- ... (1 others)idris2
-- data G : Type where
--   { MkG : G
--   } -- c)

-- Without where clause it means something else, we declare this type, but we don't define it yet.
-- data F : Type          a)
-- declare data F : Type  a)

-- Suggestions for definition of empty type
-- data F : Type where -- b)

-- data F : Type where -- c)
--   impossible

-- data F : Type empty -- d)

-- data F : Type impossible -- e)

-- data F : Type where {}

data F : Type where -- c)

fElim : {0 a : Type} -> F -> a
fElim x impossible

fElim' : {a : Type} -> F -> a
fElim' = \x => case x of {} -- \case leads to a parse error

-- uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
-- uniq-⊥ h ()

uniqF : {c : Type} -> (h : F -> c) -> (w : F) -> fElim w = h w
uniqF h w impossible

-- ⊥-identityˡ

fIdentityL : Iso (Either F a) a
fIdentityL = MkIso
  { to     = either fElim id
  , from   = Right
  , fromTo = \case
                (Left x) => fElim x
                (Right x) => Refl
  , toFrom = \y => Refl
  }

fIdentityR : Iso (Either a F) a
fIdentityR = isoTrans commEither fIdentityL

-- η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
-- η-→ f = refl


-- TODO: Ask
--    a : Type
--    b : Type
--    f : a -> b
-- ------------------------------
-- xx : (\x => f x) = f
etaFun : {a,b : Type} -> (f : a -> b) -> (\x => f x) = f
etaFun f = Refl

--    a : Type
--    b : Type
--    f : a -> b
-- ------------------------------
-- xRefl : (\x => f x) = (\y => f y)
alphaFun : {a,b : Type} -> (f : a -> b) -> (\x => f x) = (\y => f y)
alphaFun f = Refl

-- Under the hood terms are normalized for alpha/eta equivalence?
alphaFun2 : {a,b,c : Type} -> (f : a -> b -> c) -> (z : b) -> (\x => f x z) = (\y => f y z)
alphaFun2 f z = Refl

betaFun : (y : Nat) -> (\x => x * x) y = y * y
betaFun y = Refl

namespace Newtype12

  export
  Person : Type
  Person = (String, Int)

  public export
  mkPerson : (String, Int) -> Person
  mkPerson = id

  public export
  unPerson : Person -> (String, Int)
  unPerson = id

  export
  0
  samePersonLemma : (p : Person) -> (mkPerson (unPerson p)) = p
  samePersonLemma p = Refl

  -- export
  -- samePersonLemma

test5 : Person
test5 = mkPerson ("Andor", 23)

-- samePersonLemma : (p : Person) -> (mkPerson (unPerson p)) = p
-- samePersonLemma p = Refl

samePersonLemmaR : (p : (String, Int)) -> (unPerson (mkPerson p) = p)
samePersonLemmaR p = ?h1_0

handwaving : {t : Type} -> (a : t) -> (b : t) -> (a = b)
handwaving a b = believe_me (the (a=a) Refl)

namespace Postulate

  export
  extensionality : {a,b : Type} -> {f,g : a -> b} -> ((x : a) -> f x = g x) -> f = g
  extensionality _ = handwaving f g

-- currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying : {a,b,c : Type} -> Iso (a -> b -> c) ((a,b) -> c)
currying = MkIso
  { to      = \f => \(x,y) => f x y
  , from    = \f => \x => \y => f (x, y)
  , fromTo  = \f => Refl
  , toFrom  = \g => extensionality (\(x,y) => Refl)
  }

-- c ^ (a + b) ~ c ^ a * c ^ b
-- →-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
distribFunOverSumR : {a,b,c : Type} -> Iso (Either a b -> c) (a -> c, b -> c)
distribFunOverSumR = MkIso
  { to     = \f     => (f . Left, f . Right)
  , from   = \(f,g) => either f g
  , fromTo = \f     => extensionality (\case { Left x => Refl ; Right y => Refl })
  , toFrom = \(f,g) => Refl
  }

-- →-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
-- (p * n) ^ m = (p ^ m) * (n ^ m)
distribFunOverProdL : {a,b,c : Type} -> Iso (a -> (b,c)) (a -> b, a -> c)
distribFunOverProdL = MkIso
  { to     = \f     => (fst . f, snd . f)
  , from   = \(f,g) => \x => (f x, g x)
  , fromTo = \f     => extensionality (\x => etaTuple (f x)) -- TODO: Next time cong
  , toFrom = \(f,g) => Refl
  }
