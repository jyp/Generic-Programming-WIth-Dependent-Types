
open import Data.Bool
open import Data.Empty
open import Data.Maybe
open import Data.Nat
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality
open import Data.Fin
open import Data.Function
open import Data.Unit
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Lib

module Preliminaries where ---------------------------------------------------
------------------------------------------------------------------------------


  data So : (Bool -> Set) where
    oh : So true


  notSo : {X : Set} -> So false -> X
  notSo ()

  module WNat where
    wNat : Set
    wNat = W Bool So

    wZero : wNat
    wZero = Sup false notSo

    wSuc : {X : Set} -> (x : X) -> wNat -> wNat
    wSuc x n = Sup true (\p -> n)


  module Exercise3 where

    data TreeShape (L : Set) : Set where
      leaf : L -> TreeShape L
      bin  : TreeShape L
    
    data TreePos {L : Set} : TreeShape L -> Set where
      left  : TreePos bin
      right : TreePos bin

      
    BinTree : Set -> Set
    BinTree A = W (TreeShape A) TreePos
    
    wLeaf : {L : Set} -> L -> BinTree L
    wLeaf a = Sup (leaf a) (\ ())

    sel : forall {a} -> BinTree a -> BinTree a -> TreePos {a} bin -> BinTree a
    sel l r left = l
    sel l r right = r

    wBin : {L : Set} -> BinTree L -> BinTree L -> BinTree L
    wBin l r = Sup bin (sel l r)

  module Exercise3a where
    
    TreeShape = Maybe

    TreePos : {L : Set} -> TreeShape L -> Set 
    TreePos (just x) = ⊥  -- no recursive position
    TreePos nothing = Bool -- two recursive position

    BinTree : Set -> Set
    BinTree A = W (TreeShape A) TreePos
    
    wLeaf : {L : Set} -> L -> BinTree L
    wLeaf a = Sup (just a) (\ ())

    wBin : {L : Set} -> BinTree L -> BinTree L -> BinTree L
    wBin l r = Sup nothing (\ p -> if p then l else r)

  module Views where

    data EqOrNot (B : Bool) : (Bool -> Set) where
      same : EqOrNot B B
      diff : EqOrNot B (not B)

    eqOrNot : (a b : Bool) -> EqOrNot a b
    eqOrNot true true = same
    eqOrNot true false = diff
    eqOrNot false true = diff
    eqOrNot false false = same

    xor : (a b : Bool) -> Bool
    xor a b with eqOrNot a b 
    xor a .a       | same = false
    xor a .(not a) | diff = true

    ----------------------------

    open WNat

    wNatEq : (x y : wNat) -> Bool
    wNatEq (Sup b f)     (Sup a g) with eqOrNot b a
    wNatEq (Sup true f)  (Sup true g)     | same = wNatEq (f oh) (g oh)
    wNatEq (Sup false f) (Sup false g)    | same = true
    wNatEq (Sup b f)     (Sup .(not b) g) | diff = false

  Nat = ℕ

  plus : Nat -> Nat -> Nat
  plus zero n = n
  plus (suc n) m = suc (plus n m)


  times : Nat -> Nat -> Nat
  times zero n = zero
  times (suc m) n = plus n (times m n)



  -------------------------------
  -- SUM

  -- | finl will map the lements of Fin m to the first m elements fo Fin  (plus m n)
  finl : (m n : Nat) (i : Fin m) -> Fin (plus m n)
  finl zero    n ()
  finl (suc m) n zero = zero
  finl (suc m) n (suc i) = suc (finl m n i)

  -- | finr will map the lements of Fin n to last n elements fo Fin (plus m n)
  finr : (m n : Nat) (j : Fin n) -> Fin (plus m n)
  finr zero    n j = j
  finr (suc m) n j = suc (finr m n j)

  -- | View of Fin (plus m n) as two parts; in left or right.

  -- This can be seen as a relation between the three arguments: m, n and Fin (plus m n)
  -- with associated information: Left or Right?

  -- The family is inductive because the type of the 3rd argument depends on the first two.
  data FinPlus (m n : Nat) : Fin (plus m n) -> Set where
    isfinl : (i : Fin m) -> FinPlus m n (finl m n i)
    isfinr : (j : Fin n) -> FinPlus m n (finr m n j)

  -- | Coverage of the above view; definition of the relation.
  finPlus : (m n : Nat) (i : Fin (plus m n)) -> FinPlus m n i
  finPlus zero n i = isfinr i
  finPlus (suc m) n zero = isfinl zero
  finPlus (suc m) n (suc i) with finPlus m n i
  finPlus (suc m) n (suc .(finl m n i)) | isfinl i = isfinl (suc i)
  finPlus (suc m) n (suc .(finr m n j)) | isfinr j = isfinr j
    

  fcase : {X : Set} {m n : Nat} (s : Fin (plus m n)) (l : Fin m -> X) (r : Fin n -> X) -> X
  fcase {X} {m} {n} s l r with finPlus m n s 
  fcase {X} {m} {n} .(finl m n i) l r | isfinl i = l i
  fcase {X} {m} {n} .(finr m n j) l r | isfinr j = r j
   

  -------------------------------
  -- PRODUCT

  fpair : (m n : Nat) (i : Fin m) (j : Fin n) -> Fin (times m n)
  fpair zero _ () _ 
  fpair (suc m) n zero j = finl n (times m n) j
  fpair (suc m) n (suc i) j = finr n (times m n) (fpair m n i j)

  data FinTimes (m n : Nat) : Fin (times m n) -> Set where
    isfpair : (i : Fin m) (j : Fin n) -> FinTimes m n (fpair m n i j)

  finTimes : (m n : Nat) (i : Fin (times m n)) -> FinTimes m n i
  finTimes zero n ()
  finTimes (suc m) n i with finPlus n (times m n) i
  finTimes (suc m) n .(finl n (times m n) i) | isfinl i = isfpair zero i
  finTimes (suc m) n .(finr n (times m n) j) | isfinr j with finTimes m n j
  finTimes (suc m) n .(finr n (times m n) (fpair m n i j)) | isfinr .(fpair m n i j) | isfpair i j  = isfpair (suc i) j

