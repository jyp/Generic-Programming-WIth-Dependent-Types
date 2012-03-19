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

module ContextFreeTypes where
  -- Codes for context-free types
  data Ucf : ℕ -> Set where
    Bot : forall {n} -> Ucf n
    Top : forall {n} -> Ucf n
    _⊕_ : forall {n} -> (a b : Ucf n) -> Ucf n
    _⊗_ : forall {n} -> (a b : Ucf n) -> Ucf n
    vl  : forall {n} -> Ucf (suc n) -- last variable (in a non-empty context.)
    wk  : forall {n} -> (a : Ucf n) -> Ucf (suc n) -- introduce a variable
    def : forall {n} -> (f : Ucf (suc n)) -> (a : Ucf n) -> Ucf n -- substitute the last variable
    μ   : forall {n} -> (f : Ucf (suc n)) -> Ucf n -- fixpoint (of the last variable)

  infixr 7 _⊗_
  infixr 6 _⊕_

  uNat : forall {n} -> Ucf n
  uNat = μ (Top ⊕ vl)

  uList : forall {n} -> Ucf (suc n)
  uList = μ (Top ⊕ wk vl ⊗ vl)

  uTree : forall {n} -> Ucf (suc n)
  uTree = μ (Top ⊕ vl ⊗ wk vl ⊗ vl)

  roseTree : forall {n} -> Ucf (suc n)
  roseTree = μ (def uList (wk vl ⊗ vl))


  data Tel : ℕ -> Set where
    tnil : Tel 0
    tcons : {n : ℕ} -> (a : Ucf n) -> (as : Tel n) -> Tel (suc n)

  -- elements of type "Ucf n" applied to the given telescope.  
  data Elcf : {n : ℕ} -> Ucf n -> Tel n -> Set where
      void  : {n : ℕ} {as : Tel n} -> Elcf Top as
      inl   : {n : ℕ} {as : Tel n} {a b : Ucf n} -> (x : Elcf a as) -> Elcf (a ⊕ b) as
      inr   : {n : ℕ} {as : Tel n} {a b : Ucf n} -> (x : Elcf b as) -> Elcf (a ⊕ b) as
      pair  : {n : ℕ} {as : Tel n} {a b : Ucf n} -> (x : Elcf a as) -> (y : Elcf b as) -> Elcf (a ⊗ b) as
      top   : {n : ℕ} {as : Tel n} {a : Ucf n} -> Elcf a as -> Elcf vl (tcons a as)
      pop   : {n : ℕ} {as : Tel n} {a b : Ucf n} -> Elcf a as -> Elcf (wk a) (tcons b as)
      push  : {n : ℕ} {as : Tel n} {a : Ucf n} {f : Ucf (suc n)} -> Elcf f (tcons a as) -> Elcf (def f a) as
      ins   : {n : ℕ} {as : Tel n} {f : Ucf (suc n)} -> (x : Elcf f (tcons (μ f) as)) -> Elcf (μ f) as -- here the args of tcons are swapped in the paper (typo?)

  uListRose : Ucf 0 -> Ucf 0
  uListRose tc = def uList (def roseTree tc)
  uListRose' : {n : ℕ} -> Ucf (suc n)
  uListRose'  = def uList (def roseTree vl)

  ListRose : Ucf 0 -> Set
  ListRose tc = Elcf (uListRose tc) tnil

  Rose : Ucf 0 -> Set
  Rose tc = Elcf roseTree (tcons tc tnil)

{-
  List : Ucf 0 -> Set
  List tc = Elcf uList (tcons t tnil) 
-}

  fork : (ac : Ucf 0) -> Elcf ac tnil -> ListRose ac -> Rose ac
  fork ac e rs = ins (push {!!})

  uZero : {n : ℕ} {as : Tel n} -> Elcf uNat as
  uZero = ins (inl void)

  uSuc : {n : ℕ} {as : Tel n} -> Elcf uNat as -> Elcf uNat as
  uSuc arg = ins (inr (top arg))

  data NatView {N : ℕ} {as : Tel N} : (n : Elcf uNat as) -> Set where
    isZ : NatView uZero
    isS : forall {n} -> Elcf uNat as -> NatView (uSuc n)
    
  natView : forall {N} -> {as : Tel N} -> (n : Elcf uNat as) -> NatView n
  natView (ins (inl void)) = isZ
  natView (ins (inr (top n))) = isS n

  module Exercise6 where
    uNil : forall {n} -> {X : Ucf n} {as : Tel n} -> Elcf uList (tcons X as)
    uNil = ins (inl void)

    uCons : forall {n} -> {X : Ucf n} {as : Tel n} -> Elcf X as -> Elcf uList (tcons X as) -> Elcf uList (tcons X as)
    uCons x xs = ins (inr (pair (pop (top x)) (top xs)))
     
    data ListView {n : ℕ} {X : Ucf n} {as : Tel n} : Elcf uList (tcons X as) -> Set where
      isNil : ListView uNil
      isCons : forall {x xs} -> Elcf X as -> Elcf uList (tcons X as) -> ListView (uCons x xs)

    listView : {n : ℕ} {X : Ucf n} {as : Tel n} (xs : Elcf uList (tcons X as)) -> ListView xs
    listView (ins (inl void)) = isNil
    listView (ins (inr (pair (pop (top y)) (top y')))) = isCons y y'

  geq : forall {N a} -> {as : Tel N} -> (x y : Elcf a as) -> Bool
  geq void void = true
  geq (inl x)  (inl x') = geq x x'
  geq (inl x)  (inr x') = false
  geq (inr x)  (inl x') = false
  geq (inr x)  (inr x') = geq x x'
  geq (pair x y) (pair x' y') = geq x x' ∧ geq y y'
  geq (top y)  (top y') = geq y y'
  geq (pop y)  (pop y') = geq y y'
  geq (push y) (push y') = geq y y'
  geq (ins x)  (ins x') = geq x x'



  module Exercise7 where
    Injectiv : {A B : Set} -> (f : A -> B) -> Set
    Injectiv {A} {B} f = {x y : A} -> f x ≡ f y -> x ≡ y

    lift' : forall {A B} {x y : A} -> (f : A -> B) -> Injectiv f -> Dec (x ≡ y) -> Dec (f x ≡ f y)
    lift' f inj (yes p) = yes (cong f p)
    lift' f inj (no ¬p) = no (\q -> ¬p (inj q))
  
    -- lots of awesome injectivity lemmas...
    inlinj : {n : ℕ} {as : Tel n} {a b : Ucf n} -> Injectiv {Elcf a as} {Elcf (a ⊕ b) as} inl
    inlinj refl = refl

    inrinj : {n : ℕ} {as : Tel n} {a b : Ucf n} -> Injectiv {Elcf a as} {Elcf (b ⊕ a) as} inr
    inrinj refl = refl

    topinj : {n : ℕ} {as : Tel n} {a : Ucf n} -> Injectiv {Elcf a as} {Elcf vl (tcons a as)} top
    topinj refl = refl

    popinj : {n : ℕ} {as : Tel n} {a b : Ucf n} -> Injectiv {Elcf a as} {Elcf (wk a) (tcons b as)} pop
    popinj refl = refl

    pushinj : {n : ℕ} {as : Tel n} {a : Ucf n} {f : Ucf (suc n)} -> Injectiv {Elcf f (tcons a as)} {Elcf (def f a) as} push
    pushinj refl = refl

    insinj : {n : ℕ} {as : Tel n} {f : Ucf (suc n)} -> Injectiv {Elcf f (tcons (μ f) as)} {Elcf (μ f) as} ins
    insinj refl = refl

    pair1 : {n : ℕ} {as : Tel n} {a b : Ucf n} -> {x x' : Elcf a as} -> {y y' : Elcf b as} -> pair x y ≡ pair x' y' -> x ≡ x'
    pair1 refl = refl

    pair2 : {n : ℕ} {as : Tel n} {a b : Ucf n} -> {x x' : Elcf a as} -> {y y' : Elcf b as} -> pair x y ≡ pair x' y' -> y ≡ y'
    pair2 refl = refl

    geqdec : forall {N a} -> {as : Tel N} -> (x y : Elcf a as) -> Dec (x ≡ y)
    geqdec void void = yes refl
    geqdec (inl x) (inl x') = lift' inl inlinj (geqdec x x')
    geqdec (inl x) (inr x') = no (λ ())
    geqdec (inr x) (inl x') = no (λ ())
    geqdec (inr x) (inr x') = lift' inr inrinj (geqdec x x')
    geqdec (pair x y) (pair x' y') with geqdec x x' | geqdec y y' 
    geqdec (pair x y) (pair x' y') | yes p | yes q = yes (cong₂ pair p q)
    geqdec (pair x y) (pair x' y') | no ¬p | yy    = no (λ q → ¬p (pair1 q))
    geqdec (pair x y) (pair x' y') | xx    | no ¬p = no (λ q → ¬p (pair2 q))
    geqdec (top y0) (top y1) = lift' top topinj (geqdec y0 y1)
    geqdec (pop y0) (pop y1) = lift' pop popinj (geqdec y0 y1)
    geqdec (push y0) (push y1) = lift' push pushinj (geqdec y0 y1)
    geqdec (ins x) (ins y) = lift' ins insinj (geqdec x y)
