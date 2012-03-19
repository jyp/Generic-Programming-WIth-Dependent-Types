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

module ContainerTypes where

    * = Set
    *₁ = Set1

    module Unary where
      
      data UCont : *₁ where
        ucont : (S : *) (P : S -> *) -> UCont

      Shape : UCont -> *
      Shape (ucont S P) = S

      Position : (c : UCont) ->  Shape c -> *
      Position (ucont S P) s = P s
      

      data UExt : UCont -> * -> *₁ where
        uext :  forall {S P X} -> (s : S) -> (f : P s -> X) -> UExt (ucont S P) X

      shape : forall {C X} -> UExt C X -> Shape C
      shape (uext s _) = s

      module Lists where

        cList = ucont ℕ Fin

        cNil : forall {X} -> UExt cList X 
        cNil = uext 0 (\ ())

        caseFin : forall {n} -> {a : *} -> a -> (Fin n -> a) -> (Fin (suc n) -> a)
        caseFin a' f zero = a'
        caseFin a' f (suc i) = f i

        cCons : forall {X} -> X -> UExt cList X -> UExt cList X
        cCons x (uext s f) = uext (suc s) (caseFin x f) 

      module Exercise10 where -- TODO

      ucmap : forall {X Y} -> (C : UCont) (f : X -> Y) (c : UExt C X) -> UExt C Y
      ucmap (ucont S P) f (uext s g) = uext s (f ∘ g)

      lookup : {X : *} {C : UCont} -> (c : UExt C X) -> (p : Position C (shape c)) -> X
      lookup (uext s f) p = f p

      

    module Nary where
      
      -- code for a container type
      data Cont (n : ℕ) : *₁ where
        cont : (Shape : *) ->                                                 -- shape of the container
               (Position : (variable : Fin n) -> Shape -> *) ->               -- for each variable, type of positions in the container
               Cont n


      Shape : forall {n} -> Cont n -> *
      Shape (cont S P) = S

      Position : forall {n} -> (c : Cont n) -> Fin n -> Shape c -> *
      Position (cont S P) i s = P i s


      -- In the following: 
      --  S T ∈ Shape
      --  P Q ∈ Contents

      -- semantics for a container type
      data Ext {n : ℕ} : Cont n -> (Fin n -> *) -> *₁ where
        ext :  forall {S P Xs} -> (s : S) -> (f : {i : Fin n} -> P i s -> Xs i) -> Ext (cont S P) Xs

      -- extract the shape
      shape : forall {n Xs} -> {C : Cont n} -> Ext C Xs -> Shape C
      shape (ext s f) = s

      -- lookup an element
      lookup : forall {n Xs} {C : Cont n} (i : Fin n) (c : Ext C Xs) -> (p : Position C i (shape c)) -> Xs i
      lookup i (ext s f) = f {i}

      -- N-ary map
      map : {n : ℕ} (C : Cont n) (Xs Ys : Fin n -> *) -> (fs : {i : Fin n} -> Xs i -> Ys i) -> Ext C Xs -> Ext C Ys
      map .(cont S P) Xs Ys f (ext {S} {P} s g) = ext s (f ∘ g)


      cZero : forall {n} -> Cont n
      cZero = cont ⊥ (\s p -> ⊥)

      cOne  : forall {n} -> Cont n
      cOne  = cont ⊤ (\s p -> ⊥)


      -- sum position
      data PPlus {A B : *} (P : A -> *) (Q : B -> *) : A ⊎ B -> * where
        pinl : forall {a} -> (p : P a) -> PPlus P Q (inj₁ a) -- on the left: then we have the left position
        pinr : forall {b} -> (q : Q b) -> PPlus P Q (inj₂ b) 

      cPlus : forall {n} -> Cont n -> Cont n -> Cont n
      cPlus (cont S P) (cont T Q) = cont (S ⊎ T) (λ i → PPlus (P i) (Q i))

      -- product position
      data PTimes {A B : *} (P : A -> *) (Q : B -> *) : A × B -> * where
        pleft  : forall {a b} -> (p : P a) -> PTimes P Q (a , b)
        pright : forall {a b} -> (q : Q b) -> PTimes P Q (a , b)

      cTimes : forall {n} -> Cont n -> Cont n -> Cont n
      cTimes (cont S P) (cont T Q) = cont (S × T) (λ i → PTimes (P i) (Q i))

      module Exercise14 where -- TODO

      cvl : forall {n} -> Cont (suc n)
      cvl = cont ⊤ (λ i tt' → i ≡ zero)

      Pwk : forall {n} {S : *} -> (P : Fin n → S → *) -> (i : Fin (suc n)) -> (s : S) -> *
      Pwk P zero s = ⊥
      Pwk P (suc i) s = P i s

      cwk : forall {n} -> Cont n -> Cont (suc n)
      cwk (cont S P) = cont S (Pwk P)

      -- alternatively, direct access to a variable:
      cvar : forall {n} -> Fin n -> Cont n
      cvar v = cont ⊤ (λ i tt' -> i ≡ v) -- there is 1 position if i = v, 0 otherwise.

      -- shape after substituting T in S.
      data Sdef (S : *) (P₀ : S → *) (T : *) : * where
        sdef : (s : S) ->         -- outer shape
               (f : P₀ s → T) ->  -- inner shapes: for each (outer) position, an inner shape
               Sdef S P₀ T

      -- postition after substitution.
      data Pdef {S T} (P₀ P' : S → *) (Q : T → *) : Sdef S P₀ T -> * where
        -- outer position
        ppos : forall {s f} -> (p : P' s)                  -> Pdef P₀ P' Q (sdef s f)
        -- inner position
        qpos : forall {s f} -> (p : P₀ s) -> (q : Q (f p)) -> Pdef P₀ P' Q (sdef s f)

      cdef : forall {n} -> Cont (suc n) -> Cont n -> Cont n
      cdef (cont S P) (cont T Q) = cont (Sdef S (P zero) T) (λ i → Pdef (P zero) (P (suc i)) (Q i))

    
      data PW (S : *) (P₀ P' : S -> *) : W S P₀ -> * where
        here  : forall {s f} -> (x : P' s)                           -> PW S P₀ P' (Sup s f)
        under : forall {s f} -> (p : P₀ s) -> (r : PW S P₀ P' (f p)) -> PW S P₀ P' (Sup s f)
      
      
      cMu : forall {n} -> Cont (suc n) -> Cont n
      cMu (cont S P) = cont (W S (P zero)) (λ i → PW S (P zero) (P (suc i)))


      μ : forall {n} -> Cont (suc n) -> Cont n
      μ = cMu

      Top  : forall {n} -> Cont n
      Top = cOne

      _⊕_ : forall {n} -> Cont n -> Cont n -> Cont n
      _⊕_ = cPlus

      _⊗_ : forall {n} -> Cont n -> Cont n -> Cont n
      _⊗_ = cTimes

      vl : forall {n} -> Cont (suc n)
      vl = cvl

      wk : forall {n} -> Cont n -> Cont (suc n)
      wk = cwk
      infixr 7 _⊗_
      infixr 6 _⊕_

      uTree : forall {n} -> Cont (suc n)
      uTree = μ (Top ⊕ vl ⊗ wk vl ⊗ vl)
    

