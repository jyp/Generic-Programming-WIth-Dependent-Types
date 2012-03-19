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

module StrictlyPositiveTypes where
  data Usp : ℕ -> Set1 where
    Bot : forall {n} -> Usp n
    Top : forall {n} -> Usp n
    _⊕_ : forall {n} -> (a b : Usp n) -> Usp n
    _⊗_ : forall {n} -> (a b : Usp n) -> Usp n
    vl  : forall {n} -> Usp (suc n) -- last variable (in a non-empty context.)
    wk  : forall {n} -> (a : Usp n) -> Usp (suc n) -- introduce a variable
    def : forall {n} -> (f : Usp (suc n)) -> (a : Usp n) -> Usp n -- substitute the last variable
    μ   : forall {n} -> (f : Usp (suc n)) -> Usp n -- fixpoint (of the last variable)
    _⟶_ : forall {n} -> (A : Set) -> (b : Usp n) -> Usp n -- positive arrow

  data Tel : ℕ -> Set1 where
    tnil : Tel 0
    tcons : {n : ℕ} -> (a : Usp n) -> (as : Tel n) -> Tel (suc n)

  data Elsp : {n : ℕ} -> Usp n -> Tel n -> Set1 where
      void  : {n : ℕ} {as : Tel n} -> Elsp Top as
      inl   : {n : ℕ} {as : Tel n} {a b : Usp n} -> (x : Elsp a as) -> Elsp (a ⊕ b) as
      inr   : {n : ℕ} {as : Tel n} {a b : Usp n} -> (x : Elsp b as) -> Elsp (a ⊕ b) as
      pair  : {n : ℕ} {as : Tel n} {a b : Usp n} -> (x : Elsp a as) -> (y : Elsp b as) -> Elsp (a ⊗ b) as
      top   : {n : ℕ} {as : Tel n} {a : Usp n} -> Elsp a as -> Elsp vl (tcons a as)
      pop   : {n : ℕ} {as : Tel n} {a b : Usp n} -> Elsp a as -> Elsp (wk a) (tcons b as)
      push  : {n : ℕ} {as : Tel n} {a : Usp n} {f : Usp (suc n)} -> Elsp f (tcons a as) -> Elsp (def f a) as
      ins   : {n : ℕ} {as : Tel n} {f : Usp (suc n)} -> (x : Elsp f (tcons (μ f) as)) -> Elsp (μ f) as -- here the args of tcons are swapp
      fun   : {n : ℕ} {as : Tel n} {A : Set} {b : Usp n} (f : A -> Elsp b as) -> Elsp (A ⟶ b) as


  ord : {n : ℕ} -> Usp n 
  ord = μ (Top ⊕ (vl ⊕ (ℕ ⟶ vl)))

