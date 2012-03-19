
module Ordinals where

import Data.Nat as N
open N using (ℕ; zero; suc)

data Ord : Set where
     oz : Ord
     os : (a : Ord) -> Ord
     olim : (f : ℕ -> Ord) -> Ord

n2o : ℕ -> Ord
n2o zero = oz
n2o (suc n) = os (n2o n)

ω : Ord
ω = olim n2o

_+_ : Ord -> Ord -> Ord
oz + b = b
os a + b = os (a + b)
olim f + b = olim (λ n → b + f n)



     



