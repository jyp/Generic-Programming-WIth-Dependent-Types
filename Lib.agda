module Lib where

-- well-founded tree-like data. Tree-like data is
-- built from nodes. Each node carries some sort of data—its shape—usually, a
-- tag indicating what sort of node it is, plus some appropriate labelling. In any
-- case, the node shape determines what positions there might be for subtrees.


data W (Shape : Set) (Position : Shape -> Set) : Set where
  Sup : (s : Shape) -> (f : Position s -> W Shape Position) -> W Shape Position
