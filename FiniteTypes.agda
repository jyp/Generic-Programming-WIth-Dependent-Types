module FiniteTypes where
  -- Codes for finite types
  data Ufin : Set where
    O : Ufin
    I : Ufin
    _⊕_ : Ufin -> Ufin -> Ufin
    _⊗_ : Ufin -> Ufin -> Ufin

  -- Finite types
  data Elfin : Ufin -> Set where
    void : Elfin I
    inl : {a b : Ufin} -> (x : Elfin a) -> Elfin (a ⊕ b)
    inr : {a b : Ufin} -> (x : Elfin b) -> Elfin (a ⊕ b)
    pair : {a b : Ufin} -> (x : Elfin a) -> (y : Elfin b) -> Elfin (a ⊗ b)
  

  dist : {a b c : Ufin} -> Elfin (a ⊗ (b ⊕ c)) -> Elfin ((a ⊗ b) ⊕ (a ⊗ c))
  dist (pair x (inl y)) = inl (pair x y)
  dist (pair x (inr y)) = inr (pair x y)


  -- Values will be stored in a tree
  data ET (A : Set) : Set where
    V : (a : A) -> ET A             -- leaf  
    C : (l r : ET A) -> ET A        -- bin 
    E : ET A                        -- empty

  -- Those trees form a monad...
  returnET : {A : Set} (a : A) -> ET A
  returnET a = V a

  bindET : {A B : Set} (t : ET A) (f : A -> ET B) -> ET B
  bindET (V a) f = f a
  bindET (C l r) f = C (bindET l f) (bindET r f)
  bindET E f = E

  mapET : {A B : Set} (f : A -> B) (t : ET A) -> ET B
  mapET f t = bindET t (\x -> returnET (f x))

  -- Enumerate all elements of a finite type. (finite values)
  enum : (a : Ufin) -> ET (Elfin a)
  enum O = E
  enum (a ⊕ b) = C (mapET inl (enum a)) (mapET inr (enum b))
  enum I = V void
  enum (a ⊗ b) = bindET (enum a) (\x -> mapET (\y -> pair x y) (enum b))
