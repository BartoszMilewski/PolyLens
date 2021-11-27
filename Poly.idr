module Main

data Vect : Type -> Nat -> Type where
  VNil : Vect a Z
  VCons : (x: a) -> (xs : Vect a n) -> Vect a (S n)

data Tree : Type -> Nat -> Type where
  Empty : Tree a Z
  Leaf  : a -> Tree a 1
  Node  : Tree a n -> Tree a m -> Tree a (m + n + 1)

-- Synonym for Nat-dependent types
Nt : Type
Nt = Nat -> Type

-- Existential types hiding dependence on Nat
data Some : Nt -> Type where
  Hide : {n : Nat} -> nt n -> Some nt

SomeTree : Type -> Type
SomeTree a = Some (Tree a)

SomeVect : Type -> Type
SomeVect a = Some (Vect a)

-- Vector utility functions

appendV : Vect a m -> Vect a n -> Vect a (m + n)
appendV VNil v = v
appendV (VCons a w) v = VCons a (appendV w v)

splitV : (n : Nat) -> Vect a (n + m) -> (Vect a n, Vect a m)
splitV Z v = (VNil, v)
splitV (S k) (VCons a v') = let (v1, v2) = splitV k v'
                            in (VCons a v1, v2)

mapV : (a -> b) -> Vect a n -> Vect b n
mapV f VNil = VNil
mapV f (VCons a v) = VCons (f a) (mapV f v)

-- The lens returns this existential type
-- For instance:
-- exists n. (k, Vect a n, Vect b n -> Tree k)
-- is a pair: a vector of leaves and a leaf changer
data SomePair : Nt -> Nt -> Nt -> Type where
 HidePair : {n : Nat} -> (k : Nat) -> a n -> (b n -> t k) -> SomePair a b t

------------------
-- Polynomial Lens
------------------

PolyLens : Nt -> Nt -> Nt -> Nt -> Type
PolyLens s t a b = {k : Nat} -> s k -> SomePair a b t

--------------------
-- Tree Lens
-- focuses on leaves
--------------------
-- When traversing the tree, each branch produces
-- a leaf changer. We have to compose them

--Compose two functions that turn vector to tree
compose : (Vect b n -> Tree b k) -> (Vect b m -> Tree b j) ->
       (Vect b (n + m) -> Tree b (j + k + 1))
compose {n} f1 f2 v =
  let (v1, v2) = splitV n v
  in Node (f1 v1) (f2 v2)

-- Given source Tree a, return a pair
--  (Vect a of leaves, function from Vect b of leaves to Tree b)
replace : (b : Type) -> Tree a n -> SomePair (Vect a) (Vect b) (Tree b)
replace b Empty = HidePair 0 VNil (\v => Empty)
replace b (Leaf x) = HidePair 1 (VCons x VNil) (\(VCons y VNil) => Leaf y)
replace b (Node t1 t2) =
  let (HidePair k1 v1 f1) = replace b t1
      (HidePair k2 v2 f2) = replace b t2
      v3 = appendV v1 v2
      f3 = compose f1 f2
  in HidePair (k2 + k1 + 1) v3 f3

-- Tree lens focuses on leaves of a tree
treeLens : PolyLens (Tree a) (Tree b) (Vect a) (Vect b)
treeLens {b} t = replace b t

-- Use tree lens to extract a vector of leaves
getLeaves : Tree a n -> SomeVect a
getLeaves t =
  let  HidePair k v vt =
    -- Help Idris with type annotation
         (the (PolyLens  (Tree a) (Tree a) (Vect a) (Vect a)) treeLens) t
  in   Hide v

-- Use tree lens to modify leaves
-- 1. extract the leaves
-- 2. map function over vector of leaves
-- 3. replace leaves with the new vector
mapLeaves : (a -> b) -> Tree a n -> SomeTree b
mapLeaves {a} {b} f t =
  let  HidePair k v vt =
    -- Help Idris with type annotation
         (the (PolyLens  (Tree a) (Tree b) (Vect a) (Vect b)) treeLens) t
  in  Hide (vt (mapV f v))

-- Utility functions for testing

Show a => Show (Vect a n) where
  show VNil = ""
  show (VCons a v) = show a ++ show v

Show a => Show (Tree a n) where
  show Empty = "()"
  show (Leaf a) = show a
  show (Node t1 t2) = "(" ++ show t1 ++ "," ++ show t2 ++ ")"

v0 : Vect Char 0
v0 = VNil
v1 : Vect Char 1
v1 = VCons 'a' VNil
v2 : Vect Char 2
v2 = VCons 'b' (VCons 'c' VNil)
v3 : Vect Char 3
v3 = appendV v1 v2

someV : SomeVect Char
someV = Hide v2

Show a => Show (SomeVect a) where
  show (Hide v) = show v

Show a => Show (SomeTree a) where
  show (Hide v) = show v

t1 : Tree Char 1
t1 = Leaf 'z'
t3 : Tree Char 5
t3 = (Node t1 (Node (Leaf 'a') (Leaf 'b')))

main : IO ()
main = do
  putStrLn "getLeaves"
  print (getLeaves t3)
  putStrLn "\nmapLeaves"
  print (mapLeaves ord t3)
  putStrLn "\nmapLeaves of an empty tree"
  print (mapLeaves ord Empty)
  putStrLn ""
