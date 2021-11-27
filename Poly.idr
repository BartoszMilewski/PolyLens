module Main
import Data.Fin

data Vect : Type -> Nat -> Type where
  VNil : Vect a Z
  VCons : (x: a) -> (xs : Vect a n) -> Vect a (S n)

append : Vect a m -> Vect a n -> Vect a (m + n)
append VNil v = v
append (VCons a w) v = VCons a (append w v)

index : Fin n -> Vect a n -> a
index FZ (VCons a v) = a
index (FS n) (VCons a v) = index n v

data Tree : Type -> Nat -> Type where
  Empty : Tree a Z
  Leaf  : a -> Tree a 1
  Node  : Tree a n -> Tree a m -> Tree a (m + n + 1)

-- existential vector (n is hidden)
data SomeVect : Type -> Type where
  FromV : {n : Nat} -> Vect a n -> SomeVect a

data SomeTree : Type -> Type where
  FromT : {n : Nat} -> Tree a n -> SomeTree a

Nt : Type
Nt = Nat -> Type

splitV : (n : Nat) -> Vect a (n + m) -> (Vect a n, Vect a m)
splitV Z v = (VNil, v)
splitV (S k) (VCons a v') = let (v1, v2) = splitV k v'
                            in (VCons a v1, v2)

mapV : (a -> b) -> Vect a n -> Vect b n
mapV f VNil = VNil
mapV f (VCons a v) = VCons (f a) (mapV f v)

split : Vect a (n + m) -> (Vect a n -> Tree b k) -> (Vect a m, Tree b k)
split {n} v f = let (v1, v2) = splitV n v
                in (v2, f v1)

--Compose two functions that turn vector to tree
compose : (Vect b n -> Tree b k) -> (Vect b m -> Tree b j) ->
       (Vect b (n + m) -> Tree b (j + k + 1))
compose {n} f1 f2 v =
  let (v1, v2) = splitV n v
  in Node (f1 v1) (f2 v2)

-- exists n. (k, Vect a n, Vect b n -> Tree k)
data SomePair : Nt -> Nt -> Nt -> Type where
 FromPair : {n : Nat} -> (k : Nat) -> a n -> (b n -> t k) -> SomePair a b t

-- Given source Tree a, return a pair
--  (Vect a of leaves, function from Vect b of leaves to Tree b)
replace : (b : Type) -> Tree a n -> SomePair (Vect a) (Vect b) (Tree b)
replace b Empty = FromPair 0 VNil (\v => Empty)
replace b (Leaf x) = FromPair 1 (VCons x VNil) (\(VCons y VNil) => Leaf y)
replace b (Node t1 t2) =
  let (FromPair k1 v1 f1) = replace b t1
      (FromPair k2 v2 f2) = replace b t2
      v3 = append v1 v2
      f3 = compose f1 f2
  in FromPair (k2 + k1 + 1) v3 f3

PolyLens : Nt -> Nt -> Nt -> Nt -> Type
PolyLens s t a b = {k : Nat} -> s k -> SomePair a b t

treeLens : PolyLens (Tree a) (Tree b) (Vect a) (Vect b)
--treeLens Empty = FromPair 0 VNil (\b => Empty)
treeLens {b} t = replace b t

getLeaves : Tree a n -> SomeVect a
getLeaves t =
  let  FromPair k v vt = (the (PolyLens  (Tree a) (Tree a) (Vect a) (Vect a)) treeLens) t
  in  FromV v

mapLeaves : (a -> b) -> Tree a n -> SomeTree b
mapLeaves {a} {b} f t =
  let  FromPair k v vt = (the (PolyLens  (Tree a) (Tree b) (Vect a) (Vect b)) treeLens) t
  in  FromT (vt (mapV f v))


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
v3 = append v1 v2

someV : SomeVect Char
someV = FromV v2

Show a => Show (SomeVect a) where
  show (FromV v) = show v

Show a => Show (SomeTree a) where
  show (FromT v) = show v

t1 : Tree Char 1
t1 = Leaf 'z'
t3 : Tree Char 5
t3 = (Node t1 (Node (Leaf 'a') (Leaf 'b')))

main : IO ()
main = do
  print (getLeaves t3)
  print (mapLeaves ord t3)
  print (mapLeaves ord Empty)
