{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ConstraintKinds #-}
module Main where
import Data.Kind
import Unsafe.Coerce

-- Peano numbers
data Nat = Z | S Nat
  deriving Show

type One   = S Z

-- Addition of Nats lifted to types (Here, Nat is a kind)
type family (+) (a :: Nat) (b :: Nat) :: Nat
type instance Z   + m = m
type instance S n + m = S (n + m)


data Vec a n where
    VCons :: a -> Vec a n -> Vec a (S n)
    VNil :: Vec a Z

concatV :: Vec a n -> Vec a m -> Vec a (n + m)
concatV VNil v = v
concatV (VCons a as) v = VCons a (concatV as v)

data Tree a (n :: Nat) where
  Empty :: Tree a Z
  Leaf :: a -> Tree a One
  Node :: Tree a m -> Tree a n -> Tree a (One + (m + n))

data SumPl a b t (k :: Nat) =
  forall (n :: Nat). SPL (a n, b n -> t k)

mapSum :: Functor1 v => (a -> b) -> SumPl (v a) (v b) t k -> t k
mapSum f (SPL (xs, bs2t)) = bs2t (fmap1 f xs)

type PolyLens s t a b = forall (k :: Nat). s k -> SumPl a b t k

treeLens :: PolyLens (Tree a) (Tree b) (Vec a) (Vec b)
treeLens (Leaf x) = SPL (VCons x VNil, \(VCons b VNil) -> (Leaf b))

t1 = Leaf 'a'
t2 = Leaf 'b'
t3 = Leaf 'c'
t4 = Node t1 t2
t5 = Node t3 t4


class Functor1 (f :: Type -> Nat -> Type) where
  fmap1 :: (a -> b) -> f a n -> f b n

instance Functor1 Vec where
    fmap1 f (VCons a as) = VCons (f a) (fmap1 f as)
    fmap1 _ VNil = VNil

mapTree :: (a -> b) -> Tree a n -> Tree b n
mapTree f t = mapSum f (treeLens t)

data ExVec a = forall (n :: Nat). ExVec (Vec a n)

trav :: Tree a n -> ExVec a
trav (Leaf x) = ExVec (VCons x VNil)
trav (Node t1 t2) = concatExVec (trav t1) (trav t2)

concatExVec :: ExVec a -> ExVec a -> ExVec a
concatExVec (ExVec v1) (ExVec v2) = ExVec (concatV v1 v2)


splitVT :: Vec b (n + m) -> (Vec b n -> Tree b k) -> (Vec b m, Tree b k)
splitVT VNil f = (VNil, Empty)
splitVT v@(VCons x VNil) f = (VNil, f v)


{-
splitV :: SNat n -> SNat m -> Vec a (n + m) -> (Vec a n, Vec a m)
splitV SZ _ v = (VNil, v)
splitV (SS n) m (h `VCons` t) = (h `VCons` t1, t2)
  where
      (t1, t2) = splitV n m t
-}

data Dict :: Constraint -> Type where
  Dict :: a => Dict a

plusZ :: forall n. Dict (n ~ (n + Z))
plusZ = unsafeCoerce (Dict :: Dict (n ~ n))
