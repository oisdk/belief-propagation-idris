module Semiring

import Data.Morphisms

%default total
%hide (+)
%hide (*)
%access public export

interface Semiring a where
  (+) : a -> a -> a
  (*) : a -> a -> a
  one : a
  zer : a

sum : (Foldable f, Semiring a) => f a -> a
sum = foldl (+) zer

mul : (Foldable f, Semiring a) => f a -> a
mul = foldl (*) one

implementation Semiring b => Semiring (Morphism a b) where
  (Mor f) + (Mor g) = Mor (\x => f x + g x)
  (Mor f) * (Mor g) = Mor (\x => f x * g x)
  one = Mor (\_ => one)
  zer = Mor (\_ => zer)

implementation Semiring Double where
  (+) = prim__addFloat
  (*) = prim__mulFloat
  one = 1
  zer = 0
