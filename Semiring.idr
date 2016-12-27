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

Semiring Bool where
  x + y = x || y
  x * y = x && y
  one = True
  zer = False

Semiring b => Semiring (Morphism a b) where
  (Mor f) + (Mor g) = Mor (\x => f x + g x)
  (Mor f) * (Mor g) = Mor (\x => f x * g x)
  one = Mor (\_ => one)
  zer = Mor (\_ => zer)

Semiring Double where
  (+) = prim__addFloat
  (*) = prim__mulFloat
  one = 1
  zer = 0

interface Semiring a => VerifiedSemiring a where
  plusAssoc : (x, y, z : a) -> (x + y) + z = x + (y + z)
  multAssoc : (x, y, z : a) -> (x * y) * z = x * (y * z)
  plusComm  : (x : a) -> (y : a) -> x + y = y + x
  plusId : (x : a) -> x + Semiring.zer = x
  mulIdR : (x : a) -> x * Semiring.one = x
  mulIdL : (x : a) -> Semiring.one * x = x
  mulAnR : (x : a) -> x * Semiring.zer = Semiring.zer
  mulAnL : (x : a) -> Semiring.zer * x = Semiring.zer
  mulDsR : (x, y, z : a) -> (x + y) * z = (x * z) + (y * z)
  mulDsL : (x, y, z : a) -> x * (y + z) = (x * y) + (x * z)

VerifiedSemiring Bool where
  plusAssoc False y z = Refl
  plusAssoc True  y z = Refl
  multAssoc False y z = Refl
  multAssoc True  y z = Refl
  plusComm False False = Refl
  plusComm False True  = Refl
  plusComm True  False = Refl
  plusComm True  True  = Refl
  plusId False = Refl
  plusId True  = Refl
  mulIdL False = Refl
  mulIdL True  = Refl
  mulIdR False = Refl
  mulIdR True  = Refl
  mulAnR False = Refl
  mulAnR True  = Refl
  mulAnL x = Refl
  mulDsR False y z = Refl
  mulDsR True False False = Refl
  mulDsR True False True  = Refl
  mulDsR True True False  = Refl
  mulDsR True True True   = Refl
  mulDsL False y z = Refl
  mulDsL True  y z = Refl

Semiring Nat where
  (+) = plus
  (*) = mult
  one = 1
  zer = 0

VerifiedSemiring Nat where
  plusAssoc x y z = sym (plusAssociative x y z)
  multAssoc x y z = sym (multAssociative x y z)
  plusComm = plusCommutative
  plusId = plusZeroRightNeutral
  mulAnL = multZeroLeftZero
  mulAnR = multZeroRightZero
  mulIdL = multOneLeftNeutral
  mulIdR = multOneRightNeutral
  mulDsL = multDistributesOverPlusRight
  mulDsR = multDistributesOverPlusLeft

interface Semigroup a => VerifiedSemigroup a where
  semigroupOpIsAssociative : (l, c, r : a) -> l <+> (c <+> r) = (l <+> c) <+> r

interface (VerifiedSemigroup a, Monoid a) => VerifiedMonoid a where
  monoidNeutralIsNeutralL : (l : a) -> l <+> neutral = l
  monoidNeutralIsNeutralR : (r : a) -> neutral <+> r = r

interface VerifiedMonoid a => CommutativeMonoid a where
  mappendCommutes : (x, y : a) -> x <+> y = y <+> x

CommutativeMonoid a => Semiring (Endomorphism a) where
  (Endo f) + (Endo g) = Endo (\x => f x <+> g x)
  (Endo f) * (Endo g) = Endo (f . g)
  zer = Endo (const neutral)
  one = Endo id
