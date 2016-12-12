module Prob

import Marginalization
import Semiring
import HetVect

%default total
%access public export

||| Probability monad which keeps a list of the variables it contains
||| Prob s xs a = probability of `a`, given `xs`. `s` is the unit
data Prob : Type -> List Type -> Type -> Type where
  ||| change to (forall s. Semiring s => (a -> s) -> s) in order to avoid enum,
  ||| bounded constraints (maybe).
  Dst : (a -> s) -> Prob s [] a
  ||| Monadic bind. Potentially better performance if applicatives are added.
  ||| Also: should a be added here?
  Bnd : Prob s ys a -> (a -> Prob s xs b) -> Prob s (a::xs++ys) b
  -- Cmb : Prob s xs (a -> b) -> Prob s ys a -> Prob s (xs++ys) b

linear : Semiring s => Prob s xs a -> {auto prf : AllFinite xs} -> (a -> s)
linear (Dst f) y = f y
linear {xs=a::xs++ys} (Bnd x f) y {prf=Extra later}
  = marg (\z => linear x z {prf=finiteDistR later} * linear (f z) y {prf = finiteDistL later})


-- ||| Step one of belief propagation.
-- sendOut : Semiring s => Prob s xs a -> (Prob s xs a, Vect xs -> a -> s)
-- sendOut (Obs f) = (Obs f, const f)
-- sendOut (Dst f) = (Dst f, (\([x]), y => f x * f y)) -- not sure here
-- sendOut (Bnd f x) = ?sendOut_rhs_3

-- ||| Second part of belief propagation.
-- sendIn
--   : {s : Type}
--   -> Semiring s
--   => (f : Vect xs -> s)
--   -> {auto prf : AllFinite xs}
--   -> Prob s xs a
--   -> Prob s xs a
-- sendIn f (Obs x) = Obs x
-- sendIn f (Dst g) = Dst (\x => f [x] * g x)
-- sendIn {s} {prf=Extra rest} {xs=xs++ys} f (Bnd g x)
--   = Bnd
--     (\y => sendIn (margVecL {prf = ysFinite} f . (y::)) {prf = xsFinite} (g y))
--     (sendIn (margVecR (margOnce f) {prf = xsFinite}) {prf = ysFinite} x)
--   where
--     xsFinite : AllFinite xs
--     xsFinite = finiteDistL rest
--     ysFinite : AllFinite ys
--     ysFinite = finiteDistR rest
-- sendIn {s} {prf} {xs=xs++ys} f (Cmb g x)
--   = Cmb
--     (sendIn (margVecL {prf = ysFinite} f) {prf = xsFinite} g)
--     (sendIn (margVecR f {prf = xsFinite}) {prf = ysFinite} x)
--   where
--     xsFinite : AllFinite xs
--     xsFinite = finiteDistL prf
--     ysFinite : AllFinite ys
--     ysFinite = finiteDistR prf

-- ||| Full belief propagation.
-- propagate
--   : Semiring s
--   => Prob s xs a
--   -> {auto allFinite : AllFinite xs}
--   -> Prob s xs a
-- propagate p = sendIn (sendOut p) p

-- probOf
--   :  Semiring s
--   => Prob s xs a
--   -> {auto fin : AllFinite xs}
--   -> {auto elem : Elem x xs}
--   -> x
--   -> s
-- probOf {fin} {elem} p = margVecAny fin elem (sendOut p)

(>>=) : Prob s ys a -> (a -> Prob s xs b) -> Prob s (a::xs++ys) b
(>>=) = Bnd

pure : Eq a => a -> Prob Double [] a
pure x = Dst (\y => if y == x then 1.0 else 0.0)

bool : Prob Double [] Bool
bool = Dst (const 0.5)

implementation MaxBound Bool where
  maxBound = True

implementation MinBound Bool where
  minBound = False

implementation Enum Bool where
  pred True = False
  pred False = False
  toNat True = 1
  toNat False = 0
  fromNat Z = False
  fromNat _ = True

ands : Prob Double [Bool,Bool,Bool] Bool
ands = do
  x <- bool
  y <- bool
  z <- bool
  pure (x && y && z)

res : Double
res = linear ands True

f : Bool -> Double
f True = 0.5
f False = 0.5
