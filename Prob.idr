module Prob

import Marginalization
import Semiring
import HetVect

%default total

||| Probability monad which keeps a list of the variables it contains
data Prob : Type -> List Type -> Type -> Type where
  ||| Observed value. Equivalent to "certain"
  Obs : a -> Prob s [] a
  ||| change to (forall s. Semiring s => (a -> s) -> s) in order to avoid enum,
  ||| bounded constraints (maybe).
  Dst : (a -> s) -> Prob s [a] a
  ||| Monadic bind. Potentially better performance if applicatives are added.
  Bnd : (a -> Prob s xs b) -> Prob s ys a -> Prob s (a::xs++ys) b

||| Step one of belief propagation.
sendOut  : Semiring s => Prob s xs a -> Vect xs -> s
sendOut (Obs x  ) y       = one
sendOut (Dst f  ) [x]     = f x
sendOut (Bnd f x) (y::ys) = prodFuncs (sendOut (f y)) (sendOut x) ys

||| Second part of belief propagation.
sendIn
  : {s : Type}
  -> Semiring s
  => (f : Vect xs -> s)
  -> {auto prf : AllFinite xs}
  -> Prob s xs a
  -> Prob s xs a
sendIn f (Obs x) = Obs x
sendIn f (Dst g) = Dst (\x => f [x] * g x)
sendIn {s} {prf=Extra rest} {xs=a::xs++ys} f (Bnd g x)
  = Bnd
    (\y => sendIn (margVecL {prf = ysBounds} f . (y::)) {prf = xsBounds} (g y))
    (sendIn (margVecR (margOnce f) {prf = xsBounds}) {prf = ysBounds} x)
  where
    xsBounds : AllFinite xs
    xsBounds = boundedDistL rest
    ysBounds : AllFinite ys
    ysBounds = boundedDistR rest

||| Full belief propagation.
propagate
: Semiring s
  => Prob s xs a
  -> {auto allBounded : AllFinite xs}
  -> Prob s xs a
propagate p = sendIn (sendOut p) p
