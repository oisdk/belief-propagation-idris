module Prob

import Marginalization
import Semiring
import HetVect

%default total
%access public export

data MultiArg : (Type -> Type) -> List Type -> Type -> Type where
  Single : (a -> f b) -> f a -> MultiArg f [a] b
  Multi  : MultiArg f as (b -> c) -> f b -> MultiArg f (b::as) c



||| Probability monad which keeps a list of the variables it contains
data Prob : Type -> List Type -> Type -> Type where
  ||| Observed value.
  Obs : a -> Prob s [] a
  ||| change to (forall s. Semiring s => (a -> s) -> s) in order to avoid enum,
  ||| bounded constraints (maybe).
  Dst : (a -> s) -> Prob s [a] a
  ||| Monadic bind. Potentially better performance if applicatives are added.
  ||| Also: should a be added here?
  Bnd : (a -> Prob s xs b) -> Prob s ys a -> Prob s (a::xs++ys) b
  Cmb : Prob s xs (a -> b) -> Prob s ys a -> Prob s (xs++ys) b

||| Step one of belief propagation.
sendOut  : Semiring s => Prob s xs a -> Vect xs -> s
sendOut (Obs x  ) y       = one
sendOut (Dst f  ) [x]     = f x
sendOut (Bnd f x) (y::ys) = prodFuncs (sendOut (f y)) (sendOut x) ys
sendOut (Cmb f x) ys      = prodFuncs (sendOut f) (sendOut x) ys

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
    (\y => sendIn (margVecL {prf = ysFinite} f . (y::)) {prf = xsFinite} (g y))
    (sendIn (margVecR (margOnce f) {prf = xsFinite}) {prf = ysFinite} x)
  where
    xsFinite : AllFinite xs
    xsFinite = finiteDistL rest
    ysFinite : AllFinite ys
    ysFinite = finiteDistR rest
sendIn {s} {prf} {xs=xs++ys} f (Cmb g x)
  = Cmb
    (sendIn (margVecL {prf = ysFinite} f) {prf = xsFinite} g)
    (sendIn (margVecR f {prf = xsFinite}) {prf = ysFinite} x)
  where
    xsFinite : AllFinite xs
    xsFinite = finiteDistL prf
    ysFinite : AllFinite ys
    ysFinite = finiteDistR prf

||| Full belief propagation.
propagate
  : Semiring s
  => Prob s xs a
  -> {auto allFinite : AllFinite xs}
  -> Prob s xs a
propagate p = sendIn (sendOut p) p
