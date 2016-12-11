module Marginalization

import Semiring
import HetVect
import Data.Morphisms

%default total
%access public export

prodFuncs
  : Semiring n
  => {xs, ys: List Type}
  -> (Vect xs -> n)
  -> (Vect ys -> n)
  -> Vect (xs++ys)
  -> n
prodFuncs {xs=[]} f g vs = f Nil * g vs
prodFuncs {xs=x::xs} f g (y :: z) = prodFuncs (f . (y::)) g z

||| A proof that every type in a given list belongs to a finite, bounded,
||| enumerable domain. Possibly better modelled in a more generic way (ie for 
||| arbitrary constraints).
data AllFinite : List Type -> Type where
  Empty : AllFinite []
  Extra
    :  (rest : AllFinite xs)
    -> (MinBound x, MaxBound x, Enum x)
    => AllFinite (x::xs)

||| Maybe reformulate this in a tail-recursive way.
marg : (Semiring n, MinBound a, MaxBound a, Enum a) => (a -> n) -> n
marg f = sum (map f [minBound .. maxBound])

margOnce
  : (Semiring n, MinBound t, MaxBound t, Enum t)
  => (Vect (t::ts) -> n) -> (Vect ts -> n)
margOnce f = (applyMor . marg) (\x => Mor (f . (x::)))

margVec
  : Semiring n
  => {xs : List Type}
  -> {auto prf : AllFinite xs}
  -> (Vect xs -> n) -> n
margVec {xs=[]} f = f []
margVec {xs=x::xs} {prf=Extra rest} f = margVec (margOnce f)

margVecL
  : Semiring n
  => {xs, ys: List Type}
  -> {auto prf : AllFinite ys}
  -> (Vect (xs++ys) -> n)
  -> Vect xs -> n
margVecL f [] =  margVec f
margVecL f (x :: xs) = margVecL (\ys => f (x::ys)) xs

margVecR
  : Semiring n
  => {xs, ys: List Type}
  -> (Vect (xs++ys) -> n)
  -> {auto prf : AllFinite xs}
  -> Vect ys
  -> n
margVecR f = applyMor (margVec (\xs => Mor (\ys => f (xs++ys))))

finiteDistL
  : {xs, ys : List Type}
  -> (prf : AllFinite (xs++ys))
  -> AllFinite xs
finiteDistL {xs=[]} prf = Empty
finiteDistL {xs=x::xs} (Extra rest) = Extra (finiteDistL rest)

finiteDistR
  : {xs,ys : List Type}
  -> (prf : AllFinite (xs++ys))
  -> AllFinite ys
finiteDistR {xs=[]} prf = prf
finiteDistR {xs=x::xs} (Extra rest) = finiteDistR {xs} rest
