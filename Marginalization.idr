module Marginalization

import Semiring
import HetVect
import Data.Morphisms

%default total
%access public export

prodFuncsV
  : Semiring n
  => {xs, ys: List Type}
  -> (Vect xs -> n)
  -> (Vect ys -> n)
  -> Vect (xs++ys)
  -> n
prodFuncsV {xs=[]} f g vs = f Nil * g vs
prodFuncsV {xs=x::xs} f g (y :: z) = prodFuncsV (f . (y::)) g z

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

-- elemConforms : {x : Type} -> {xs : List Type} -> (conform : AllFinite xs) -> (el : Elem x xs) -> Enum x
-- elemConforms (Extra rest) Here = Enum x
-- elemConforms conform (There x) = ?elemConforms_rhs_2

margVecAny
  :  Semiring n
  => {x : Type}
  -> {xs : List Type}
  -> (fin : AllFinite xs)
  -> (elem : Elem x xs)
  -> (Vect xs -> n)
  -> x -> n
margVecAny (Extra rest) Here f x = margVec {prf = rest} (f . (x::))
margVecAny (Extra rest) (There z) f x = margVecAny rest z (margOnce f) x

-- Can almost certainly be written quicker.
margAll
  :  Semiring s
  => {xs : List Type}
  -> {auto finite : AllFinite xs}
  -> curried xs s
  -> s
margAll = go where
  go
    :  Semiring s
    => {xs : List Type}
    -> {auto finite : AllFinite xs}
    -> curried xs s
    -> s
  go {finite = Empty} m = m
  go {finite = (Extra rest)} m =
    sum (map (go . m) [minBound .. maxBound])

prodFuncs
  : Semiring n
  => {xs: List Type}
  -> curried xs n
  -> curried xs n
  -> curried xs n
prodFuncs {xs=[]} x y = x * y
prodFuncs {n} {xs=x::xs} f g
  = \y => prodFuncs {n} {xs} (f y) (g y)


-- margSubset
--   : {n : Type}
--   -> Semiring n
--   => {xs, ys : List Type}
--   -> {auto sub : Subset ys xs}
--   -> {auto fin : AllFinite xs}
--   -> (Vect xs -> n)
--   -> Vect ys -> n
-- margSubset {sub = EmptySet} f [] = margVec f
-- margSubset {sub = WithElem later elem}
