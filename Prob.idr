module Prob

import Marginalization
import Semiring
import HetVect

%default total
%access public export

-- TODO: convert to haskell, parallel, prove

mutual
  ||| Probability monad which keeps a list of the variables it contains
  ||| Prob s xs a = probability of `a`, given `xs`. `s` is the unit
  data Prob : Type -> Type -> Type where
    ||| change to (forall s. Semiring s => (a -> s) -> s) in order to avoid enum,
    ||| bounded constraints (maybe).
    Dst : (a -> s) -> Prob s a
    Bnd
      : {xs : List Type}
      -> {auto finite : AllFinite xs}
      -> MultiProb s xs
      -> (Vect xs -> Prob s b)
      -> Prob s b

  data MultiProb : Type -> List Type -> Type where
    Nil  : MultiProb s []
    (::) : {x : Type} -> Prob s x -> MultiProb s xs -> MultiProb s (x :: xs)

getProb : Semiring s => Prob s a -> a -> s
getProb (Dst f) = f
getProb (Bnd {xs} ps f) = \y => margVec (\ws => allMessages ws * getProb (f ws) y) where

  funcs : Semiring s => {ys : List Type} -> MultiProb s ys -> s -> Vect ys -> s
  funcs [] = \n, _ => n
  funcs (p::ps) =
    let m  = getProb p
        ms = funcs ps
    in \n, (v::vs) => ms (n * m v) vs -- change to not tail-recursive to make parallel

  allMessages : Vect xs -> s
  allMessages = funcs ps one

getProbPar : Semiring s => Prob s a -> a -> s
getProbPar (Dst f) = f
getProbPar (Bnd {xs} ps f) = \y => margVec (\ws => allMessages ws * getProb (f ws) y) where

  funcs : Semiring s => {ys : List Type} -> MultiProb s ys -> Vect ys -> s
  funcs [] = \_ => one
  funcs (p::ps) = \(v::vs) =>
    let m  = getProbPar p v -- Evaluate these in parallel (only currently possible in Haskell)
        ms = funcs ps vs
    in ms * m

  allMessages : Vect xs -> s
  allMessages = funcs ps
