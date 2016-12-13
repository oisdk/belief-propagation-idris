module TaggedProb

import Marginalization
import Semiring
import HetVect
import Data.Morphisms

%default total
%access public export
%hide Prelude.Pairs.DPair.snd
%hide Prelude.Pairs.DPair.fst

mutual
  ||| Probability monad which keeps a list of the variables it contains
  ||| Prob s xs a = probability of `a`, given `xs`. `s` is the unit
  data Prob : (unit : Type) -> (given : List Type) -> (var : Type) -> Type where
    ||| Given variables xs, give probability of a.
    Dst : (Vect xs -> a -> s) -> Prob s xs a
    Bnd
      :  {xs, ys : List Type}
      -> {auto finite : AllFinite xs}
      -> MultiProb s xs ys
      -> Prob s ys b
      -> Prob s (xs++ys) b

  data MultiProb : (unit : Type) -> (given : List Type) -> (vars : List Type) -> Type where
    Nil  : MultiProb s [] []
    (::) : {x : Type} -> Prob s cs x -> MultiProb s xs ys -> MultiProb s (cs++xs) (x::ys)

mutual
  -- I want FOLDS for goodness' sake.
  getMultiProb : Semiring s => MultiProb s xs ys -> Vect xs -> Vect ys -> s
  getMultiProb [] = \_, _ => one
  getMultiProb (p::ps) {xs=cs++xs} {ys=x::ys}
      = \vxs, (y::vys) =>  prodFuncsV (hfnc y) (rfnc vys) vxs where
    rfnc : Vect ys -> Vect xs -> s
    rfnc vys vxs = (getMultiProb ps) vxs vys
    hfnc : x -> Vect cs -> s
    hfnc y vcs = getProb p vcs y


  getProb : Semiring s => Prob s xs a -> Vect xs -> a -> s
  getProb (Dst f) vs x = f vs x
  getProb (Bnd ps f) {xs=xs++ys} vs x = fdist vs x * mdist vs x  where
    fdist : Vect (xs++ys) -> a -> s
    fdist = lengthen (getProb f)
    mdist : Vect (xs++ys) -> a -> s
    mdist = const . uncurryLong (getMultiProb ps)

pure : (Semiring s, Eq a) => a -> Prob s [] a
pure x = Dst (\([]), y => if x == y then one else zer)

(>>=) : Semiring s => Prob s xs a -> (a -> Prob s ys b) -> Prob s (a::xs++ys) b
(>>=) p f
  = Dst (\(x::xs), y => prodFuncsV (flip (getProb p) x) (flip (getProb (f x)) y) xs)
