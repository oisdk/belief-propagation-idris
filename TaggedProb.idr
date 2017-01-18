module TaggedProb

import Semiring
import Data.Morphisms
import HetTree

%default total
%access public export

||| A free monad for probabilities, which remembers the variables it
||| contains
data Prob : (unit : Type) -> (variables : Tree Type) -> (current : Type) -> Type where
  Obs : ((a -> s) -> s) -> Prob s Nil a
  Dst :  (a -> s) -> Prob s (End a) a
  Bnd : Prob s ls a -> (a -> Prob s rs b) -> Prob s (ls::rs) b

observe : {xs : Tree Type} -> (val : x) -> {auto elem : Elem x xs} -> Prob s xs a -> Prob s (remove x xs elem) a
observe val (Dst _) {elem = Here} = Obs (\f => f val)
observe val (Bnd x f) {elem = (Left  p)} = Bnd (observe val x) f
observe val (Bnd x f) {elem = (Right p)} = Bnd x (observe val . f)

margOut
  : (MinBound x, MaxBound x, Enum x, Semiring s)
  => {xs : Tree Type}
  -> {auto elem : Elem x xs}
  -> Prob s xs a
  -> Prob s (remove x xs elem) a
margOut {elem = Here     } (Dst   f)  = Obs (\c => marg (\x => f x * c x))
margOut {elem = (Left  p)} (Bnd x f)  = Bnd (margOut x) f
margOut {elem = (Right p)} (Bnd x f)  = Bnd x (margOut {elem=p} . f)
