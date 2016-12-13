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
  getMultiProb : Semiring s => MultiProb s xs ys -> (MultiProb s xs ys, Vect xs -> Vect ys -> s)
  getMultiProb [] = ([], \_, _ => one)
  getMultiProb (p::ps) {xs=cs++xs} {ys=x::ys}
      = (fst head :: fst rest, \vxs, (y::vys) =>  prodFuncsV (hfnc y) (rfnc vys) vxs) where
    rest : (MultiProb s xs ys, Vect xs -> Vect ys -> s)
    rest = getMultiProb ps
    rfnc : Vect ys -> Vect xs -> s
    rfnc vys vxs = snd rest vxs vys
    head : (Prob s cs x, Vect cs -> x -> s)
    head = getProb p
    hfnc : x -> Vect cs -> s
    hfnc y vcs = snd head vcs y


  getProb : Semiring s => Prob s xs a -> (Prob s xs a, Vect xs -> a -> s)
  getProb (Dst f) = (Dst f, f)
  getProb (Bnd ps f) {xs=xs++ys} = ?rhs where
    fprop : (Prob s ys a, Vect ys -> a -> s)
    fprop = getProb f
    mprop : (MultiProb s xs ys, Vect xs -> Vect ys -> s)
    mprop = getMultiProb ps
    fdist : Vect (xs++ys) -> a -> s
    fdist = lengthen (snd fprop)
    mdist : Vect (xs++ys) -> a -> s
    mdist = const . uncurryLong (snd mprop)
      -- cmb : (Vect xs, Vect ys)
      -- cmb = split vs
      -- lhs : Vect xs
      -- lhs = fst cmb
      -- rhs : Vect ys
      -- rhs = snd cmb
    -- (fx,fd) = getProb f
    -- rhs ws y = margVecR getProb (f ws) y
    -- (Bnd ps f, \ws => (\y => allMessages ws * getProb (f ws) y))
    -- This function is written in a somewhat strange way to highlight
    -- the parallel nature of the recursive call to getProb.
    -- funcs : Semiring s => {ys : List Type} -> MultiProb s ys zs -> s -> Vect ys -> s
    -- funcs [] n = \_ => n
    -- funcs (p::ps) n =
    --   let (up,m) = getProb p
    --       ms = funcs ps
    --   in \(v::vs) => ms (n * m v) vs -- change to not tail-recursive to make parallel
    -- allMessages : Vect xs -> s
    -- allMessages = funcs ps one
 
