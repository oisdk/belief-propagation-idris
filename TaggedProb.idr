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
    Dst : (Vect xs -> (a -> s) -> s) -> Prob s xs a
    Bnd
      :  {xs, ys : List Type}
      -> {auto finite : AllFinite xs}
      -> MultiProb s xs ys
      -> Prob s ys b
      -> Prob s (xs++ys) b
    -- Cmb
    --   :  {xs, ys : List Type}
    --   -> {auto finite : AllFinite xs}
    --   -> (Vect ys -> b)
    --   -> MultiProb s xs ys
    --   -> Prob s (xs++ys) b

  data MultiProb : (unit : Type) -> (given : List Type) -> (vars : List Type) -> Type where
    Nil  : MultiProb s [] []
    (::) : {x : Type} -> Prob s cs x -> MultiProb s xs ys -> MultiProb s (cs++xs) (x::ys)

mutual
  -- I want FOLDS for goodness' sake.
  getMultiProb : Semiring s => MultiProb s xs ys -> (MultiProb s xs ys, Vect xs -> Vect ys -> s)
  getMultiProb [] = ([], \_, _ => one)
  getMultiProb (p::ps) {xs=cs++xs} {ys=x::ys}
      = (fst htot :: fst rtot, \vxs, (y::vys) =>  prodFuncsV (hfnc y) (rfnc vys) vxs) where
    rtot : (MultiProb s xs ys, Vect xs -> Vect ys-> s)
    rtot = getMultiProb ps
    rfnc : Vect ys -> Vect xs -> s
    rfnc vys vxs = (snd rtot) vxs vys
    htot : (Prob s cs x, Vect cs -> x -> s)
    htot = getProb p
    hfnc : x -> Vect cs -> s
    hfnc y vcs = snd htot vcs y

  getProb : Semiring s => Prob s xs a -> (Prob s xs a, Vect xs -> a -> s)
  getProb (Dst x) = (Dst x, \_, _ => one)
  getProb (Bnd {finite} ps f) {xs=xs++ys} = (Bnd {finite} (fst mboth) (fst fboth), \vs,x => fdist vs x * mdist vs x) where
    fboth : (Prob s ys a, Vect ys -> a -> s)
    fboth = getProb f
    fdist : Vect (xs++ys) -> a -> s
    fdist = lengthen (snd fboth)
    mboth : (MultiProb s xs ys, Vect xs -> Vect ys -> s)
    mboth = getMultiProb ps
    mdist : Vect (xs++ys) -> a -> s
    mdist = const . uncurryLong (snd mboth)

-- pure : a -> Prob s [] a
-- pure x = Dst (\([]), f => f x)

mutual
  sendInMulti : Semiring s => MultiProb s xs ys -> Vect xs -> (Vect ys -> s) -> s
  sendInMulti [] vs f = f vs
  sendInMulti (p::ps) vs {xs=cs++xs} {ys=x::ys} f = sendIn (fst spt) (\y => sendInMulti ps (snd spt) (\ys => f (y::ys))) p where
    spt : (Vect cs, Vect xs)
    spt = split vs

  sendIn : Semiring s => Vect xs -> (a -> s) -> Prob s xs a -> s
  sendIn vs f (Dst g) = g vs f
  sendIn vs f (Bnd x y) {xs=xs++ys} = lhs (fst spt) (\zs => rhs zs * rhs (snd spt))  where
    rhs : Vect ys -> s
    rhs vs = sendIn vs f y
    lhs : Vect xs -> (Vect ys -> s) -> s
    lhs = sendInMulti x
    spt : (Vect xs, Vect ys)
    spt = split vs

-- prop : Semiring s => Prob s xs a -> Vect xs -> s
-- prop x vs = sendIn vs (getProb x vs) x

-- bool : Prob Double [] Bool
-- bool = Dst (\([]) => const 0.5)

-- ands : Prob Double [Bool,Bool] Bool
-- ands = Dst (\([x,y]), r => r (x && y))

