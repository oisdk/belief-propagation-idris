module TaggedProb

import Marginalization
import Semiring
import HetVect
import Data.Morphisms

%default total
%access public export
%hide Prelude.Pairs.DPair.snd
%hide Prelude.Pairs.DPair.fst

||| Probability monad which keeps a list of the variables it contains
||| Prob s xs a = probability of `a`, given `xs`. `s` is the unit
data Prob : (unit : Type) -> (given : Type) -> (var : Type) -> Type where
  ||| Given variables xs, give probability of a.
  Dst : (a -> (b -> s) -> s) -> Prob s a b
  Bnd
    :  {xs, ys : List Type}
    -> {auto finite : AllFinite xs}
    -> Prob s (Vect xs) (Vect ys)
    -> Prob s (Vect ys) b
    -> Prob s (Vect (xs++ys)) b
  -- Cmb
  --   :  {xs, ys : List Type}
  --   -> {auto finite : AllFinite xs}
  --   -> (Vect ys -> b)
  --   -> MultiProb s xs ys
  --   -> Prob s (xs++ys) b

getProb : Semiring s => Prob s a b -> (Prob s a b, a -> (b -> s) -> s)
getProb (Dst f) = (Dst f, f)
getProb (Bnd {xs} {ys} {b} x y) = (Dst res, res) where
  lhs : (Prob s (Vect xs) (Vect ys), Vect xs -> (Vect ys -> s) -> s)
  lhs = getProb x
  rhs : (Prob s (Vect ys) b, Vect ys -> (b -> s) -> s)
  rhs = getProb y
  res : Vect (xs++ys) -> (b -> s) -> s
  res vs f = prodFuncsV (flip (snd lhs) imd) imd vs  where
    imd : Vect ys -> s
    imd = flip (snd rhs) f

observe : (x : a) -> Prob s (Vect xs) a -> {auto prf : Elem a xs} -> (ys ** Prob s (Vect ys) a)
observe x {a} (Dst f) {xs} {prf} = (remove a xs prf ** Dst (pop prf f x))
observe x (Bnd y z) = ?observe_rhs_2

-- mutual
--   sendInMulti : Semiring s => MultiProb s xs ys -> Vect xs -> (Vect ys -> s) -> s
--   sendInMulti [] vs f = f vs
--   sendInMulti (p::ps) vs {xs=cs++xs} {ys=x::ys} f = sendIn (fst spt) (\y => sendInMulti ps (snd spt) (\ys => f (y::ys))) p where
--     spt : (Vect cs, Vect xs)
--     spt = split vs

--   sendIn : Semiring s => Vect xs -> (a -> s) -> Prob s xs a -> s
--   sendIn vs f (Dst g) = g vs f
--   sendIn vs f (Bnd x y) {xs=xs++ys} = lhs (fst spt) (\zs => rhs zs * rhs (snd spt))  where
--     rhs : Vect ys -> s
--     rhs vs = sendIn vs f y
--     lhs : Vect xs -> (Vect ys -> s) -> s
--     lhs = sendInMulti x
--     spt : (Vect xs, Vect ys)
--     spt = split vs

-- -- prop : Semiring s => Prob s xs a -> Vect xs -> s
-- -- prop x vs = sendIn vs (getProb x vs) x

-- -- bool : Prob Double [] Bool
-- -- bool = Dst (\([]) => const 0.5)

-- -- ands : Prob Double [Bool,Bool] Bool
-- -- ands = Dst (\([x,y]), r => r (x && y))

