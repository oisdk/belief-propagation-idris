module Prob

import Marginalization
import Semiring
import HetVect

%default total
%access public export

mutual
  ||| Probability monad which keeps a list of the variables it contains
  ||| Prob s xs a = probability of `a`, given `xs`. `s` is the unit
  data Prob : Type -> Type -> Type where
    ||| change to (forall s. Semiring s => (a -> s) -> s) in order to avoid enum,
    ||| bounded constraints (maybe).
    Dst : (a -> s) -> Prob s a
    ||| Monadic bind. Potentially better performance if applicatives are added.
    ||| Also: should a be added here?
    Bnd : {xs : List Type} -> {auto finite : AllFinite xs} -> MultiProb s xs -> (Vect xs -> Prob s b) -> Prob s b

  data MultiProb : Type -> List Type -> Type where
    Nil  : MultiProb s []
    (::) : {x : Type} -> Prob s x -> MultiProb s xs -> MultiProb s (x :: xs)

linear : Semiring s => Prob s a -> a -> s
linear (Dst f) y = f y
linear (Bnd {xs} ps f) y = margVec (\ws => allMessages ws * linear (f ws) y) where
  funcs : {ys : List Type} -> MultiProb s ys -> Vect ys -> s
  funcs [] = \_ => one
  funcs (p::ps) =
    let m  = linear p
        ms = funcs ps
    in \(v::vs) => m v * ms vs
  allMessages : Vect xs -> s
  allMessages = funcs ps

(>>=) : (MinBound a, MaxBound a, Enum a) => Prob s a -> (a -> Prob s b) -> Prob s b
x >>= f = Bnd [x] (\([y]) => f y)

pure : Eq a => a -> Prob Double a
pure x = Dst (\y => if y == x then 1.0 else 0.0)

bool : Prob Double Bool
bool = Dst (const 0.5)

implementation MaxBound Bool where maxBound = True

implementation MinBound Bool where minBound = False

implementation Enum Bool where
  pred True = False
  pred False = False
  toNat True = 1
  toNat False = 0
  fromNat Z = False
  fromNat _ = True

ands : Prob Double Bool
ands = do
  x <- bool
  y <- bool
  z <- bool
  pure (x && y && z)

res : Double
res = linear ands True

f : Bool -> Double
f True = 0.5
f False = 0.5
