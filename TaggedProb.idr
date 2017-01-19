module TaggedProb

import Semiring
import Data.Morphisms
import HetVect
import Marginalization

-- %default total
%access public export

mutual
  data Prob : (unit : Type) -> (current : Type) -> Type where
    Dist : ((a -> s) -> s) -> Prob s a
    Fmap : (Vect xs -> b) -> ListProb s xs -> Prob s b
    Join : Prob s (Prob s a) -> Prob s a

  data ListProb : (unit : Type) -> (xs : List Type) -> Type where
    Nil : ListProb s []
    (::) : Prob s x -> ListProb s xs -> ListProb s (x::xs)

getProb : Prob s a -> (a -> s) -> s
getProb (Dist g) f = g f
getProb (Join x) f = getProb x (\a => getProb a f)
getProb (Fmap g ps) f = go g ps f where
  go : (Vect xs -> b) -> ListProb s xs -> (b -> s) -> s
  go f [] g = g (f [])
  go f (p :: ps) g = getProb p (\x => go (f . (x::)) ps g)

map : (a -> b) -> Prob s a -> Prob s b
map f (Dist g) = Dist (\h => g (h . f))
map f (Fmap g x) = Fmap (f . g) x
map f (Join x) = Join (map (\p => map f p) x)

(<$>) : (a -> b) -> Prob s a -> Prob s b
(<$>) = map


pure : a -> Prob s a
pure x = Fmap (\([]) => x) Nil

return : a -> Prob s a
return = pure

(<*>) : Prob s (a -> b) -> Prob s a -> Prob s b
(<*>) (Dist f) xs = Dist (\k => f (\c => getProb xs (k . c)))
(<*>) (Fmap f ps) p = Fmap (\(v::vs) => f vs v) (p::ps)
(<*>) (Join x) xs = Join (map (<*> xs) x)

join : Prob s (Prob s a) -> Prob s a
join = Join

(>>=) : Prob s a -> (a -> Prob s b) -> Prob s b
(>>=) p f = Join (map f p)

dice : Prob Double Int
dice = Dist (\f => Semiring.sum ( map (\n => f n / 6.0) [1 .. 6]) )

probOf : (Eq a, Semiring s) => a -> Prob s a -> s
probOf x p = getProb p (\y => if x == y then one else zer)

dices : Prob Double Int
dices = do
  x <- dice
  y <- dice
  return (x+y)
