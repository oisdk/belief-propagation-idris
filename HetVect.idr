module HetVect

%default total
%access public export

infixr 7 ::

||| Heterogeneous list
data Vect : List Type -> Type where
  Nil  : Vect []
  (::) : t -> Vect ts -> Vect (t::ts)

-- Name hints for interactive editing
%name Vect vs, ws, xs, ys, zs

curried : (ts : List Type) -> (result : Type) -> Type
curried [] result = result
curried (t :: ts) result = t -> curried ts result

curryV : (f : Vect ts -> result) -> curried ts result
curryV f {ts = []} = f []
curryV f {ts = (t :: ts)} = \x => curryV (f . (x::))

uncurryV : (f : curried ts result) -> Vect ts -> result
uncurryV f [] = f
uncurryV f (x :: xs) = uncurryV (f x) xs

infixr 7 ++

(++) : Vect xs -> Vect ys -> Vect (xs++ys)
[] ++ ws = ws
(v::vs) ++ ws = v :: vs ++ ws

using (x:a, y:a, xs:List a)
  data Elem : a -> List a -> Type where
    Here  : Elem x (x :: xs)
    There : Elem x xs -> Elem x (y :: xs)

||| Nothing can be in an empty Vect
noEmptyElem : {x : a} -> Elem x [] -> Void
noEmptyElem Here impossible

data Subset : List a -> List a -> Type where
  EmptySet : Subset [] ys
  WithElem : (later : Subset xs ys) -> Elem x ys -> Subset (x::xs) ys

split : {xs, ys : List Type} -> Vect (xs++ys) -> (Vect xs, Vect ys)
split {xs = []} vs = ([], vs)
split {xs = (x :: xs)} (y :: ys)
  = let (lhs,rhs) = split ys
    in  (y :: lhs, rhs)

uncurryLong
  :  {xs, ys : List Type}
  -> (Vect xs -> Vect ys -> a)
  -> Vect (xs++ys)
  -> a
uncurryLong f = uncurry f . split

lengthen
  :  {xs, ys : List Type}
  -> (Vect ys -> a)
  -> Vect (xs++ys)
  -> a
lengthen {xs=_::xs} f (_::vs) = lengthen {xs} f vs
lengthen {xs=[]} f vs = f vs

