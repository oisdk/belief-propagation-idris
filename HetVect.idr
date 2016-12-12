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

curryTypeV : (ts : List Type) -> (result : Type) -> Type
curryTypeV [] result = result
curryTypeV (t :: ts) result = t -> curryTypeV ts result

curryV : (f : Vect ts -> result) -> curryTypeV ts result
curryV f {ts = []} = f []
curryV f {ts = (t :: ts)} = \x => curryV (f . (x::))

uncurryV : (f : curryTypeV ts result) -> Vect ts -> result
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
