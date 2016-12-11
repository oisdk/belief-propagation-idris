module HetVect

%default total

infixr 7 ::

||| Heterogeneous list
public export
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

export
(++) : Vect xs -> Vect ys -> Vect (xs++ys)
[] ++ ws = ws
(v::vs) ++ ws = v :: vs ++ ws
