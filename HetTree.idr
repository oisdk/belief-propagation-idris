module HetTree

import Semiring

%default total
%access public export

data Tree a = Nil | End a | (::) (Tree a) (Tree a)

data BiVect : Tree Type -> Type where
  Leaf : BiVect Nil
  Node : a -> BiVect (End a)
  Branch : BiVect ls -> BiVect rs -> BiVect (ls::rs)

using (x : a, ls : Tree a, rs : Tree a)
  data Elem : a -> Tree a -> Type where
    Here  : Elem x (End x)
    Left  : Elem x ls -> Elem x (ls::rs)
    Right : Elem x rs -> Elem x (ls::rs)

remove : (x : a) -> (xs : Tree a) -> Elem x xs -> Tree a
remove x (End x) Here = Nil
remove x (ls :: rs) (Left  p) = remove x ls p :: rs
remove x (ls :: rs) (Right p) = ls :: remove x rs p

addBack
  : {xs : Tree Type}
  -> {x : Type}
  -> {auto elem : Elem x xs}
  -> (val : x)
  -> (vec : BiVect (remove x xs elem))
  -> BiVect xs
addBack {elem = Here} val vec = Node val
addBack {elem = (Left  x)} val (Branch ls rs) = Branch (addBack val ls) rs
addBack {elem = (Right x)} val (Branch ls rs) = Branch ls (addBack val rs)

data AllFinite : Tree Type -> Type where
  Empty : AllFinite Nil
  Both
    : (lhs : AllFinite ls)
    -> (rhs : AllFinite rs)
    -> AllFinite (ls::rs)
  Extra
    : (MinBound x, MaxBound x, Enum x)
    => AllFinite (End x)

marg : (Semiring n, MinBound a, MaxBound a, Enum a) => (a -> n) -> n
marg f = sum (map f [minBound .. maxBound])

margBiVec
: Semiring n
=> {xs : Tree Type}
-> {auto prf : AllFinite xs}
-> (BiVect xs -> n) -> n
margBiVec {xs=Nil} f = f Leaf
margBiVec {xs=End x} {prf=Extra} f = marg (\y => f (Node y))
margBiVec {xs=ls::rs} {prf=Both lp rp} f = margBiVec (\lhs => margBiVec (\rhs => f (Branch lhs rhs)))

margOnce : (Semiring n, Enum x, MinBound x, MaxBound x) => {xs : Tree Type} -> {auto elem : Elem x xs} -> (BiVect xs -> n) -> BiVect (remove x xs elem) -> n
margOnce {elem} f tr = marg (\x => f (addBack x tr))

split : {auto elem : Elem x xs} -> BiVect xs -> (x, BiVect (remove x xs elem))
split {elem = Here} (Node x) = (x, Leaf)
split {elem = (Left  p)} (Branch ls rs) = let (el,rm) = split {elem=p} ls in (el, Branch rm rs)
split {elem = (Right p)} (Branch ls rs) = let (el,rm) = split {elem=p} rs in (el, Branch ls rm)

pop : {auto elem : Elem x xs} -> BiVect xs -> BiVect (remove x xs elem)
pop {elem = Here} (Node x) = Leaf
pop {elem = (Left  p)} (Branch ls rs) = Branch (pop ls) rs
pop {elem = (Right p)} (Branch ls rs) = Branch ls (pop rs)
