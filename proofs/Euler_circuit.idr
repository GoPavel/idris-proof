module Euler_circuit

import Data.Fin
import Data.Vect as V

data Graph1 : (n : Nat) -> Type where
  WithoutEdge : Graph1 k
  AddEdge     : (a: Fin k) -> (b: Fin k) -> Graph1 k -> Graph1 k

data Graph2 : (n : Nat) -> Vect n (List (Fin n)) -> Vect n (List (Fin n)) -> Type where
  Graph2Empty     : {k: Nat} -> Graph2 k (replicate k Nil) (replicate k Nil)
  Graph2AddEdge   : (a : Fin k) -> (b : Fin k) -> (g: Graph2 k ies oes)
                  -> Graph2 k (updateAt b (a::) $ ies)
                              (updateAt a (b::) $ oes)

-- data EulerG : Graph n -> Type where
--   EulerEmpty : (g: Graph Z)   -> EulerG g
--   EulerAddLoop   : (a: Fin k) -> (g: Graph1 k ** EulerG g) -> EulerG (AddEdge a a g)
--   -- TODO

data EqLen : List a -> List a -> Type where
  EqLenZ : EqLen Nil Nil
  EqLenS : EqLen xs ys -> a -> b -> EqLen (a::xs) (b::ys)

data ZipPVect : (P : a -> b -> Type) -> Vect n a -> Vect n b -> Type where
  ZipPVectZ : {P: a -> b -> Type} -> ZipPVect P Nil Nil
  ZipPVectS : {P: a -> b -> Type} -> ZipPVect P xs ys -> (x: a) -> (y: b) -> P x y -> ZipPVect P (x::xs) (y::ys)

data ContainEdge : List (Fin n, Fin n) -> (g: Graph2 n ies oes) -> Type where
  ContainEdgeZ : ContainEdge Nil Graph2Empty
  ContainEdgeS : ContainEdge es g -> (a: Fin n) -> (b: Fin n) -> ContainEdge ((a,b)::es) (Graph2AddEdge a b g)

theorem : (g: Graph2 n ies oes ** ZipPVect EqLen ies oes) -> (path ** ContainEdge path g)


  -- data EvenG = (g : Graph2 n ies oes ** ZipPVect ies oes EqLen)
