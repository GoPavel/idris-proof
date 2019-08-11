module Euler_circuit

import Data.Fin
import Data.Vect as V

data Graph1 : (n : Nat) -> Type where
  WithoutEdge : Graph1 k
  AddEdge     : (a: Fin k) -> (b: Fin k) -> Graph1 k -> Graph1 k

data Graph2 : (n : Nat) -> Vect n (List (Fin n)) -> Type where
  Graph2Empty     : {k: Nat} -> Graph2 k (replicate k Nil)
  Graph2EddEdge   : (a : Fin k) -> (b : Fin k) -> (g: Graph2 k es) -> Graph2 k (updateAt a (b::) es)

-- data EulerG : Graph n -> Type where
--   EulerEmpty : (g: Graph Z)   -> EulerG g
--   EulerAddLoop   : (a: Fin k) -> (g: Graph1 k ** EulerG g) -> EulerG (AddEdge a a g)
--   -- TODO

data EvenVect : Vect n a -> Type where
  EvenVectZero : EvenVect Nil
  EvenVectStep : EvenVect vs -> a -> b -> EvenVect (a::b::vs)

data EvenG : Graph2 n es -> Type where
  EvenGStep :  (g : Graph2 n es ** EvenG g) -> (i: Fin n) -> (o: Fin n)
            -> EvenGStep (Graph2 n ())
