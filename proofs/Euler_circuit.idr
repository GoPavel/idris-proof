module Euler_circuit

import Data.Fin
import Data.Vect as V

  -- data EulerG : Graph n -> Type where
  --   EulerEmpty : (g: Graph Z)   -> EulerG g
  --   EulerAddLoop   : (a: Fin k) -> (g: Graph1 k ** EulerG g) -> EulerG (AddEdge a a g)
  -- 

data Graph1 : (n : Nat) -> Type where
  WithoutEdge : Graph1 k
  AddEdge     : (a: Fin k) -> (b: Fin k) -> Graph1 k -> Graph1 k

data Graph2 : (n : Nat) -> Vect n (List (Fin n)) -> Vect n (List (Fin n)) -> Type where
  Graph2Empty     : {k: Nat} -> Graph2 k (replicate k Nil) (replicate k Nil)
  Graph2AddEdge   : (a : Fin k) -> (b : Fin k) -> (g: Graph2 k ies oes)
                  -> Graph2 k (updateAt b (a::) $ ies)
                              (updateAt a (b::) $ oes)

data EqLen : List a -> List a -> Type where
  EqLenZ : EqLen Nil Nil
  EqLenS : EqLen xs ys -> a -> b -> EqLen (a::xs) (b::ys)

data ZipPVect : (P : a -> b -> Type) -> Vect n a -> Vect n b -> Type where
  ZipPVectZ : {P: a -> b -> Type} -> ZipPVect P Nil Nil
  ZipPVectS : {P: a -> b -> Type} -> ZipPVect P xs ys -> (x: a) -> (y: b) -> P x y -> ZipPVect P (x::xs) (y::ys)

data Path : (head: Type) -> head -> Type where
  PathO : {a: Type} -> (x: a) -> (y: a) -> Path a y
  PathS : {a: Type} -> Path a x -> (y: a) -> Path a y

data ContainEdges : Path (Fin n) h -> (g: Graph2 n ies oes) -> Type where
  ContainEdgesO : (a: Fin n) -> (b: Fin n) -> ContainEdges (PathO a b) (Graph2AddEdge a b Graph2Empty)
  ContainEdgesS : (es: Path (Fin n) h) -> (g: Graph2 n ies oes) -> ContainEdges es g
               -> (a: Fin n) -> (b: Fin n) -> h = a -> ContainEdges (PathS es b) (Graph2AddEdge a b g)

data IsoGraph2 : (g1: Graph2 n1 ies1 oes1) -> (g2: Graph2 n2 ies2 oes2) -> Type where
  IsoGraph2eq : g1 = g2 -> IsoGraph2 g1 g2

delete_empty_node : (g: Graph2 (S k) (Nil::ies) (Nil::oes)) -> ZipPVect EqLen ies oes
                 -> (g': Graph2 k ies' oes' ** ZipPVect EqLen ies' oes')
delete_empty_node = ?q1

add_empty_node : (path: Path (Fin n) h) -> (g: Graph2 n ies oes) -> (contEd: ContainEdges path g') -> (isoG: IsoGraph2 g g')
              -> (path: Path (Fin n) h ** (ContainEdges path g'', IsoGraph2 g g''))
add_empty_node = ?q2

theorem : {n: Nat} -> (g: Graph2 n ies oes) -> ZipPVect EqLen ies oes
       -> Maybe (path: Path (Fin n) h ** (ContainEdges path g', IsoGraph2 g' g))
theorem Graph2Empty _ = Nothing
theorem g (ZipPVectS zipPVect [] [] (EqLenZ)) =
  let (g' ** zipPVect') = delete_empty_node g zipPVect
      (path' ** (contEd, isoG)) = case theorem g' zipPVect' of -- TODO: can't match `P path'` and `(A, B)`
         (Just x) => x
         Nothing  => absurd
  in Just $ ?add_empty_node path' g' contEd isoG

-- TODO: prove round trip add/delete empty node
{-
 g  ~  g'+1
 !      !
g-1  ~  g'
-}

