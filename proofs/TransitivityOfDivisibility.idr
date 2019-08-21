module TransitivityOfDivisibility

data Divb : Nat -> Nat -> Type where
  DivbAx1 : a = k*b -> a `Divb` b

lemma1 : a `Divb` b*c -> a `Divb` c
lemma1 {a=a}{b=b}{c=c} (DivbAx1{k=k} aEqKBC) =
  let aEqKBC' = trans aEqKBC $ multAssociative k b c
  in DivbAx1 aEqKBC'

theorem : a `Divb` b -> b `Divb` c -> a `Divb` c
theorem aDivbB (DivbAx1{k=kb} bEqKbC) =
  let aDivbB' = replace bEqKbC aDivbB
  in lemma1 aDivbB'
