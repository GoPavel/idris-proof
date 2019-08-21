# idris-proofs

## Commutativity of addition
[Code](https://github.com/GoPavel/idris-proof/blob/master/proofs/CommutativityOfAddition.idr)

```idris
sym_plus : {x,y:Nat} -> x + y = y + x
```

## Transitivity of Divisibility
[Code](https://github.com/GoPavel/idris-proof/blob/master/proofs/TransitivityOfDivisibility.idr)

if b|a and b|c then c|a

on idris:
```idris
data Divb : Nat -> Nat -> Type where
  DivbAx1 : a = k*b -> a `Divb` b

theorem : a `Divb` b -> b `Divb` c -> a `Divb` c
```

## Euler circuit theorem(in progress)
[Code](https://github.com/GoPavel/idris-proof/blob/master/proofs/Euler_circuit.idr)

Proof of the famous graph theorem about necessary and sufficient condition Eulerian graph: it has exactly two vertices of odd degree.
