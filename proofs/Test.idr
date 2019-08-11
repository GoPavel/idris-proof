module Simple

x : Int
x = 2

y : Nat
y = 2 + ?a

---------- Proofs ----------

Simple.a = proof
  intro n
  exact 2


