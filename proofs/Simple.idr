module Simple

%default total


sym_eq : x = y -> y = x
sym_eq Refl = Refl

tr_eq : x = y -> y = z -> x = z
tr_eq Refl Refl = Refl

congr : (P : a -> b) -> x = y -> P x = P y
congr f Refl = Refl


-- x = x + 0
sym_plus_z : {m : Nat} -> m = m + 0
sym_plus_z {m=Z} = Refl
-- sym_plus_z {m=(S k)} = congr S (sym_plus_z{m=k})
sym_plus_z {m=(S k)} = rewrite sym_plus_z{m=k} in Refl

-- S x = 1 + x
sym_plus_one_left : {m : Nat} -> S m = 1 + m
sym_plus_one_left = Refl

-- S x = x + 1
sym_plus_one_right : {m : Nat} -> S m = m + 1
sym_plus_one_right {m=Z} = Refl
sym_plus_one_right {m=(S k)} =
    rewrite sym_plus_one_right{m=k} in Refl

proof11 : {m : Nat} -> S m + m = S (m + m)
proof11 {m = Z}     = Refl
proof11 {m = (S k)} = Refl

proof12 : {m : Nat} -> {a : Nat} -> a + (S m) = S (a + m)
-- 0 + (S m) = S (0 + m)
proof12 {m=m} {a=Z} = Refl
proof12 {m=m} {a=(S k)} = rewrite proof12{m=m}{a=k} in Refl

-- S x + S x = S (S (x + x))
export
-- S (S x) + S (S x) = S (S (S S (x + x)))
sumSucc : {m : Nat} -> S m + S m = S (S (m + m))
-- -- S 0 + S 0 = S (S (0 + 0))
sumSucc {m=Z} = Refl
-- S (S k) + S (S k) = S (S ((S k) + (S k)))
sumSucc {m=m} = let rec = proof12{m=m}{a=m} -- (S m) + (S m) = S ((S m) + m)
             in rewrite rec
             in Refl

proof2 : {x: Nat} -> {y: Nat} -> S x + S y = S (S (x + y))
proof2 {x=Z} {y=Z}           = Refl
proof2 {x=Z} {y=(S k)}       = Refl
proof2 {x=(S k)}  {y=Z}      = rewrite proof2{x=k}{y=Z} in Refl
proof2 {x=(S kx)} {y=(S ky)} = rewrite proof2{x=kx}{y=(S ky)} in Refl


proof3 : {x, y: Nat} -> {y: Nat} -> S (x + y) = x + (S y)
proof3 {x=Z}{y=y} = Refl
proof3 {x=(S k)}{y=y} =      -- S (S k + y) = S k + (S y)
    let p = proof3{x=k}{y=y} --   S (k + y) = k + (S y)
    in congr S p
    -- rewrite proof3{x=k}{y=y} --   S (k + y) = k + (S y)
    -- in Refl                  --  (k + (S y) = k + (S y)
                                --  S (S k + y) = S (k + (S y))
    -- replace{P=\w => S (S k + y) = S w} (proof3{x=k}{y=y}) Refl{x=(S k + y)}


sym_plus : {x,y:Nat} -> x + y = y + x
sym_plus {x=Z}{y=Z}           = Refl
sym_plus {x=Z}{y=(S k)}       = sym_plus_z
sym_plus {x=(S k)}{y=Z}       = sym_eq sym_plus_z
-- sym_plus_z = 0 + x = x + 0
sym_plus {x=(S kx)}{y=(S ky)} =       --  S kx + y = y + S kx
    let p1 = sym_plus{x=kx}{y=(S ky)}    -- kx + y = y + kx
        p2 =  proof3{x=(S ky)}{y=kx} -- S (y + kx) = y + (S kx)
    in tr_eq (congr S p1) p2
-- proof3 : S (x + y) = x + (S y)


