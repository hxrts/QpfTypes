import Qpf

/-!
# Mutual Coinductive Spec Test

This mirrors the `MyS/MyT` mutual coinductive example from R13_01.
Since mutual `codata` is not supported yet, this file is a placeholder
for the expected macro syntax once implemented.
-/

/--
TODO: Replace with a mutual `codata` block when supported.
Example target syntax:
```
mutual
  codata MyS where
    | mkS : MyT → MyS

  codata MyT where
    | mkT : MyS → MyT
end
```
-/-
