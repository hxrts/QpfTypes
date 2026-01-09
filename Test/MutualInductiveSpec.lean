import Qpf

/-!
# Mutual Inductive Spec Test

This mirrors the `MyA/MyB` mutual inductive example from R13_01.
Currently this uses Lean's native `mutual` syntax; once the macro
supports mutual `data` blocks, this should be ported to `data`.
-/

mutual
  inductive MyA : Type
  | mk : MyB → MyA

  inductive MyB : Type
  | nil : MyB
  | cons : MyA → MyB → MyB
end

mutual
  def sizeA : MyA → Nat
  | MyA.mk b => sizeB b

  def sizeB : MyB → Nat
  | MyB.nil => 0
  | MyB.cons a b => sizeA a + sizeB b + 1
end

example : sizeB MyB.nil = 0 := rfl
