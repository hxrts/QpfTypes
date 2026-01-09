import Qpf

data SizedList α where
  | nil : SizedList α
  | cons : α → SizedList α → SizedList α
with
  size : Nat
  | .nil => 0
  | .cons _ t => t + 1

example : SizedList Nat → Nat := SizedList.size (α := Nat)

example {α : Type _} : SizedList.size (α := α) (SizedList.nil (α := α)) = 0 := by
  simp

example {α : Type _} (a : α) (t : SizedList α) :
    SizedList.size (α := α) (SizedList.cons (α := α) a t) = SizedList.size (α := α) t + 1 := by
  simp
