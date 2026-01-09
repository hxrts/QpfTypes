import Qpf

data SizedList α where
  | nil : SizedList α
  | cons : α → SizedList α → SizedList α
with
  size : Nat
  | .nil => 0
  | .cons _ t => t + 1

example : SizedList Nat → Nat := SizedList.size (α := Nat)
