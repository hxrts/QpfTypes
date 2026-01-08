import Qpf

-- Explicit result type annotations should be accepted.
data List0 α : Type where
  | nil : List0 α
  | cons : α → List0 α → List0 α

#check List0
#check List0.Shape

data List1 α : Type 1 where
  | nil : List1 α
  | cons : α → List1 α → List1 α

#check List1

universe u

data ListU.{u} α : Type u where
  | nil : ListU α
  | cons : α → ListU α → ListU α

#check @ListU

data ListSort.{u} α : Sort (u+1) where
  | nil : ListSort α
  | cons : α → ListSort α → ListSort α

#check @ListSort

/--
error: Only explicit result types of the form `Type`, `Type u`, `Type n`, or `Sort u` are supported. Indexed families (e.g., `Nat → Type`) are not supported by QPFs.
-/
#guard_msgs in
data BadVec α : Nat → Type where
  | mk : BadVec α 0
