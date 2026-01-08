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

data WrapProp (α : Type) : Prop where
  | intro : WrapProp α

#check WrapProp

/--
error: Indexed families are not supported by QPFs. Got function type: Nat → Type
-/
#guard_msgs in
data BadVec α : Nat → Type where
  | mk : BadVec α 0
