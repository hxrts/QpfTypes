import Qpf

-- Test 1: Dead parameter only (no universe polymorphism)
data SimpleVec (n : Nat) α where
  | nil : SimpleVec n α
  | cons : α → SimpleVec n α → SimpleVec n α

#check SimpleVec.Shape
#check SimpleVec.Shape.Applied
-- Expected: Shape.Applied : Nat → CurriedTypeFun 1

-- Test 2: Universe polymorphism only (no dead parameters)
data Pair.{u, v} (α : Type u) (β : Type v) where
  | mk : α → β → Pair α β

#check Pair.Shape.{u, v}
-- Expected: Shape : Type (max u v)

-- Test 3: Combined - dead param + universe polymorphism
data BoundedVec.{u} (n : Nat) (α : Type u) where
  | nil : BoundedVec n α
  | cons : Fin n → α → BoundedVec n α → BoundedVec n α

#check BoundedVec.Shape.{u}
#check BoundedVec.Shape.Applied.{u}
-- Expected: Shape.Applied.{u} : Nat → CurriedTypeFun.{u} 1

-- Test 4: Multiple dead parameters
data Matrix (m n : Nat) α where
  | mk : (Fin m → Fin n → α) → Matrix m n α

#check Matrix.Shape.Applied
-- Expected: Shape.Applied : Nat → Nat → CurriedTypeFun 1

-- Test 5: ITree (dead param in constructor)
codata ITree (α : Type) ε ρ where
  | ret : ρ → ITree α ε ρ
  | tau : ITree α ε ρ → ITree α ε ρ
  | vis : ∀ (a : α), (a → ITree α ε ρ) → ITree α ε ρ

#check ITree.Shape.Applied
-- Expected: Shape.Applied : Type → CurriedTypeFun 2
