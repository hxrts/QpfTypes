import Qpf

-- Test 1: Dead parameter only (no universe polymorphism)
data SimpleVec (n : Nat) α where
  | nil : SimpleVec n α
  | cons : α → SimpleVec n α → SimpleVec n α

#check SimpleVec.Shape
#check SimpleVec.Shape.Applied
-- Expected: Shape.Applied : Nat → CurriedTypeFun 2

-- Test 2: Universe polymorphism only (no dead parameters)
data UPair α β where
  | mk : α → β → UPair α β

#check @UPair.Shape
-- Expected: Shape is universe-polymorphic

-- Test 3: Combined - dead param + universe polymorphism
data BoundedVec (n : Nat) α where
  | nil : BoundedVec n α
  | cons : Fin n → α → BoundedVec n α → BoundedVec n α

#check BoundedVec.Shape
#check BoundedVec.Shape.Applied
-- Expected: Shape.Applied : Nat → CurriedTypeFun 2

-- Test 4: Multiple dead parameters
data MultiVec (m n : Nat) α where
  | nil : MultiVec m n α
  | cons : Fin m → Fin n → α → MultiVec m n α → MultiVec m n α

#check MultiVec.Shape.Applied
-- Expected: Shape.Applied : Nat → Nat → CurriedTypeFun 2

-- Test 5: Codata with dead parameter in constructor
codata CoVec (n : Nat) α where
  | cons : Fin n → α → CoVec n α → CoVec n α

#check CoVec.Shape
#check CoVec.Shape.Applied
-- Expected: Shape.Applied : Nat → CurriedTypeFun 2

-- Test 6: ITree-style codata (dead Type parameter)
codata TestITree (α : Type) ε ρ where
  | ret : ρ → TestITree α ε ρ
  | tau : TestITree α ε ρ → TestITree α ε ρ
  | vis : ε → (α → TestITree α ε ρ) → TestITree α ε ρ

#check TestITree.Shape
#check TestITree.Shape.Applied
-- Expected: Shape.Applied : Type → CurriedTypeFun 4
