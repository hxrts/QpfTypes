/-
# Universe Polymorphism Test

This file tests that the `data` macro correctly generates universe-polymorphic types.

After the fix to Qpf/Macro/Data.lean, these definitions should work with explicit
universe parameters.
-/

import Qpf

-- Test 1: Single universe parameter (should now work)
-- The generated HeadT, ChildT, and P should all be universe-polymorphic
data UList.{u} (α : Type u) where
  | nil : UList α
  | cons : α → UList α → UList α

#check UList.{0}  -- UList.{0} : Type → Type
#check UList.{1}  -- UList.{1} : Type 1 → Type 1

-- Test 2: Verify the generated types are universe-polymorphic
#check @UList.Shape.HeadT  -- Should be universe-polymorphic
#check @UList.Shape.ChildT
#check @UList.Shape.P

-- Test 3: Basic usage at different universe levels
def listOfNats : UList.{0} Nat := .cons 1 (.cons 2 .nil)
def listOfTypes : UList.{1} Type := .cons Nat (.cons Bool .nil)

-- Test 4: Codata with universe parameter
codata UStream.{u} (α : Type u) where
  | cons : α → UStream α → UStream α

#check UStream.{0}
#check UStream.{1}
