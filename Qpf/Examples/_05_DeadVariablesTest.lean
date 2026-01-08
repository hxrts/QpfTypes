/-
# Dead Variables Examples and Test Cases

This file demonstrates basic dead variable support in the QPF `data` macro.

## Background: Live vs Dead Parameters

In QPF definitions:
- **Live parameters**: Can be mapped over (functor positions)
  - Written without type annotations: `α`, `β`
  - Inferred to have kind `Type _`

- **Dead parameters**: Fixed parameters that cannot be mapped
  - Have explicit type annotations: `(n : Nat)`, `(cmp : α → α → Bool)`
  - Can be values, proofs, or functions
  - Do NOT correspond to functor positions

## Implementation Status

✓ Basic dead variable support implemented in `Qpf/Macro/Data/Replace.lean`
✓ Single and multiple dead parameters work correctly
✓ Dead variables preserved in constructor arguments
✓ Codata with dead parameters works

See `Qpf/Problems/P6_Dead_Variables.lean` for full problem description and solution details.
-/

import Qpf

namespace DeadVariables

/-!
## Test 1: Single Dead Parameter (Natural Number)

The `n : Nat` parameter is dead and should be preserved in `Fin n` without replacement.
-/

data BoundedVec (n : Nat) α where
  | nil : BoundedVec n α
  | cons : α → Fin n → BoundedVec n α → BoundedVec n α

#check BoundedVec
-- BoundedVec (n : ℕ) : CurriedTypeFun 1

#check BoundedVec.cons
-- BoundedVec.cons {α : Type} {n : ℕ} : α → Fin n → BoundedVec n α → BoundedVec n α

/-!
## Test 2: Function Type as Dead Parameter

The `(Fin n → α)` argument depends on the dead parameter `n`.
-/

data Repeat (n : Nat) α where
  | mk : (Fin n → α) → Repeat n α

#check Repeat
-- Repeat (n : ℕ) : CurriedTypeFun 1

#check Repeat.mk
-- Repeat.mk {n : ℕ} {α : Type} : (Fin n → α) → Repeat n α

/-!
## Test 3: Multiple Dead Parameters
-/

data MultiVec (m n : Nat) α where
  | nil : MultiVec m n α
  | cons : Fin m → Fin n → α → MultiVec m n α → MultiVec m n α

#check MultiVec.Shape.Applied
-- MultiVec.Shape.Applied : Nat → Nat → CurriedTypeFun 2

/-!
## Test 4: Codata with Dead Parameter
-/

codata TestITree (α : Type) ε ρ where
  | ret : ρ → TestITree α ε ρ
  | tau : TestITree α ε ρ → TestITree α ε ρ
  | vis : ε → (α → TestITree α ε ρ) → TestITree α ε ρ

#check TestITree.Shape.Applied
-- TestITree.Shape.Applied : Type → CurriedTypeFun 4

/-!
## Summary

The dead variable implementation successfully:
1. Preserves dead parameter references in constructor arguments (e.g., `Fin n`)
2. Generates correct type signatures with dead parameters
3. Calculates arity based only on live parameters

Remaining work:
- Universe separation between dead and live parameters needs more testing
- Collision detection between dead and fresh variables not yet implemented
-/

end DeadVariables
