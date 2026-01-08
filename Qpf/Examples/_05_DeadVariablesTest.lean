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
✓ Single dead parameters work correctly
✓ Dead variables preserved in constructor arguments
⚠️ Multiple dead parameters may have issues
⚠️ Mapping over types with dead parameters has limitations

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
## Test 3: Multiple Dead Parameters (Currently Limited)

Multiple dead parameters currently have issues with QPF instance synthesis.
This is documented as a remaining limitation.
-/

-- data Tagged (tag : String) (n : Nat) α where
--   | mk : Fin n → α → Tagged tag n α

/-!
## Test 4: Functor Mapping (Currently Limited)

MvFunctor.map fails when dead parameters appear in constructor arguments.
This is related to how types like `Fin n` interact with the QPF instance.
-/

-- def testMap : BoundedVec 3 Nat → BoundedVec 3 String :=
--   MvFunctor.map (fun n => toString n)

/-!
## Summary

The dead variable implementation successfully:
1. Preserves dead parameter references in constructor arguments (e.g., `Fin n`)
2. Generates correct type signatures with dead parameters
3. Calculates arity based only on live parameters

Remaining work:
- Multiple dead parameters need additional support
- Functor mapping with dead parameter dependencies needs investigation
- Universe separation between dead and live parameters needs testing
-/

end DeadVariables
