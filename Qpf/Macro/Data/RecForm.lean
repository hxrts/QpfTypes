/-
# Recursion Form Analysis

This file analyzes constructor arguments to determine their recursion structure.
This is used during recursor generation to properly handle recursive arguments.

## Recursion Forms

- `nonRec`: Non-recursive argument (e.g., `α` in `cons : α → List α → List α`)
- `directRec`: Direct recursive argument (e.g., the `List α` in `cons`)
- `composed`: Composed recursion like `List (Tree α)` (not yet supported)

## Example

For `cons : α → R α → R α` where `R α` is the recursive type:
- First argument `α` is `nonRec`
- Second argument `R α` is `directRec`
-/

import Qpf.Macro.Data.Replace

open Lean.Parser (Parser)
open Lean Meta Elab.Command Elab.Term Parser.Term
open Lean.Parser.Tactic (inductionAlt)

/--
  Encodes how a constructor argument relates to recursion.

  - `nonRec stx`: A non-recursive argument with syntax `stx`
  - `directRec`: A direct recursive occurrence of the type being defined
  - `composed stx`: A composed recursion like `List (Tree α)` (not yet supported)
-/
inductive RecursionForm where
  | nonRec (stx : Term)
  | directRec
  | composed (stx : Term)  -- TODO: Add support for composed recursive types
deriving Repr, BEq

namespace RecursionForm

variable {m} [Monad m] [MonadQuotation m]

/-- Check if `search` appears anywhere in `top`. -/
private def containsStx (top : Term) (search : Term) : Bool :=
  (top.raw.find? (· == search)).isSome

/-- Extract the argument types from an arrow chain (excluding the result type). -/
partial def getArgTypes (v : Term) : List Term := match v.raw with
  | .node _ ``arrow #[arg, _, deeper] =>
     ⟨arg⟩ :: getArgTypes ⟨deeper⟩
  | rest => [⟨rest⟩]

/-- Reconstruct an arrow type from a list of argument types. -/
partial def toType (retTy : Term) : List Term → m Term
  | [] => pure retTy
  | hd :: tl => do `($hd → $(← toType retTy tl))

/--
  Extract the recursion forms from a constructor.

  Assumes the preprocessor has already run. Does not support polymorphic recursive types
  like `data Ql α | nil | l : α → Ql Bool → Ql α`.
-/
def extract (view : CtorView) (rec_type : Term) : List RecursionForm := do
  if let some type := view.type? then
    let type_ls := (getArgTypes ⟨type⟩).dropLast
    type_ls.map fun v =>
      if v == rec_type then .directRec
      else if containsStx v rec_type then .composed v
      else .nonRec v
  else []

/-- Extract recursion forms along with the constructor name (relative to `topName`). -/
def extractWithName (topName : Name) (view : CtorView) (rec_type : Term) : Name × List RecursionForm :=
  (view.declName.replacePrefix topName .anonymous, extract view rec_type)

/-- Replace the recursive type in a recursion form with a new type. -/
def replaceRec (old new : Term) : RecursionForm → Term
  | .nonRec x => x
  | .directRec => new
  | .composed x => ⟨Replace.replaceAllStx old new x⟩

/-- Convert a recursion form back to a term, using `recType` for recursive occurrences. -/
def toTerm (recType : Term) : RecursionForm → Term
  | .nonRec x | .composed x => x
  | .directRec => recType

end RecursionForm
