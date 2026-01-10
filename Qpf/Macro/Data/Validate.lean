/-
# DataView Validation

This file contains validation logic for `data`/`codata` declarations.
It validates that the parsed DataView conforms to QPF requirements.
-/

import Qpf.Macro.Data.View

open Lean Meta Elab Elab.Command

namespace Qpf.Macro.Data.Validate

private def stripParens : Syntax → Syntax
  | Syntax.node _ ``Parser.Term.paren #[_, inner, _] => stripParens inner
  | stx => stx

private def isAllowedExplicitType (stx : Syntax) : Bool :=
  let stx := stripParens stx
  let k := stx.getKind
  k == ``Parser.Term.type || k == ``Parser.Term.sort || k == ``Parser.Term.prop

private def tryElabType (stx : Syntax) : CommandElabM (Option Expr) := do
  try
    let ty ← runTermElabM fun _ => Term.elabType stx
    pure (some ty)
  catch _ =>
    pure none

/--
  Raises informative errors when `data` or `codata` are used with unsupported specifications.
-/
def doSanityChecks (view : DataView) : CommandElabM DataView := do
  if view.liveBinders.isEmpty then
    if view.deadBinders.isEmpty then
      if view.command == .Codata then
        throwError "Due to a bug, codatatype without any parameters don't quite work yet. Please try adding parameters to your type"
      else
        throwError "Trying to define a datatype without variables, you probably want an `inductive` type instead"
    else
      throwErrorAt view.binders "You should mark some variables as live by removing the type ascription (they will be automatically inferred as `Type _`), or if you don't have variables of type `Type _`, you probably want an `inductive` type"

  let mut explicitUniverse? := view.explicitUniverse?
  match view.type? with
  | some t =>
      let ty? ← tryElabType t
      if let some ty := ty? then
        if ty.isForall then
          throwErrorAt t m!"Indexed families are not supported by QPFs. Got function type: {ty}"
        unless ty.isSort do
          throwErrorAt t m!"Explicit result type must be a sort (`Type`, `Sort`, or `Prop`). Got: {ty}"
        explicitUniverse? := some ty.sortLevel!
      if isAllowedExplicitType t then
        pure ()
      else
        throwErrorAt t "Only explicit result types of the form `Type`, `Type u`, `Type n`, `Type _`, `Prop`, or `Sort u` are supported. Indexed families (e.g., `Nat → Type`) are not supported by QPFs."
  | none => pure ()
  pure { view with explicitUniverse? }

end Qpf.Macro.Data.Validate
