/-
# Syntax Parsing for data/codata

This file contains the main parsing function `dataSyntaxToView` that transforms
`data`/`codata` syntax into a `DataView` structure.

This is heavily based on `inductiveSyntaxToView` from `Lean.Elab.Inductive`.
-/

import Qpf.Macro.Data.View
import Qpf.Macro.Data.Validate
import Qpf.Macro.Common

open Lean Meta Elab Elab.Command
open Parser.Command (declId)

open Macro (withQPFTraceNode)

namespace Qpf.Macro.Data.Parse

/-- Collect universe level names used in a syntax tree. -/
private partial def collectLevelNames (stx : Syntax) (levelNames : List Name) : List Name :=
  let rec go (s : Syntax) (acc : List Name) : List Name :=
    match s with
    | Syntax.ident _ _ name _ =>
        if levelNames.contains name then name :: acc else acc
    | _ => s.getArgs.foldl (fun acc s => go s acc) acc
  go stx [] |>.eraseDups

/--
  Parse a `data` or `codata` syntax node into a `DataView`.

  This is heavily based on `inductiveSyntaxToView` from `Lean.Elab.Inductive`.
-/
def dataSyntaxToView (modifiers : Modifiers) (decl : Syntax) : CommandElabM DataView :=
  withQPFTraceNode "dataSyntaxToView" (tag := "dataSyntaxToView") <| do

  -- `data`/`codata` declarations may be noncomputable (not sure about partial, but we allow it for now)
  -- checkValidInductiveModifier modifiers

  let (binders, type?) := expandOptDeclSig decl[2]

  let declId  : TSyntax ``declId := ⟨decl[1]⟩
  let ns ← getCurrNamespace
  let ⟨name, declName, levelNames, _docString?⟩ ← liftTermElabM do
    Term.expandDeclId ns (← Term.getLevelNames) declId modifiers
  -- addDeclarationRanges declName decl
  let ctors      ← decl[4].getArgs.mapM fun ctor => withRef ctor do
    /-
    ```
    def ctor := leading_parser optional docComment >> "\n| " >> declModifiers >> rawIdent >> optDeclSig
    ```
    -/
    let mut ctorModifiers ← elabModifiers ⟨ctor[2]⟩
    if let some leadingDocComment := ctor[0].getOptional? then
      if ctorModifiers.docString?.isSome then
        logErrorAt leadingDocComment "duplicate doc string"
      ctorModifiers := { ctorModifiers with docString? := some (⟨leadingDocComment⟩, false) }
    if ctorModifiers.isPrivate && modifiers.isPrivate then
      throwError "invalid 'private' constructor in a 'private' inductive datatype"
    if ctorModifiers.isProtected && modifiers.isPrivate then
      throwError "invalid 'protected' constructor in a 'private' inductive datatype"
    checkValidCtorModifier ctorModifiers
    let ctorName := ctor.getIdAt 3
    let ctorName := declName ++ ctorName
    let ctorName ← withRef ctor[3] <| applyVisibility ctorModifiers ctorName
    let (ctorBinders, type?) := expandOptDeclSig ctor[4]
    if let some (doc, _) := ctorModifiers.docString? then
      liftTermElabM <| addDocString ctorName ctorBinders doc
    return { ref := ctor, declId := ctor[3], modifiers := ctorModifiers, declName := ctorName, binders := ctorBinders, type? := type? : CtorView }
  let computedFields ← (decl[5].getOptional?.map (·[1].getArgs) |>.getD #[]).mapM fun cf => withRef cf do
    let modifiers ← elabModifiers ⟨cf[0]⟩
    let modifiers := { modifiers with computeKind := .noncomputable }
    return {
      ref := cf
      modifiers
      fieldId := cf[1].getId
      type := ⟨cf[3]⟩
      matchAlts := ⟨cf[4]⟩
    }
  let classes ← liftCoreM <| getOptDerivingClasses decl[6]


  let command ← DataCommand.fromSyntax decl[0]
  let (liveBinders, deadBinders) ← Macro.splitLiveAndDeadBinders binders.getArgs
  let (deadBinders, deadBinderNames) ← Macro.mkFreshNamesForBinderHoles deadBinders
  let deadBinderInfos := deadBinders.raw.mapIdx fun idx binder =>
    let name := deadBinderNames[idx]!.getId
    let universeNames := collectLevelNames binder levelNames
    { name, binder, universeNames }


  let view : DataView := {
    ref             := decl
    shortDeclName   := name
    derivingClasses := classes
    declId, modifiers, declName, levelNames
    binders, type?, ctors,
    explicitUniverse? := none
    command, liveBinders, deadBinders, deadBinderNames, deadBinderInfos
    computedFields
  }
  withQPFTraceNode "elaborated view …" <| do
    trace[QPF] m!"{view}"

  let view ← Validate.doSanityChecks view
  return view

end Qpf.Macro.Data.Parse
