/-
# DataView: Parsed View of data/codata Declarations

This file defines the `DataView` structure, which represents a parsed view of a `data` or
`codata` declaration. It's analogous to Lean's `InductiveView` but specialized for QPF types.

## Key Types

- `DataCommand`: Distinguishes between `data` (inductive) and `codata` (coinductive)
- `DataView`: Complete parsed view of a declaration, including:
  - Live binders (type parameters that can be mapped over)
  - Dead binders (fixed parameters like `n : Nat`)
  - Constructors and their types

## Live vs Dead Binders

- **Live binders**: Parameters of type `Type _` that appear as functor positions
  (e.g., `α` in `List α`). These are what the QPF can map over.

- **Dead binders**: Parameters with explicit non-Type annotations (e.g., `n : Nat`).
  These are fixed across the type and cannot be mapped over.
-/

import Mathlib.Data.QPF.Multivariate.Constructions.Cofix
import Mathlib.Data.QPF.Multivariate.Constructions.Fix

import Lean
import Qpf.Macro.Common

open Lean
open Meta Elab Elab.Command
open Parser.Term (bracketedBinder)
open Parser.Command (declId)

open Macro (withQPFTraceNode)

/-! ## DataCommand -/

inductive DataCommand where
  | Data
  | Codata
  deriving BEq, Inhabited

namespace DataCommand

def fromSyntax : Syntax → CommandElabM DataCommand
  | Syntax.atom _ "data"   => pure .Data
  | Syntax.atom _ "codata" => pure .Codata
  | stx => throwErrorAt stx "Expected either `data` or `codata`"

instance : ToString DataCommand where
  toString := fun
    | .Data => "data"
    | .Codata => "codata"

/--
  Return a syntax tree for `MvQPF.Fix` or `MvQPF.Cofix` when self is `Data`, resp. `Codata`.
-/
def fixOrCofix : DataCommand → Ident
  | .Data   => mkIdent ``_root_.MvQPF.Fix
  | .Codata => mkIdent ``_root_.MvQPF.Cofix

/--
  Return a syntax tree for `MvPFunctor.W` or `MvPFunctor.M` when self is `Data`, resp. `Codata`.
-/
def fixOrCofixPolynomial : DataCommand → Ident
  | .Data   => mkIdent ``_root_.MvPFunctor.W
  | .Codata => mkIdent ``_root_.MvPFunctor.M

end DataCommand

/-! ## DataView Structure -/

/--
  Parsed view of a `data` or `codata` declaration.

  This is analogous to Lean's `InductiveView` but specialized for QPF types.
  The key difference is the separation of binders into `liveBinders` and `deadBinders`.
-/
structure DeadBinderInfo where
  name         : Name
  binder       : Syntax
  universeNames : List Name
  deriving Inhabited

structure DataView where
  ref             : Syntax
  declId          : TSyntax ``declId
  modifiers       : Modifiers
  shortDeclName   : Name
  declName        : Name
  levelNames      : List Name
  binders         : Syntax
  type?           : Option Syntax
  ctors           : Array CtorView
  derivingClasses : Array DerivingClassView
  command         : DataCommand
  /-- Live binders: type parameters that can be mapped over (e.g., `α` in `List α`) -/
  liveBinders     : TSyntaxArray ``Parser.Term.binderIdent
  /-- Dead binders: fixed parameters with explicit types (e.g., `(n : Nat)`) -/
  deadBinders     : TSyntaxArray ``bracketedBinder
  /-- Names of dead binders for easy access -/
  deadBinderNames : Array Ident
  /-- Dead binder metadata, including syntactic universe usage. -/
  deadBinderInfos : Array DeadBinderInfo
    deriving Inhabited

namespace DataView

def deadLevelNames (view : DataView) : List Name :=
  view.deadBinderInfos.toList.foldl (fun acc info => acc ++ info.universeNames) [] |>.eraseDups

def liveLevelNames (view : DataView) : List Name :=
  let dead := view.deadLevelNames
  let live := view.levelNames.filter (fun n => !dead.contains n)
  if live.isEmpty && !view.liveBinders.isEmpty then
    view.levelNames
  else
    live

end DataView





/-! ## Conversion Functions -/

/--
  Convert a `DataView` to an `InductiveView` for use with Lean's inductive elaboration.

  Note: Some fields are not yet supported (computed fields, class inductives, sort polymorphism).
-/
def DataView.asInductive (view : DataView) : InductiveView := {
  ref             := view.ref
  declId          := view.declId
  modifiers       := view.modifiers
  shortDeclName   := view.shortDeclName
  declName        := view.declName
  levelNames      := view.levelNames
  binders         := view.binders
  type?           := view.type?
  ctors           := view.ctors
  derivingClasses := view.derivingClasses
  -- TODO: Add support for computed fields in data/codata declarations
  computedFields  := #[]
  isClass := false
  allowIndices := false
  allowSortPolymorphism := false
  docString? := none
}


/-! ## Binder Manipulation -/

open Lean.Parser in
/-- Push a new live binder onto the view. -/
def DataView.pushLiveBinder (view : DataView) (binderIdent : TSyntax ``Parser.Term.binderIdent) : DataView :=
  let liveBinders := view.liveBinders.push binderIdent
  let binders := view.binders.setArgs (view.binders.getArgs.push binderIdent)
  { view with liveBinders, binders }

/-- Pop the last live binder from the view. -/
def DataView.popLiveBinder (view : DataView) : DataView :=
  if view.liveBinders.size == 0 then
    view
  else
    let liveBinders := view.liveBinders.pop
    let binders := view.binders.setArgs (view.binders.getArgs.pop)
    { view with liveBinders, binders }

/-- Replace the constructors in the view. -/
def DataView.setCtors (view : DataView) (ctors : Array CtorView) : DataView :=
  { view with ctors }

/-- Add a suffix to the declaration name. -/
def DataView.addDeclNameSuffix (view : DataView) (suffix : String) : DataView :=
  let declName := Name.mkStr view.declName suffix
  let declId := mkNode ``Parser.Command.declId #[mkIdent declName, mkNullNode]
  let shortDeclName := Name.mkSimple suffix
  { view with declName, declId, shortDeclName }


/-! ## Expected Type Construction -/

/--
  Returns the fully applied form of the type to be defined.

  The `name` parameter allows the user to control what the const at the bottom of the type is.
  This lets the user get types that have the same parameters such as the DeepThunk types.
-/
def DataView.getExpectedTypeWithName (view : DataView) (name : Name) : Term :=
  Macro.getBinderIdents view.binders.getArgs false |> Syntax.mkApp (mkIdent name)

/-- Returns the fully applied form of the type to be defined. -/
def DataView.getExpectedType (view : DataView) : Term :=
  view.getExpectedTypeWithName view.shortDeclName

/-- Returns the fully applied, explicit (`@`) form of the type to be defined. -/
def DataView.getExplicitExpectedType (view : DataView) : CommandElabM Term :=
  let args := Macro.getBinderIdents view.binders.getArgs true
  `(@$(mkIdent view.shortDeclName):ident $args:term*)

/-! ## MessageData Instances -/

instance : ToMessageData CtorView where
  toMessageData ctor := m!"\{\
  modifiers := {ctor.modifiers},
  declName  := {ctor.declName},
  binders   := {ctor.binders},
  type?     := {ctor.type?},
}"

/-
We omit ref from the output, since it tends to dump a large amount of not
particularly interesting syntax -- especially considering ref is only used
as a reference to know where to throw an error
-/
instance : ToMessageData InductiveView where
  toMessageData view := m!"\{\
  declId          := {view.declId},
  modifiers       := {view.modifiers},
  ref             := <omitted>,
  declId          := {view.declId          },
  modifiers       := {view.modifiers       },
  shortDeclName   := {view.shortDeclName   },
  declName        := {view.declName        },
  levelNames      := {view.levelNames      },
  binders         := {view.binders         },
  type?           := {view.type?},
  ctors           := {view.ctors},
  derivingClasses := <omitted>,
}"

instance : ToMessageData DataView where
  toMessageData view := m!"\{\
  declId          := {view.declId},
  modifiers       := {view.modifiers},
  ref             := <omitted>,
  declId          := {view.declId          },
  modifiers       := {view.modifiers       },
  shortDeclName   := {view.shortDeclName   },
  declName        := {view.declName        },
  levelNames      := {view.levelNames      },
  binders         := {view.binders         },
  type?           := {view.type?},
  ctors           := {view.ctors},
  derivingClasses := <omitted>,
  command         := {view.command         },
  liveBinders     := {view.liveBinders     },
  deadBinders     := {view.deadBinders     },
  deadBinderNames := {view.deadBinderNames },
}"


private def CtorView.toStringImpl (ctor: CtorView) : String :=
  s!"\{
  modifiers := {ctor.modifiers},
  declName  := {ctor.declName},
  binders   := {ctor.binders},
  type?     := {ctor.type?},
}"

instance : ToString DataView where
  toString view :=
    let ctors := view.ctors.map CtorView.toStringImpl
    s!"\{
  declId          := {view.declId},
  modifiers       := {view.modifiers},
  ref             := {view.ref             },
  declId          := {view.declId          },
  modifiers       := {view.modifiers       },
  shortDeclName   := {view.shortDeclName   },
  declName        := {view.declName        },
  levelNames      := {view.levelNames      },
  binders         := {view.binders         },
  type?           := {view.type?},
  ctors           := {ctors},
  derivingClasses := <omitted>,
  command         := {view.command         },
  liveBinders     := {view.liveBinders     },
  deadBinders     := {view.deadBinders     },
  deadBinderNames := {view.deadBinderNames },
}"

/-! ## Parsing Syntax to View -/

private partial def collectLevelNames (stx : Syntax) (levelNames : List Name) : List Name :=
  let rec go (s : Syntax) (acc : List Name) : List Name :=
    match s with
    | Syntax.ident _ _ name _ =>
        if levelNames.contains name then name :: acc else acc
    | _ => s.getArgs.foldl (fun acc s => go s acc) acc
  go stx [] |>.eraseDups


/--
  Raises informative errors when `data` or `codata` are used with unsupported specifications.
-/
def DataView.doSanityChecks (view : DataView) : CommandElabM Unit := do
  if view.liveBinders.isEmpty then
    if view.deadBinders.isEmpty then
      if view.command == .Codata then
        throwError "Due to a bug, codatatype without any parameters don't quite work yet. Please try adding parameters to your type"
      else
        throwError "Trying to define a datatype without variables, you probably want an `inductive` type instead"
    else
      throwErrorAt view.binders "You should mark some variables as live by removing the type ascription (they will be automatically inferred as `Type _`), or if you don't have variables of type `Type _`, you probably want an `inductive` type"

  -- TODO: Allow types like `Type`, `Type 3`, or `Type u` and only throw an error for indexed families
  match view.type? with
  | some t => throwErrorAt t "Unexpected type; type will be automatically inferred. Note that inductive families are not supported due to inherent limitations of QPFs"
  | none => pure ()


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
  let classes ← liftCoreM <| getOptDerivingClasses decl[5]


  let command ← DataCommand.fromSyntax decl[0]
  let (liveBinders, deadBinders) ← Macro.splitLiveAndDeadBinders binders.getArgs
  let (deadBinders, deadBinderNames) ← Macro.mkFreshNamesForBinderHoles deadBinders
  let deadBinderInfos := deadBinders.raw.mapIdx fun idx binder =>
    let name := deadBinderNames[idx]!.getId
    let universeNames := collectLevelNames binder levelNames
    { name, binder, universeNames }


  let view := {
    ref             := decl
    shortDeclName   := name
    derivingClasses := classes
    declId, modifiers, declName, levelNames
    binders, type?, ctors,
    command, liveBinders, deadBinders, deadBinderNames, deadBinderInfos
  }
  withQPFTraceNode "elaborated view …" <| do
    trace[QPF] m!"{view}"

  view.doSanityChecks
  return view
