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

structure QpfComputedFieldView where
  ref       : Syntax
  modifiers : Modifiers
  fieldId   : Name
  type      : Syntax.Term
  matchAlts : TSyntax ``Parser.Term.matchAlts
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
  /-- Explicit result universe, when a result type annotation is provided. -/
  explicitUniverse? : Option Level := none
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
  /-- Computed field declarations attached to this data/codata definition. -/
  computedFields  : Array QpfComputedFieldView
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
  explicitUniverse? := {view.explicitUniverse?},
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
  explicitUniverse? := {view.explicitUniverse?},
  ctors           := {ctors},
  derivingClasses := <omitted>,
  command         := {view.command         },
  liveBinders     := {view.liveBinders     },
  deadBinders     := {view.deadBinders     },
  deadBinderNames := {view.deadBinderNames },
}"

/-! ## Parsing and Validation

Parsing (`dataSyntaxToView`) is in `Qpf.Macro.Data.Parse`.
Validation (`doSanityChecks`) is in `Qpf.Macro.Data.Validate`.
-/
