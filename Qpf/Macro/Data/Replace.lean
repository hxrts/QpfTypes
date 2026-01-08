/-
# Shape Extraction Logic

This file contains the core "shape" extraction logic for the `data`/`codata` macro.

## Overview

The shape extraction process transforms a user's type definition into a polynomial functor
representation. This involves:

1. **Replacing type expressions with fresh variables**: Each unique type expression in
   constructor arguments is replaced with a fresh type variable, ensuring repeated
   occurrences map to the same variable.

2. **Handling dead variables**: Parameters that are not functorial (e.g., `n : Nat` in
   `BoundedVec n α`) are preserved as-is rather than being replaced.

3. **Building constructor argument tracking**: The `CtorArgs` structure tracks which
   arguments correspond to which type variables.

## Key Types

- `Replace`: State monad tracking new parameters and dead variable names
- `CtorArgs`: Tracks constructor argument mappings per type variable
- `ReplaceM`: State monad for the replacement process

## Dead Variable Handling

Dead variables (those with explicit type annotations that are not `Type _`) are preserved
during shape extraction. The `shapeOf'` function checks if an argument contains a dead
variable reference and keeps it as-is rather than replacing it with a fresh variable.

This allows:
- Dead variables to live in different universes from live ones
- The shape functor to properly depend on dead parameters
- Types like `Fin n` where `n : Nat` is a dead parameter to be preserved
-/

import Lean

import Qpf.Macro.Common
import Qpf.Macro.Data.View

open Lean Meta Elab.Command Elab.Term
open Macro (withQPFTraceNode)

structure CtorArgs where
  (args : Array Name)
  (per_type : Array (Array Name))

structure Replace where
  (newParameters : Array (Name × Term))
  (ctor: CtorArgs)
  /-- Names of dead variables that should not be replaced -/
  (deadVarNames : Array Name := #[])
  /-- Names of live variables (functor parameters) -/
  (liveVarNames : Array Name := #[])

def Replace.vars (r : Replace) : Array Name := r.newParameters.map Prod.fst
def Replace.expr (r : Replace) : Array Term := r.newParameters.map Prod.snd

variable (m) [Monad m] [MonadQuotation m] [MonadError m] [MonadTrace m] [MonadOptions m]
              [AddMessageContext m] [MonadLiftT IO m]

private abbrev ReplaceM := StateT Replace m

variable {m}

private def Replace.new (deadVarNames : Array Name := #[]) (liveVarNames : Array Name := #[]) : m Replace :=
  do pure ⟨#[], ⟨#[], #[]⟩, deadVarNames, liveVarNames⟩

private def CtorArgs.reset : ReplaceM m Unit := do
  let r ← StateT.get
  let n := r.vars.size
  let ctor : CtorArgs := ⟨#[], (Array.range n).map fun _ => #[]⟩
  StateT.set { r with ctor }

private def CtorArgs.get : ReplaceM m CtorArgs := do
  pure (←StateT.get).ctor

/-- The arity of the shape type created *after* replacing, i.e., the size of `r.newParameters` -/
def Replace.arity (r : Replace) : Nat :=
  r.newParameters.size

def Replace.getBinderIdents (r : Replace) : Array Ident :=
  r.vars.map mkIdent

open Parser.Term in
def Replace.getBinders {m} [Monad m] [MonadQuotation m] (r : Replace) : m <| TSyntax ``bracketedBinder := do
  let names := r.getBinderIdents
  `(bracketedBinderF | ($names* : Type _ ))

/-! ## Core Replacement Logic -/

/--
  Get or create an identifier for a type expression.

  If the expression has been seen before, returns the existing identifier.
  Otherwise, creates a fresh identifier and records the mapping.

  **Important**: Uses `{ r with ... }` syntax to preserve `deadVarNames` across state updates.
-/
private def ReplaceM.identFor (stx : Term) : ReplaceM m Ident := do
  let r ← StateT.get
  let ctor := r.ctor
  let argName ← mkFreshBinderName
  let args := ctor.args.push argName

  let name ← match r.expr.idxOf? stx with
  | some id => do
      -- Expression already seen; reuse existing variable
      let per_type := ctor.per_type.set! id $ (ctor.per_type[id]!).push argName
      let ctor := { args, per_type }
      StateT.set { r with ctor }
      pure $ r.vars[id]!
  | none => do
      -- New expression; create fresh variable
      let per_type := ctor.per_type.push #[argName]
      let name ← mkFreshBinderName
      StateT.set { r with newParameters := r.newParameters.push (name, stx), ctor := { args, per_type } }
      pure name

  return mkIdent name

/-! ## Variable Detection -/

/-- Check if a syntax node is an identifier matching one of the given variable names. -/
private def isNamedVariable (stx : Syntax) (varNames : Array Name) : Bool :=
  match stx with
  | Syntax.ident _ _ name _ => varNames.contains name
  | _ => false

/-- Check if a syntax node contains a reference to any of the given variable names. -/
private partial def containsVariable (stx : Syntax) (varNames : Array Name) : Bool :=
  if isNamedVariable stx varNames then true
  else match stx with
  | Syntax.node _ _ args => args.any (containsVariable · varNames)
  | _ => false

/-! ## Shape Extraction -/

open Lean.Parser in
/--
  Given a sequence of (non-dependent) arrows, replace each unique expression in between the arrows
  with a fresh variable, such that repeated occurrences of the same expression map to the same
  variable.

  **Dead variable handling**: Arguments that depend only on dead variables (and no live variables)
  are NOT replaced. They are kept as-is to preserve the dependency on dead parameters.
  For example, in `data BoundedVec (n : Nat) α`, an argument of type `Fin n` is preserved.
  Arguments that mention any live variable are still replaced, even if they also mention
  dead variables (e.g., `α → ITree α ε ρ`).
-/
private partial def shapeOf' : Syntax → ReplaceM m Syntax
  | Syntax.node _ ``Term.arrow #[arg, arrow, tail] => do
    let r ← StateT.get
    -- If the argument depends only on dead variables, keep it as-is
    let hasDead := containsVariable arg r.deadVarNames
    let hasLive := containsVariable arg r.liveVarNames
    let ctor_arg ← if hasDead && !hasLive then
      -- Preserve dead argument in the constructor type, but still record its binder name
      let argName ← mkFreshBinderName
      let ctor := { r.ctor with args := r.ctor.args.push argName }
      StateT.set { r with ctor }
      pure arg
    else
      (ReplaceM.identFor ⟨arg⟩ : ReplaceM m Ident)
    let ctor_tail ← shapeOf' tail

    pure $ mkNode ``Term.arrow #[ctor_arg, arrow, ctor_tail]

  | ctor_type =>
      pure ctor_type

open Lean.Parser in
/-- Given a sequence of (non-dependent) arrows, change the last expression into `res_type`. -/
private partial def setResultingType (res_type : Syntax) : Syntax → ReplaceM m Syntax
  | Syntax.node _ ``Term.arrow #[arg, arrow, tail] => do
    let tail ← setResultingType res_type tail
    pure $ mkNode ``Term.arrow #[arg, arrow, tail]
  | _ =>
      pure res_type

/--
  For indexed families, prepend explicit binders for index variables to a constructor type.

  **Example transformation**:
  - Input constructor type: `α → Fin n → rec → ResultType`
  - Index names: `[α, rec]`
  - Output: `(α : Type _) → (rec : Type _) → α → Fin n → rec → ResultType`

  The index variables are inserted at the FRONT as explicit named binders.
-/
private def prependIndexBinders (indexNames : Array Name) (ctorType : Syntax) : ReplaceM m Syntax := do
  let mut result := ctorType
  for indexName in indexNames.reverse do
    let indexIdent := mkIdent indexName
    let resultTerm : Term := ⟨result⟩
    result ← `(($indexIdent : Type _) → $resultTerm)
  pure result

/-! ## Helper Functions -/

-- TODO: Deprecate in favor of `{ ctor with type? }` syntax
def CtorView.withType? (ctor : CtorView) (type? : Option Syntax) : CtorView := {
  ctor with type?
}

/-! ## Running the Replacement Monad -/

/-- Runs the given action with a fresh instance of `Replace`. -/
def Replace.run (deadVarNames : Array Name := #[]) (liveVarNames : Array Name := #[]) : ReplaceM m α → m (α × Replace) :=
  fun x => do
    let r ← Replace.new deadVarNames liveVarNames
    StateT.run x r

/--
  Parse `Syntax` for an explicit binder into a `BinderView`.

  This duplicates parts of `Lean.Elab.Term.toBinderViews`; this is required because
  the latter is private.
-/
def getBinderView (ref : Syntax) : m BinderView := match ref with
  | .node _ `Lean.Parser.Term.explicitBinder
    #[_, id, (.node _ `null #[_, ty]), _, _] =>
    return .mk ref id ty .default
  | _ => Elab.throwUnsupportedSyntax

/-! ## Constructor Preprocessing -/

/--
  Preprocesses constructors by converting explicit binders to arrow types.

  Takes a `DataView` with possibly explicit binders and transforms them into
  (non-dependent) arrow types. Also infers output types when not specified.

  **Example**: `| cons (x : α) (xs : List α)` becomes `| cons : α → List α → List α`
-/
def preProcessCtors (view : DataView) : m DataView := do
  let ctors ← view.ctors.mapM fun ctor => do
    let namedArgs ← ctor.binders.getArgs.mapM getBinderView
    let flatArgs :=
      (namedArgs.map (fun b => b.id.getArgs.map (fun _ => ⟨b.type⟩)))
      |>.flatten.reverse

    let ty := if let some x := ctor.type? then x else view.getExpectedType
    let out_ty ← flatArgs.foldlM (fun acc curr => `($curr → $acc)) (⟨ty⟩)

    pure { ctor with binders := .missing, type? := some out_ty }

  pure { view with ctors }

/-! ## Shape Extraction from Constructors -/

/--
  Extract the constructors for a "shape" functor from the original constructors.

  This is the main entry point for shape extraction. It:
  1. Registers all live binders as type variables
  2. Processes each constructor, replacing type expressions with fresh variables
  3. Builds the result type with proper dead/live parameter application

  **Syntactic equality**: Uses simple syntactic comparison for type equality.
  For example, `Nat` and `ℕ` are treated as different types.

  **Dead variable preservation**: Arguments containing dead variable references
  (from `view.deadBinderNames`) are NOT replaced - they are preserved as-is
  so that the shape functor properly depends on dead parameters.
-/
def Replace.shapeOfCtors (view : DataView) (shapeIdent : Syntax)
    : m ((Array CtorView × Array CtorArgs) × Replace) := do
  let deadVarNames := view.deadBinderNames.map (·.getId)
  let liveVarNames := view.liveBinders.map fun var =>
    let raw := var.raw
    if raw.getKind == ``Parser.Term.binderIdent then
      raw[0].getId
    else
      raw.getId

  Replace.run deadVarNames liveVarNames <| do
    -- Step 1: Register all live binders as type variables
    for var in view.liveBinders do
      let varIdent : Ident := ⟨if var.raw.getKind == ``Parser.Term.binderIdent then
        var.raw[0]
      else
        var.raw
      ⟩
      let varTerm ← `($varIdent:ident)
      let _ ← ReplaceM.identFor varTerm

    -- Step 2: Process each constructor
    let pairs ← view.ctors.mapM fun ctor => do
      -- Preprocessor should have already converted binders to arrow types
      if !ctor.binders.isNone then
        throwErrorAt ctor.binders "Constructor binders are not supported yet, please provide all arguments in the type"

      trace[Qpf.Data] "{ctor.declName}: {ctor.type?}"

      CtorArgs.reset
      let type? ← ctor.type?.mapM $ shapeOf'
      pure (CtorView.withType? ctor type?, ← CtorArgs.get)

    let r ← StateT.get
    let ctors := pairs.map Prod.fst

    -- Build constructor argument tracking
    -- NOTE: Using appendList due to Array.append stack overflow issue in older Lean versions
    let ctorArgs := pairs.map fun ⟨_, ctorArgs⟩ =>
        let per_type := ctorArgs.per_type
        let diff := r.vars.size - ctorArgs.per_type.size
        let per_type := per_type.appendList $ (List.range diff).map (fun _ => (#[] : Array Name))
        ⟨ctorArgs.args, per_type⟩

    -- Step 3: Build result type: Shape dead_params live_params
    let deadBinderIdents := view.deadBinderNames
    let liveBinderIdents := r.getBinderIdents
    let shapeWithDeadParams := Syntax.mkApp (TSyntax.mk shapeIdent) deadBinderIdents
    let res := Syntax.mkApp shapeWithDeadParams liveBinderIdents

    -- Step 4: Update constructor result types
    let ctors ← ctors.mapM fun ctor => do
      let type? ← ctor.type?.mapM fun ty => do
        setResultingType res ty
      pure { ctor with type? }

    pure (ctors, ctorArgs)

/-! ## Syntax Replacement Utilities -/

/-- Replace syntax in *all* subexpressions (recursive). -/
partial def Replace.replaceAllStx (find replace stx : Syntax) : Syntax :=
  if stx == find then
    replace
  else
    stx.setArgs (stx.getArgs.map (replaceAllStx find replace))

open Parser in
/--
  Given a sequence of arrows `e₁ → e₂ → ... → eₙ`, check that `eₙ == recType`, and replace all
  *other* occurrences (i.e., in `e₁ ... eₙ₋₁`) of `recType` with `newParam`.

  This is used to make a recursive type definition non-recursive by replacing self-references
  with a fresh type variable.
-/
partial def Replace.replaceStx (recType newParam : Term) : Term → MetaM Term
  | ⟨stx⟩ => match stx with
    | stx@(Syntax.node _ ``Term.arrow #[arg, arrow, tail]) => do
        pure <| TSyntax.mk <| stx.setArgs #[
          replaceAllStx recType newParam arg,
          arrow,
          ← replaceStx recType newParam ⟨tail⟩
        ]

    | stx@(Syntax.node _ ``Term.arrow _) =>
        throwErrorAt stx "Internal bug: encountered an unexpected form of arrow syntax"

    | stx@(Syntax.node _ ``Term.depArrow _) =>
        throwErrorAt stx "Dependent arrows are not supported, please only use plain arrow types"

    | ctor_type =>
        if ctor_type != recType then
          throwErrorAt ctor_type m!"Unexpected constructor resulting type; expected {recType}, found {ctor_type}"
        else
          pure ⟨ctor_type⟩

instance : Coe Ident (TSyntax ``Parser.Term.binderIdent) := ⟨
  fun id => mkNode _ #[id]
⟩

/-! ## Non-Recursive Transformation -/

open Parser
/--
  Makes a type specification non-recursive by replacing all recursive occurrences with a fresh
  bound variable.

  Simultaneously checks that each constructor type, if given, is indeed a sequence of arrows
  `... → ... → ...` culminating in the type to be defined.

  **Example**: For `data List α | nil | cons : α → List α → List α`, this transforms
  `List α` in the constructor types to a fresh variable `rec`, yielding
  `cons : α → rec → List α`.
-/
def makeNonRecursive (view : DataView) : MetaM (DataView × Name) :=
  withQPFTraceNode "makeNonRecursive" <| do
  let expected := view.getExpectedType

  let rec ← mkFreshBinderName
  let recId := mkIdent rec

  let view := view.pushLiveBinder recId

  let ctors ← view.ctors.mapM fun ctor => do
    let type? ← ctor.type?.mapM (Replace.replaceStx expected recId <| TSyntax.mk ·)
    return CtorView.withType? ctor type?

  let view := view.setCtors ctors
  trace[QPF] "non-recursive view: {view}"
  pure (view, rec)
