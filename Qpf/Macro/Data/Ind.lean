/-
# Recursor Generation

This file generates recursors (elimination principles) for `data` types.
The generated recursors include:

- `ind`: Induction principle for `Prop`-valued motives (marked with `@[induction_eliminator]`)
- `rec`: Recursor for non-dependent `Type`-valued motives
- `drec`: Dependent recursor for `Type`-valued motives
- `cases`: Case analysis for `Prop` (marked with `@[cases_eliminator]`)
- `casesType`: Case analysis for `Type`

These recursors wrap the underlying `MvQPF.Fix.ind`, `MvQPF.Fix.rec`, and
`MvQPF.Fix.drec` functions,
providing a more natural interface that matches the shape constructors.
-/

import Qpf.Macro.Data.RecForm
import Qpf.Macro.Data.View
import Qpf.Macro.Common
import Mathlib.Data.QPF.Multivariate.Constructions.Fix
import Mathlib.Tactic.ExtractGoal

open Lean.Parser (Parser)
open Lean Meta Elab.Command Elab.Term Parser.Term PrettyPrinter
open Lean.Parser.Tactic (inductionAlt)

open Macro (withQPFTraceNode elabCommandAndTrace)

/-! ## Parser Aliases -/

/-- Flatten a name for use as an argument name. -/
def flattenForArg (n : Name) := Name.str .anonymous $ n.toStringWithSep "_" true

/--
  Parser aliases to work around optional arguments in quotation syntax.

  Both `bracketedBinder` and `matchAlts` have optional arguments which prevent them
  from being recognized in quotation syntax like `` `(bracketedBinder| ...) ``.
  These aliases force the optional argument to its default value.
-/
abbrev bb            : Parser := bracketedBinder
abbrev matchAltExprs : Parser := matchAlts

-- Coercions for the parser aliases
instance : Coe (TSyntax ``bb) (TSyntax ``bracketedBinder)      where coe x := ⟨x.raw⟩
instance : Coe (TSyntax ``matchAltExprs) (TSyntax ``matchAlts) where coe x := ⟨x.raw⟩

/-! ## Helper Functions -/

section
variable {m} [Monad m] [MonadQuotation m] [MonadError m] [MonadTrace m] [AddMessageContext m]

/-- Generate the binders for recursor arguments based on recursion forms. -/
def mkRecursorBinder
    (rec_type : Term) (name : Name)
    (form : List RecursionForm)
    (inclMotives : Bool) : m (TSyntax ``bracketedBinder) := do
  let form ← form.mapM fun x => (x, mkIdent ·) <$> mkFreshBinderName
  let form := form.reverse

  let out := Syntax.mkApp (← `(motive)) #[Syntax.mkApp (mkIdent name) (form.map Prod.snd).toArray.reverse]
  let out ←
    if inclMotives then
      (form.filter (·.fst == .directRec)).foldlM (fun acc ⟨_, name⟩ => `(motive $name → $acc)) out
    else pure out

  let ty ← form.foldlM (fun acc => (match · with
    | ⟨.nonRec x, name⟩ => `(($name : $x) → $acc)
    | ⟨.directRec, name⟩ => `(($name : $rec_type) → $acc)
    | ⟨.composed x, _⟩ => throwErrorAt x "Cannot handle recursive forms"
  )) out

  `(bb | ($(mkIdent $ flattenForArg name) : $ty))

/-- Generate binders for a non-dependent recursor (`Fix.rec`). -/
def mkRecursorBinderConst
    (motive : Term) (name : Name)
    (form : List RecursionForm) : m (TSyntax ``bracketedBinder) := do
  let form ← form.mapM fun x => (x, mkIdent ·) <$> mkFreshBinderName
  let form := form.reverse

  let out := motive
  let ty ← form.foldlM (fun acc => (match · with
    | ⟨.nonRec x, name⟩ => `(($name : $x) → $acc)
    | ⟨.directRec, name⟩ => `(($name : $motive) → $acc)
    | ⟨.composed x, _⟩ => throwErrorAt x "Cannot handle recursive forms"
  )) out

  `(bb | ($(mkIdent $ flattenForArg name) : $ty))

/-- Generate an array of fresh identifiers with the same length as the input. -/
def toEqLenNames (x : Array α) : m (Array Ident) := x.mapM (fun _ => mkIdent <$> mkFreshBinderName)

/-- Generate an array of fresh identifiers with the same length as the input list. -/
def listToEqLenNames (x : List α) : m (Array Ident) := toEqLenNames x.toArray

/-- Wrap an array of terms: singleton arrays remain as-is, otherwise create an n-ary product. -/
def wrapIfNotSingle (arr : TSyntaxArray `term) : m Term :=
  if let #[s] := arr then `($s)
  else `(⟨$arr,*⟩)

/-- Fold a list of syntax nodes with a binary operation (used for inserting `∧` between entries). -/
def seq (f : TSyntax kx → TSyntax kx → m (TSyntax kx)) : List (TSyntax kx) → m (TSyntax kx)
  | [hd] => pure hd
  | hd :: tl => do f hd (← seq f tl)
  | [] => throwError "Expected at least one value for interspersing"

/-! ## Match Body Generation -/

/-- Generate match alternatives for induction/cases eliminators. -/
def generateIndBody (ctors : Array (Name × List RecursionForm)) (includeMotive : Bool) : m (TSyntax ``matchAlts) := do
  let deeper: (TSyntaxArray ``matchAlt) ← ctors.mapM fun ⟨outerCase, form⟩ => do
    let callName := mkIdent $ flattenForArg outerCase
    let outerCaseId := mkIdent $ `Shape ++ outerCase
    let rec_count := form.count .directRec

    let names ← listToEqLenNames form

    if 0 = rec_count || !includeMotive then
      return ← `(matchAltExpr| | $outerCaseId $names*, ih => ($callName $names*))

    let names ← toEqLenNames names

    let recs := names.zip (form.toArray)
          |>.filter (·.snd == .directRec)
          |>.map Prod.fst

    let cases: TSyntaxArray _ ← ctors.mapM fun ⟨innerCase, _⟩ => do
      let innerCaseTag := mkIdent innerCase
      if innerCase != outerCase then
        `(inductionAlt| | $innerCaseTag:ident => contradiction)
      else
        let split : Array (TSyntax `tactic) ← recs.mapM fun n =>
          `(tactic|rcases $n:ident with ⟨_, $n:ident⟩)
        let injections ← toEqLenNames names

        `(inductionAlt| | $innerCaseTag:ident $[$names:ident]* => (
            $split:tactic*
            injection proof with $injections*
            subst $injections:ident*
            exact $(← wrapIfNotSingle recs)
        ))

    let witnesses ← toEqLenNames recs
    let proofs ← wrapIfNotSingle witnesses
    let type ← seq (fun a b => `($a ∧ $b)) (← recs.mapM fun x => `(motive $x)).toList

    `(matchAltExpr|
      | $outerCaseId $names*, ih =>
        have $proofs:term : $type := by
          simp only [
            $(mkIdent ``MvFunctor.LiftP):ident,
            $(mkIdent ``TypeVec.PredLast):ident
          ] at ih

          rcases ih with ⟨w, proof⟩
          cases w with
          $cases:inductionAlt*
        $callName $names* $witnesses*
    )

  `(matchAltExprs| $deeper:matchAlt* )

/-- Generate match alternatives for the recursor (destructuring recursive results). -/
def generateRecBody (ctors : Array (Name × List RecursionForm)) (includeMotive : Bool) : m (TSyntax ``matchAlts) := do
  let deeper: (TSyntaxArray ``matchAlt) ← ctors.mapM fun ⟨outerCase, form⟩ => do
    let callName := mkIdent $ flattenForArg outerCase
    let outerCaseId := mkIdent $ `Shape ++ outerCase

    let names ← listToEqLenNames form
    let names := names.zip form.toArray

    let recArgs ← names.mapM fun ⟨nm, f⟩ => do
      match f with
      | .directRec =>
          if includeMotive then
            let ih ← mkFreshBinderName
            let ihId := mkIdent ih
            let pat ← `(⟨$nm, $ihId⟩)
            pure (nm, some ihId, pat)
          else
            let pat ← `(⟨$nm, _⟩)
            pure (nm, none, pat)
      | .nonRec _ =>
          let pat ← `($nm)
          pure (nm, none, pat)
      | .composed _ =>
          throwError "Cannot handle composed"

    let desArgs : Array (TSyntax `term) := recArgs.map (fun x => x.2.2)
    let callArgs : Array Term := recArgs.map (fun x => x.1)
    let motiveArgs : Array Term := if includeMotive then
        recArgs.filterMap fun x =>
          match x.2.1 with
          | some ih => some ih
          | none => none
      else #[] 

    `(matchAltExpr|
      | $outerCaseId $desArgs* =>
        $callName $callArgs* $motiveArgs*
    )

  `(matchAltExprs| $deeper:matchAlt*)

/-- Generate match alternatives for the non-dependent recursor (`Fix.rec`). -/
def generateRecBodyConst (ctors : Array (Name × List RecursionForm)) : m (TSyntax ``matchAlts) := do
  let deeper: (TSyntaxArray ``matchAlt) ← ctors.mapM fun ⟨outerCase, form⟩ => do
    let callName := mkIdent $ flattenForArg outerCase
    let outerCaseId := mkIdent $ `Shape ++ outerCase
    let names ← listToEqLenNames form
    `(matchAltExpr|
      | $outerCaseId $names* =>
        $callName $names*
    )
  `(matchAltExprs| $deeper:matchAlt* )

/-! ## Main Recursor Generation -/

/--
  Generate all recursors for a `data` type.

  This generates four elimination principles:
  - `ind`: Induction for `Prop` (with `@[induction_eliminator]`)
  - `rec`: Recursion for non-dependent `Type _`
  - `drec`: Dependent recursion for `Type _`
  - `cases`: Case analysis for `Prop` (with `@[cases_eliminator]`)
  - `casesType`: Case analysis for `Type`
-/
def genRecursors (view : DataView) : CommandElabM Unit :=
  withQPFTraceNode "attempting to generate recursors for datatype"
    (tag := "genRecursors") <| do

  let motiveSort : Term ←
    match view.explicitUniverse? with
    | some u =>
        runTermElabM fun _ => do
          delab (mkSort u)
    | none => `(Type _)

  let rec_type := view.getExpectedType

  let mapped := view.ctors.map (RecursionForm.extractWithName view.declName · rec_type)
  let caseNames := mapped.map fun ⟨name, _⟩ => mkIdent (flattenForArg name)

  let motiveTerm ← `(motive)
  let ih_types_const ← mapped.mapM fun ⟨name, base⟩ =>
    mkRecursorBinderConst motiveTerm name base

  let ih_types ← mapped.mapM fun ⟨name, base⟩ =>
    mkRecursorBinder (rec_type) name base true

  elabCommandAndTrace (header := "elaborating induction principle …") <|← `(
    @[induction_eliminator]
    def $(view.shortDeclName ++ `ind |> mkIdent):ident
      { motive : $rec_type → Prop}
      $ih_types*
      : (val : $rec_type) → motive val
    :=
      $(mkIdent ``_root_.MvQPF.Fix.ind)
        ($(mkIdent `p) := motive)
        (match ·,· with $(← generateIndBody mapped true)))

  elabCommandAndTrace (header := "elaborating recursor …") <|← `(
    def $(view.shortDeclName ++ `rec |> mkIdent):ident
      { motive : Type _ }
      $ih_types_const*
      : (val : $rec_type) → motive
    := $(mkIdent ``_root_.MvQPF.Fix.rec)
        (match · with $(← generateRecBodyConst mapped)))

  elabCommandAndTrace (header := "elaborating dependent recursor …") <|← `(
    def $(view.shortDeclName ++ `drec |> mkIdent):ident
      { motive : $rec_type → $motiveSort}
      $ih_types*
      : (val : $rec_type) → motive val
    := $(mkIdent ``_root_.MvQPF.Fix.drec)
        (match · with $(← generateRecBody mapped true)))

  elabCommandAndTrace (header := "elaborating recOn …") <|← `(
    def $(view.shortDeclName ++ `recOn |> mkIdent):ident
      (val : $rec_type)
      { motive : $rec_type → $motiveSort}
      $ih_types*
      : motive val
    := $(mkIdent (view.shortDeclName ++ `drec)) $caseNames:ident* val
  )

  let casesOnTypes ← mapped.mapM fun ⟨name, base⟩ =>
    mkRecursorBinder (rec_type) (name) base false

  elabCommandAndTrace (header := "elaborating casesOn (Prop) eliminator …") <|← `(
    @[cases_eliminator]
    def $(view.shortDeclName ++ `cases |> mkIdent):ident
      { motive : $rec_type → Prop}
      $casesOnTypes*
      : (val : $rec_type) → motive val
    := $(mkIdent ``_root_.MvQPF.Fix.ind)
        ($(mkIdent `p) := motive)
        (match ·,· with $(← generateIndBody mapped false)))

  elabCommandAndTrace (header := "elaborating casesOn (Type _) eliminator …") <|← `(
    def $(view.shortDeclName ++ `casesType |> mkIdent):ident
      { motive : $rec_type → $motiveSort}
      $casesOnTypes*
      : (val : $rec_type) → motive val
    := $(mkIdent ``_root_.MvQPF.Fix.drec)
        (match · with $(← generateRecBody mapped false)))

  elabCommandAndTrace (header := "elaborating casesOn …") <|← `(
    @[cases_eliminator]
    def $(view.shortDeclName ++ `casesOn |> mkIdent):ident
      (val : $rec_type)
      { motive : $rec_type → Prop}
      $casesOnTypes*
      : motive val
    := $(mkIdent (view.shortDeclName ++ `cases)) $caseNames:ident* val
  )
