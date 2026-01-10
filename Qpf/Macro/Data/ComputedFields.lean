/-
# Computed Fields for data Types

This file implements computed field desugaring and simp lemma generation for `data` types.
Computed fields provide a way to define functions that pattern match on constructors
with automatic simp lemmas for each case.

## Example

```lean
data List α
  | nil
  | cons : α → List α → List α
where
  length : List α → Nat
    | nil => 0
    | cons _ xs => 1 + length xs
```

This generates:
- `List.length : List α → Nat` (the computed field function)
- `@[simp] theorem List.length_nil : length nil = 0`
- `@[simp] theorem List.length_cons : length (cons x xs) = 1 + length xs`
-/

import Qpf.Macro.Data.View
import Qpf.Macro.Data.RecForm
import Qpf.Macro.Common

open Lean Meta Elab Elab.Command Elab.Term
open Parser.Term (matchAltExpr bracketedBinder matchAlts)

open Macro (withQPFTraceNode elabCommandAndTrace)

namespace Qpf.Macro.Data.ComputedFields

/-- Parser alias for bracketedBinder to work around optional argument issues. -/
private abbrev bb : Lean.Parser.Parser := bracketedBinder

/-- Build a TypeVec from an array of terms. -/
private def mkTypeVec (terms : Array Term) : CommandElabM Term := do
  let mut acc : Term ← `(!![])
  for term in terms do
    acc ← `((TypeVec.append1 $acc $term))
  pure acc

/-- Strip parentheses from syntax. -/
private def stripParens : Syntax → Syntax
  | Syntax.node _ ``Lean.Parser.Term.paren #[_, inner, _] => stripParens inner
  | stx => stx

/-- Collect application arguments from syntax. -/
private def collectAppArgs : Syntax → Array Syntax
  | Syntax.node _ ``Lean.Parser.Term.app args =>
      if h : 0 < args.size then
        let fn := args[0]
        let rest :=
          if h1 : 1 < args.size then
            if args.size == 2 && args[1].getKind == nullKind then
              args[1].getArgs
            else
              args.extract 1 args.size
          else
            #[]
        collectAppArgs fn ++ rest
      else
        #[]
  | _ => #[]

/-- Build a case function for a computed field clause. -/
private def mkCaseFun (ctor : CtorView) (alt : Syntax) (field : QpfComputedFieldView)
    (recType : Term) : CommandElabM Term := do
  let (pat, rhs) ←
    match alt with
    | `(matchAltExpr| | $pat:term => $rhs:term) => pure (pat, rhs)
    | _ => throwErrorAt alt "Unsupported computed field clause; expected `| <ctor> ... => ...`"
  let pat := stripParens pat
  let args := collectAppArgs pat
  let forms := RecursionForm.extract ctor recType |>.toArray
  if args.size != forms.size then
    throwErrorAt pat
      "Constructor pattern has {args.size} arguments, but expected {forms.size}"
  let mut argNames : Array Ident := #[]
  for arg in args do
    if arg.getKind == identKind then
      argNames := argNames.push ⟨arg⟩
    else if arg.getKind == ``Lean.Parser.Term.hole then
      argNames := argNames.push (mkIdentFrom arg (← mkFreshBinderName))
    else
      throwErrorAt arg "Computed field patterns must use identifiers or `_`"

  let mut lam := rhs
  let pairs := (Array.zip argNames forms).toList.reverse
  for ⟨name, form⟩ in pairs do
    let argTy : Term := match form with
      | RecursionForm.nonRec stx | RecursionForm.composed stx => stx
      | RecursionForm.directRec => field.type
    lam ← `(fun ($name:ident : $argTy) => $lam)
  return lam

/--
  Generate computed field definitions and simp lemmas for a data type.

  For each computed field, this generates:
  1. The field function (using the type's recursor)
  2. A simp lemma for each constructor showing how the field evaluates
-/
def mkComputedFields (view : DataView) : CommandElabM Unit :=
  withQPFTraceNode m!"defining computed fields for {view.declId}" (tag := "mkComputedFields") <| do
  if view.computedFields.isEmpty then
    return
  if view.command == .Codata then
    throwErrorAt view.ref "Computed fields are not supported for `codata` yet"

  let liveBinders := view.liveBinders.raw.map fun stx =>
    if stx.getKind == ``Parser.Term.binderIdent then
      stx[0]
    else
      stx
  let bindersRaw := view.deadBinders.raw ++ liveBinders
  let binders : TSyntaxArray [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder] :=
    ⟨bindersRaw.toList.map TSyntax.mk⟩
  let deadBinderTerms : Array Term := view.deadBinderNames.map fun n => (n : Term)
  let liveBinderTerms : Array Term := liveBinders.map TSyntax.mk
  let allBinderTerms : Array Term := deadBinderTerms ++ liveBinderTerms
  let recType := view.getExpectedType
  let recId := mkIdent (view.shortDeclName ++ `rec)
  let shapeFunctorId := mkIdent (view.declName ++ `Shape ++ `functor)
  let shapeId := mkIdent (view.declName ++ `Shape)

  for field in view.computedFields do
    let fieldName := mkIdent (view.declName ++ field.fieldId)
    let fullType : Term ← `($recType:term → $(field.type):term)
    let modifiers := { field.modifiers with computeKind := .noncomputable }
    -- field.matchAlts is a TSyntax ``Parser.Term.matchAlts, extract its match alternatives
    -- The raw syntax has children that are matchAlt nodes, possibly wrapped in a null node
    let altsRaw := field.matchAlts.raw
    let alts :=
      if altsRaw.getArgs.size == 1 && altsRaw[0].getKind == nullKind then
        altsRaw[0].getArgs
      else
        altsRaw.getArgs
    if alts.size != view.ctors.size then
      throwErrorAt field.ref
        "Computed field has {alts.size} clauses, but expected {view.ctors.size}"
    let caseFuns ← (Array.zip view.ctors alts).mapM fun ⟨ctor, alt⟩ =>
      mkCaseFun ctor alt field recType
    let recApp : Term ←
      `($recId:ident)
    elabCommandAndTrace <|← `(
      $(quote modifiers):declModifiers
      def $fieldName:ident $binders* : $fullType :=
        $recApp $caseFuns:term*
    )
    let fieldMapHead : Term ←
      `($recApp:term $caseFuns:term*)
    for (idx, ctor) in (Array.range view.ctors.size).zip view.ctors do
      let ctorId := mkIdent ctor.declName
      let forms := RecursionForm.extract ctor recType |>.toArray
      let argTypes : Array Term := forms.map (RecursionForm.toTerm recType)
      let args ← argTypes.mapM fun ty => do
        let name ← mkFreshBinderName
        let ident := mkIdent name
        let binder : TSyntax ``bracketedBinder := ⟨(← `(bb | ($ident:ident : $ty))).raw⟩
        pure (ident, binder)
      let argTerms : Array Term := args.map (fun x => (x.1 : Term))
      let ctorHead : Term ←
        if allBinderTerms.isEmpty then
          `($ctorId:ident)
        else
          `(@$ctorId:ident $allBinderTerms:term*)
      let ctorApp : Term ←
        argTerms.foldlM (fun acc arg => `($acc $arg)) ctorHead
      let fieldHead : Term ←
        if allBinderTerms.isEmpty then
          `($fieldName:ident)
        else
          `(@$fieldName:ident $allBinderTerms:term*)
      let lhs : Term ← `($fieldHead:term $ctorApp:term)
      let caseFun := caseFuns[idx]!
      let rhsArgs ← (Array.zip forms argTerms).mapM fun ⟨form, arg⟩ => do
        match form with
        | RecursionForm.directRec => `($fieldHead:term $arg)
        | RecursionForm.nonRec _ | RecursionForm.composed _ => pure arg
      let rhs : Term ← rhsArgs.foldlM (fun acc arg => `($acc $arg)) caseFun
      let stmt : Term ← `($lhs:term = $rhs:term)
      let shapeCtorName :=
        ctor.declName.replacePrefix view.declName (view.declName ++ `Shape)
      let shapeCtorId := mkIdent shapeCtorName
      let shapeParamsIn : Array Term := allBinderTerms.push recType
      let shapeParamsOut : Array Term := allBinderTerms.push field.type
      let shapeCtorHeadIn : Term ←
        if shapeParamsIn.isEmpty then
          `($shapeCtorId:ident)
        else
          `(@$shapeCtorId:ident $shapeParamsIn:term*)
      let shapeCtorHeadOut : Term ←
        if shapeParamsOut.isEmpty then
          `($shapeCtorId:ident)
        else
          `(@$shapeCtorId:ident $shapeParamsOut:term*)
      let shapeCtorApp : Term ←
        argTerms.foldlM (fun acc arg => `($acc $arg)) shapeCtorHeadIn
      let shapeMapArgs ← (Array.zip forms argTerms).mapM fun ⟨form, arg⟩ => do
        match form with
        | RecursionForm.directRec => `($fieldMapHead:term $arg)
        | RecursionForm.nonRec _ | RecursionForm.composed _ => pure arg
      let shapeMappedApp : Term ←
        shapeMapArgs.foldlM (fun acc arg => `($acc $arg)) shapeCtorHeadOut
      let shapeBase : Term ←
        if deadBinderTerms.isEmpty then
          `($shapeId:ident)
        else
          `(@$shapeId:ident $deadBinderTerms:term*)
      let shapeVecIn ← mkTypeVec (liveBinderTerms.push recType)
      let shapeVecOut ← mkTypeVec (liveBinderTerms.push field.type)
      let shapeCtorAppUncurried : Term ←
        `(show (TypeFun.ofCurried $shapeBase $shapeVecIn) from $shapeCtorApp)
      let shapeMappedAppUncurried : Term ←
        `(show (TypeFun.ofCurried $shapeBase $shapeVecOut) from $shapeMappedApp)
      let mapFn : Term ←
        `((TypeVec.appendFun TypeVec.id $fieldMapHead))
      let mapStmt : Term ←
        `(MvFunctor.map $mapFn $shapeCtorAppUncurried = $shapeMappedAppUncurried)
      let argBindersRaw := args.map (fun x => x.2.raw)
      let lemmaBindersRaw := bindersRaw ++ argBindersRaw
      let lemmaBinders : TSyntaxArray [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder] :=
        ⟨lemmaBindersRaw.toList.map TSyntax.mk⟩
      let ctorSuffix := ctor.declName.replacePrefix view.declName .anonymous
      let lemmaName := Name.mkStr view.declName
        s!"{field.fieldId.toString}_{ctorSuffix.toStringWithSep "_" true}"
      let lemmaId := mkIdent lemmaName
      elabCommandAndTrace <|← `(
        @[simp] theorem $lemmaId:ident $lemmaBinders* : $stmt := by
          have hmap : $mapStmt := by
            change $(shapeFunctorId).map $mapFn $shapeCtorAppUncurried = $shapeMappedAppUncurried
            rfl
          simp [$(recId):ident] at hmap
          simp [$(fieldName):ident, $(recId):ident, $(ctorId):ident,
            $(mkIdent ``_root_.MvQPF.Fix.rec_eq):ident]
          first
            | simpa [hmap]
            | rfl
      )

end Qpf.Macro.Data.ComputedFields
