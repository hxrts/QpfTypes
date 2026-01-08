/-
# Constructor Generation

This file generates user-facing constructor functions for `data`/`codata` types.

The generated constructors wrap the underlying `MvQPF.Fix.mk` or `MvQPF.Cofix.mk` calls,
providing a more natural interface for users.

## Example

For `data List α | nil | cons : α → List α → List α`, we generate:
- `List.nil : List α` wrapping `MvQPF.Fix.mk Shape.nil`
- `List.cons : α → List α → List α` wrapping `MvQPF.Fix.mk (Shape.cons ...)`
-/

import Qpf.Macro.Data.Replace
import Qpf.Macro.Data.RecForm
import Qpf.Macro.Data.View

open Lean Meta Elab Elab.Command
open PrettyPrinter (delab)

open Macro (withQPFTraceNode elabCommandAndTrace)

namespace Data.Command

open Parser in
/-- Count the number of arguments (arrows) in a constructor type. -/
partial def countConstructorArgs : Syntax → Nat
  | Syntax.node _ ``Term.arrow #[_, _, tail] => 1 + countConstructorArgs tail
  | _ => 0

/--
  Generate constructor definitions that wrap Shape constructors.

  Parameters:
  - `view`: The parsed data declaration
  - `shape`: Name of the Shape type
  - `nameGen`: Function to generate constructor names
  - `argTy`, `retTy`: Argument and return types for the constructor
  - `binders`: Additional binders to add to the constructor
  - `indexIdents`: Index arguments to apply to shape constructors (for indexed families)
-/
def mkConstructorsWithNameAndType
    (view : DataView) (shape : Name)
    (nameGen : CtorView → Name) (argTy retTy : Term)
    (binders : TSyntaxArray ``Parser.Term.bracketedBinder := #[])
    (indexIdents : Array Term := #[])
    : CommandElabM Unit := do
  for ctor in view.ctors do
    withQPFTraceNode "define constructor {ctor.declName}" <| do
    trace[QPF] "type := {ctor.type?}"
    let n_args := (ctor.type?.map countConstructorArgs).getD 0

    let args := (← (List.range n_args).mapM
      fun _ => do pure <| mkIdent <|← Elab.Term.mkFreshBinderName).toArray

    let pointConstructor := mkIdent ((DataCommand.fixOrCofix view.command).getId ++ `mk)
    let shapeCtor := mkIdent <| Name.replacePrefix ctor.declName view.declName shape
    trace[QPF] "shapeCtor = {shapeCtor}"

    -- For indexed families, apply index arguments first, then constructor arguments
    let shapeCtorWithIndices := Syntax.mkApp shapeCtor indexIdents

    let body ← if n_args = 0 then
        `($pointConstructor $shapeCtorWithIndices)
      else
        `(fun $args:ident* => $pointConstructor ($shapeCtorWithIndices $args:ident*))

    let type ← RecursionForm.extract ctor view.getExpectedType
      |>.map (RecursionForm.replaceRec view.getExpectedType argTy)
      |> RecursionForm.toType retTy

    let modifiers : Modifiers := {
      computeKind := view.modifiers.computeKind
      attrs := #[{
        name := `matchPattern
      }]
    }
    let declId := mkIdent $ nameGen ctor

    elabCommandAndTrace <|← `(
      $(quote modifiers):declModifiers
      def $declId:ident $binders*: $type := $body:term
    )

  return

/--
  Generate convenient constructor functions for the QPF type.

  These constructors provide a natural interface for creating values of the type,
  hiding the underlying `Shape` and `MvQPF.Fix.mk` machinery.
-/
def mkConstructors (view : DataView) (shape : Name) : CommandElabM Unit :=
  withQPFTraceNode "deriving constructors" (tag := "mkConstructors") <| do
  let explicit ← view.getExplicitExpectedType
  let nameGen := (·.declName.replacePrefix (← getCurrNamespace) .anonymous)
  -- Let implicit parameters be inferred for the shape constructors
  mkConstructorsWithNameAndType view shape nameGen explicit explicit

end Data.Command
