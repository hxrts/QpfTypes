/-
# Universe Utilities

This file contains utilities for extracting and computing universe dependencies
from types and expressions. These are used to ensure universe polymorphism
works correctly in generated `data`/`codata` types.
-/

import Lean

open Lean Meta

namespace Qpf.Macro.Data.Universe

/-- Extract universe parameter names from a Level. -/
def getUniverseDepsLevel : Level → List Name
  | .zero => []
  | .succ l => getUniverseDepsLevel l
  | .max l1 l2 => getUniverseDepsLevel l1 ++ getUniverseDepsLevel l2
  | .imax l1 l2 => getUniverseDepsLevel l1 ++ getUniverseDepsLevel l2
  | .param n => [n]
  | .mvar _ => []

/-- Extract universe parameter names used in an expression. -/
def getUniverseDeps (e : Expr) : MetaM (List Name) := do
  let rec visit (e : Expr) : MetaM (List Name) := do
    match e with
    | .sort l => pure (getUniverseDepsLevel l)
    | .forallE _ t b _ => do
        let dt ← visit t
        let db ← visit b
        pure (dt ++ db)
    | .app f a => do
        let df ← visit f
        let da ← visit a
        pure (df ++ da)
    | .lam _ t b _ => do
        let dt ← visit t
        let db ← visit b
        pure (dt ++ db)
    | .const _ ls => pure (ls.foldl (fun acc l => acc ++ getUniverseDepsLevel l) [])
    | .letE _ t v b _ => do
        let dt ← visit t
        let dv ← visit v
        let db ← visit b
        pure (dt ++ dv ++ db)
    | .mdata _ e => visit e
    | .proj _ _ e => visit e
    | _ => pure []
  visit e

/--
  Compute the result universe for a type given the used universe parameters.
  If an explicit universe is provided, use it; otherwise compute the max of used universes.
-/
def computeResultUniverse (usedUnivs : List Name) (explicit? : Option Level) : Level :=
  match explicit? with
  | some u => u
  | none =>
      match usedUnivs with
      | [] => .zero
      | u :: us => us.foldl (fun acc n => .max acc (.param n)) (.param u)

end Qpf.Macro.Data.Universe
