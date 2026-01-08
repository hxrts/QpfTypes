/-
# Variable Occurrence Counting

This file provides utilities for counting how many times each type variable appears
in a constructor's type signature. This is used during shape extraction to track
which variables are actually used.
-/

import Lean

import Qpf.Macro.Data.Replace

open Lean Meta Parser

/--
  Recursively count variable occurrences in an arrow type.

  For each variable in the `Replace` state, increment its count each time
  it appears as an argument in the arrow chain.
-/
private partial def countVarOccurencesAux (r : Replace) (acc : Array Nat) : Syntax → Array Nat
  | Syntax.node _ ``Term.arrow #[arg, _arrow, tail] =>
      match r.vars.idxOf? arg.getId with
      | some i =>
          let acc := acc.set! i (acc[i]! + 1)
          countVarOccurencesAux r acc tail
      | none =>
          countVarOccurencesAux r acc tail
  | _ => acc

/--
  For each variable in the `Replace` state, count how many times it is mentioned
  in the given constructor type.

  Returns an array where `result[i]` is the count for the `i`th variable.
-/
def countVarOccurences (r : Replace) (ctor_type? : Option Syntax) : Array Nat :=
  let acc := (Array.range r.arity).map fun _ => 0
  match ctor_type? with
  | none => acc
  | some t => countVarOccurencesAux r acc t
