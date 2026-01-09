import Qpf

/-!
# Multiset Example (QPF List Quotient)

This example now defers to the built-in multiset construction in
`Qpf.Builtins.Multiset`, which defines `Multiset` as a quotient of the
QPF list representation by permutation.
-/

open scoped MvFunctor

/-- Alias for the QPF list typefun. -/
abbrev List' : TypeFun 1 := TypeFun.ofCurried List

/-- Alias for the built-in multiset typefun. -/
noncomputable abbrev MultiSet : TypeFun 1 := MvQPF.List.Multiset

/-- The multiset quotient has an `MvQPF` instance. -/
example : MvQPF MultiSet := by
  infer_instance
