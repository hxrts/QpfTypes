import Mathlib.Data.QPF.Multivariate.Basic
import Qpf.Qpf.Multivariate.ofPolynomial

/-!
# QPF Pattern Lemmas

This module collects small, reusable patterns for working with multivariate QPFs.
It is intended as a lightweight toolbox for hand-rolled functors and examples.
-/

namespace MvQPF

/--
`P.Obj` is a QPF with the identity box/unbox isomorphism.

This is the canonical way to discharge the QPF obligation when your functor is
*already* a polynomial functor.
-/
noncomputable def ofPolynomial_id (P : MvPFunctor n) : MvQPF P.Obj :=
  MvQPF.ofPolynomial (F := P.Obj) P
    (box := fun x => x)
    (unbox := fun x => x)
    (box_unbox_id := by intro _ x; rfl)
    (unbox_box_id := by intro _ x; rfl)
    (map_eq := by intro _ _ _ _; rfl)

/--
The projection functor is a QPF; prefer the built-in instance.
-/-
abbrev Prj (n : Nat) (i : PFin2 n) : TypeFun n := _root_.MvQPF.Prj i

/--
The binary product functor is a QPF; prefer the built-in instance.
-/-
abbrev Prod' : TypeFun 2 := @TypeFun.ofCurried 2 Prod

end MvQPF
