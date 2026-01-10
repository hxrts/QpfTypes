import Qpf
import Qpf.Util.Patterns

/-!
# ITree Base Functor Pattern

This example shows the manual HeadT/ChildT → MvPFunctor → MvQPF pipeline for
an ITree-like base functor. It mirrors the macro-generated structure but stays
explicit for documentation and debugging.
-/

namespace ITreeBasePattern

inductive HeadT : Type 1
  | ret
  | tau
  | vis (Ans : Type)

def ChildT : HeadT → TypeVec.{1} 2
  | .ret     => ![PFin2.{1} 1, PFin2.{1} 0]
  | .tau     => ![PFin2.{1} 0, PFin2.{1} 1]
  | .vis Ans => ![PFin2.{1} 0, ULift.{1, 0} Ans]

abbrev P : MvPFunctor.{1} 2 := ⟨HeadT, ChildT⟩
abbrev F : TypeFun.{1} 2 := P.Obj

instance : MvQPF F := MvQPF.ofPolynomial_id P

end ITreeBasePattern
