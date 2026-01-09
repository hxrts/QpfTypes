import Qpf.Builtins.ListPerm
import Mathlib.Data.QPF.Multivariate.Constructions.Quot

namespace MvQPF
namespace List

/-!
# Multiset as a Quotient of QPF List

This module defines multisets as quotients of QPF lists, relying on the
permutation API in `Qpf.Builtins.ListPerm`.
-/

noncomputable def Multiset : TypeFun 1 :=
  MvQPF.Quot1 permCurried

noncomputable instance : MvQPF Multiset :=
  MvQPF.relQuot permCurried permCurried_functorial

end List
end MvQPF
