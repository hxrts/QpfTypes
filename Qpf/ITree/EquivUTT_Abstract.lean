import Qpf.ITree
import Qpf.Coinduction.EquivUTT

/-!
# EquivUTT for ITree (via abstract protocol)

This module instantiates the abstract EquivUTT development for `ITree`
using the `CoinductiveTreeProtocol` instance.
-/-

namespace ITree

abbrev Terminates {α ε ρ : Type} := Coinduction.Terminates (T := ITree) (α := α) (ε := ε) (ρ := ρ)

abbrev CanDo {α ε ρ : Type} := Coinduction.CanDo (T := ITree) (α := α) (ε := ε) (ρ := ρ)

abbrev RetPathBounded {α ε ρ : Type} :=
  Coinduction.RetPathBounded (T := ITree) (α := α) (ε := ε) (ρ := ρ)

abbrev VisPathBounded {α ε ρ : Type} :=
  Coinduction.VisPathBounded (T := ITree) (α := α) (ε := ε) (ρ := ρ)

abbrev F {α ε ρ : Type} := Coinduction.F (T := ITree) (α := α) (ε := ε) (ρ := ρ)

abbrev EquivUTT {α ε ρ : Type} := Coinduction.EquivUTT (T := ITree) (α := α) (ε := ε) (ρ := ρ)

abbrev composeRel {α ε ρ : Type} :=
  Coinduction.composeRel (T := ITree) (α := α) (ε := ε) (ρ := ρ)

end ITree
