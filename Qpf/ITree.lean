import Qpf.ITree.Basic
import Qpf.ITree.Bisim
import Qpf.ITree.EquivUTT
import Qpf.ITree.Equiv

/-!
# Interaction Trees

This module provides interaction trees (ITrees), a coinductive data structure
for giving semantics to side-effecting, possibly non-terminating programs.

## Main definitions

* `ITree α ε ρ` - Interaction tree with response type `α`, event type `ε`, return type `ρ`
* `ITree.Bisim` - Membership-based weak bisimulation (complete equivalence relation)
* `ITree.EquivUTT` - F-based weak bisimulation (has incomplete transitivity due to QPF limitations)
* `ITree.Bisim.iff_EquivUTT` - Equivalence between the two bisimulation formulations

## References

* [Interaction Trees (POPL 2020)](https://arxiv.org/abs/1906.00046)
* [Coq ITree Library](https://github.com/DeepSpec/InteractionTrees)
-/
