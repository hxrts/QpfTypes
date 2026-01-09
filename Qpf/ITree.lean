import Qpf.ITree.Basic
import Qpf.ITree.ProtocolInstance
import Qpf.ITree.EquivUTT_Abstract
import Qpf.ITree.Bisim
import Qpf.ITree.EquivUTT
import Qpf.ITree.Equiv

/-!
# Interaction Trees

This module provides interaction trees (ITrees), a coinductive data structure
for giving semantics to side-effecting, possibly non-terminating programs.

## Overview

Interaction trees are a way to represent computations that may:
- Return a value (`ret`)
- Perform an internal/silent step (`tau`)
- Perform a visible event and await a response (`vis`)

## Module Structure

- `Qpf.ITree.Basic`: Core ITree definition, constructors, and structural lemmas
- `Qpf.ITree.Bisim`: Membership-based weak bisimulation (complete proofs)
- `Qpf.ITree.EquivUTT`: F-based weak bisimulation (has incomplete transitivity)
- `Qpf.ITree.Equiv`: Equivalence proof between Bisim and EquivUTT

## Main Definitions

- `ITree α ε ρ`: Interaction tree with response type `α`, event type `ε`, return type `ρ`
- `ITree.Bisim`: Membership-based weak bisimulation (recommended for proofs)
- `ITree.EquivUTT`: F-based weak bisimulation (closer to Coq's `eutt`)
- `ITree.Bisim.iff_EquivUTT`: Proof that the two formulations are equivalent

## Usage Notes

For proving properties about ITrees, prefer `Bisim` over `EquivUTT`:
- `Bisim` has complete proofs for reflexivity, symmetry, and transitivity
- `EquivUTT.trans` has sorries due to QPF quotient elimination limitations
- Use `EquivUTT.trans'` for sorry-free transitivity via the Bisim detour

## References

- [Interaction Trees (POPL 2020)](https://arxiv.org/abs/1906.00046)
- [Coq ITree Library](https://github.com/DeepSpec/InteractionTrees)
-/
