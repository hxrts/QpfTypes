import Qpf.Core
import Qpf.Macro.Data

import Qpf.Builtins.List
import Qpf.Builtins.Multiset

/-!
# QpfTypes: Coinductive Types via Quotients of Polynomial Functors

This is the main entry point for the QPF library. It provides the `data` and `codata` commands
for defining inductive and coinductive types with compositional nesting support.

## Quick Start

```lean
import Qpf

-- Define a coinductive type
codata Stream α where
  | cons : α → Stream α → Stream α

-- Define an inductive type
data MyList α where
  | nil : MyList α
  | cons : α → MyList α → MyList α

-- Nest them compositionally
codata CoTree α where
  | node : α → MyList (CoTree α) → CoTree α
```

## What's Included

This import provides:
- The `data` and `codata` macros for defining (co)inductive types
- QPF instances for `List` and `Multiset` (enabling their use in nested definitions)
- Core polynomial functor infrastructure

## Selective Imports

For more granular control, import submodules directly:
- `Qpf.Core`: Low-level PFunctor machinery only
- `Qpf.Macro`: Just the macros without builtin type instances
- `Qpf.ITree`: Interaction trees for effectful computation semantics

## References

- [MSc Thesis](https://eprints.illc.uva.nl/id/eprint/2239/1/MoL-2023-03.text.pdf): Implementation details
- [avigad/qpf](https://github.com/avigad/qpf): Original Lean 3 foundations
-/
