import Qpf.Macro.Comp
import Qpf.Macro.Data

/-!
# QPF Macros

This module provides the `data` and `codata` commands for defining inductive and coinductive
types using the QPF (Quotient of Polynomial Functors) framework.

## Overview

The macros allow defining (co)inductive types with syntax similar to Lean's built-in `inductive`:

```lean
data MyList α where
  | nil : MyList α
  | cons : α → MyList α → MyList α

codata Stream α where
  | cons : α → Stream α → Stream α
```

The key advantage is **compositionality**: types defined with `data`/`codata` can be nested
within each other, enabling mixed inductive-coinductive definitions.

## Module Structure

- `Qpf.Macro.Data`: The `data` and `codata` command elaborators
- `Qpf.Macro.Comp`: The `qpf` composition macro for building complex QPFs

## Usage

Import `Qpf` to get both the macros and standard library types. Import `Qpf.Macro` directly
only if you need the macros without the builtins.

## See Also

- `Qpf.Core`: Low-level polynomial functor infrastructure
- `Qpf.ITree`: Interaction trees built using this framework
-/
