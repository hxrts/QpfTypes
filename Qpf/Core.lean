import Qpf.PFunctor.Multivariate.Basic
import Qpf.PFunctor.Multivariate.Card
import Qpf.PFunctor.Multivariate.Constructions.Arrow
import Qpf.PFunctor.Multivariate.Constructions.Prod
import Qpf.PFunctor.Multivariate.Constructions.Sum

/-!
# QPF Core Infrastructure

This module provides the core polynomial functor (PFunctor) infrastructure that underlies
the QPF-based (co)datatype package.

## Overview

Polynomial functors are the building blocks for representing (co)inductive types. This module
re-exports the essential PFunctor definitions and constructions needed by the `data`/`codata`
macros.

## Module Structure

- `Qpf.PFunctor.Multivariate.Basic`: Core multivariate polynomial functor definitions
- `Qpf.PFunctor.Multivariate.Card`: Cardinality lemmas for polynomial functors
- `Qpf.PFunctor.Multivariate.Constructions.Arrow`: Arrow/function space construction
- `Qpf.PFunctor.Multivariate.Constructions.Prod`: Product construction
- `Qpf.PFunctor.Multivariate.Constructions.Sum`: Sum/coproduct construction

## Usage

Most users should `import Qpf` rather than this module directly. Import `Qpf.Core` only
if you need the low-level PFunctor machinery without the `data`/`codata` macros.
-/
