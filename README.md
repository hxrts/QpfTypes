
# A (co)datatype package for Lean 4, based on Quotients of Polynomial Functors

This library implements a `codata` command, which can be used to define *coinductive* types in [Lean 4](https://leanprover-community.github.io/)
using a syntax similar to `inductive`. For example, the following specifies a type of (potentially)
infinite lists.

```lean
/-- Infinite lists -/
codata Stream α
  | cons : α → Stream α → Stream α
```
```lean
/-- Potentially infinite Lists -/
codata CoList α
  | nil : CoList α
  | cons : α → CoList α → CoList α
```

The framework is *compositional*, so we can use `CoList` in subsequent specifications.

```lean
/-- Potentially infinite trees -/
codata CoTree α 
  | node : α → CoList (CoTree α) → CoTree α 
```

We can even mix induction and coinduction. However, the framework used by `codata` does not play
nice with `inductive`. So, the library also provides a `data` command for inductive types, using
that same framework.

```lean
/-- Infinitely branching, finite depth trees
    That is, one node may have infinitely many children, 
    but the depth of the tree is limited.
-/
data CoTree α 
  | node : α → CoList (CoTree α) → CoTree α 
```

# Live and Dead variables

Binders without any type ascription, such as in the examples so far, are called *live* parameters and assumed to live in `Type _`, where the universe level is inferred.
Note that this universe level is the same for all live parameters.

Conversely, binders that do specify a type, even if that type is `Type _` are *dead* parameters.

This distinction becomes important for subsequent definition: it is only allowed to nest (co)induction behind live parameters. It is thus best to leave out type ascription where possible. That said, live variables have a few more restrictions in where they may appear.

```lean
codata CoList' (α : Type _) -- In this definition, `α` is a dead parameter
  | nil : CoList' α 
  | cons : α → CoList' α → CoList' α

/-- The following is not accepted: 
    It not allowed to nest a corecursive occurrence of the type to be defined 
    behind `CoList'`, when its parameter is defined as dead.
-/
codata CoTree (α : Type _)
  | node : α → CoList' (CoTree α) → CoTree α 
  --           ^^^^^^^^^^^^^^^^^^ <-- this is where it goes wrong
```

Reusing the type ascription to distinguish live/dead variable is not ideal; in future we'll either introduce dedicated syntax, or automatically determine which variables can be live and which have to be dead.

# Limitations

The implementation is intended as a proof-of-concept. It is still very rough, and not at all ready for serious use.

Current limitations:
- **Indexed type families** are not supported (e.g., `data Vec α : Nat → Type`)
- **Mutually (co)inductive types** are not supported yet
- **Dependent arrows** in constructors are not supported (e.g., `vis {α} (e : ε α) (k : α → T)`)

The `data` macro generates standard recursion principles (`rec`, `drec`, `recOn`, `casesOn`, `ind`), and `codata` generates `corec`. These should suffice for most use cases, though complex recursion patterns may still require the lower-level `MvQPF.Fix.drec` and `MvQPF.Cofix.corec`.

Beyond this, the implementation is far from perfect and might throw errors for specifications that should be supported. Feel free to open issues for any such specifications.

# Organization

This repository focuses on the QPF-based (co)datatype framework, including:
- the `data` / `codata` macros
- the QPF encodings and core combinators
- concrete coinductive structures (e.g. `ITree`)

Related packages:
- `paco-lean`: **generic** parametrized coinduction library (no QPF/ITree deps)
- `paco-qpf`: **integration** layer that uses paco to prove QPF/ITree results

Separation of concerns:
- **QpfTypes**: types, macros, QPF machinery, domain-specific proofs
- **paco-lean**: pure paco infrastructure (relations, gpaco/up-to, companion)
- **paco-qpf**: bridges that depend on both sides (e.g. paco-based trans proofs)

Proof engineering note:
- Avoid direct elimination on quotient-encoded coinductive values. Prefer
  destructor lemmas (e.g. `dest_*`) and F-inversion lemmas for proof steps.
- For transitivity or substitution-style proofs, use paco/gpaco to avoid
  nested case analysis on fixed-point unfoldings.

# References

For a thorough discussion about the foundations and implementation of this library, see the accompanying MSc. Thesis by Alex C. Keizer: [Implementing a definitional (co)datatype package in Lean 4, based
on quotients of polynomial functors](https://eprints.illc.uva.nl/id/eprint/2239/1/MoL-2023-03.text.pdf)

The foundations of this library come from [avigad/qpf](https://github.com/avigad/qpf).
There it was described as
>  This repository contains a formalization of data type constructions in Lean, by Jeremy Avigad, Mario Carneiro, and Simon Hudon. A       preliminary version of the work is described in this talk: [http://www.andrew.cmu.edu/user/avigad/Talks/qpf.pdf](http://www.andrew.cmu.edu/user/avigad/Talks/qpf.pdf).
