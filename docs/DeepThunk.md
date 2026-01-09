# DeepThunk

DeepThunk is a higher-order functor used for productive corecursion with partial yields. It extends a functor `F` by inserting a small control layer that can either recall the corecursor or continue building the structure. The core implementation lives in `Qpf/Qpf/Multivariate/Constructions/DeepThunk.lean`.

## Core idea

DeepThunk introduces an action type `DTSum` and a generalized action type `DTSumMod`. `DTSum` is a fresh sum type to make pattern detection in macros reliable. `DTSumMod` adds a constant modifier payload that is interpreted by a user-supplied function.

```lean
def corecMod
    {F : TypeFun n.succ} {α : TypeVec n} {Mod : Type u}
    [MvFunctor F] [MvQPF F]
    (apply : Mod → UncurriedMod F Mod (α ::: β) → UncurriedMod F Mod (α ::: β))
    (f : β → UncurriedMod F Mod (α ::: β))
    : β → Cofix F α
```

This corecursor runs one step of `F` and interprets a modifier whenever it encounters `recall` or `cont`. The modifier payload is constant in the functor arguments, so the construction stays within QPFs. This matches the intended use for nested guarded corecursion.

## Common instantiations

The module provides small wrappers that cover typical patterns. `corecMod_id` ignores modifiers and recovers the behavior of `corec`. `corecMod_with` is a thin wrapper that keeps the signature explicit. `corecMod_list` folds a list of modifier tags through an interpreter.

The following instantiations are provided by QpfTypes.

- `corecMod_id`. Uses `Mod := PUnit` and ignores modifiers.
- `corecMod_with`. Uses a caller-supplied `apply` function.
- `corecMod_list`. Uses `Mod := List ι` and folds modifiers with an interpreter.
- `corecMod_endo`. Uses a `CoeeFun` modifier payload and applies it directly.

```lean
def corecMod_id
    {F : TypeFun n.succ} {α : TypeVec n}
    [MvFunctor F] [MvQPF F]
    (f : β → UncurriedMod F PUnit (α ::: β))
    : β → Cofix F α
```

This specialization is useful when you want the generalized structure but do not need any modifier semantics. It is also a stable default for migrating code that already uses `corec`.

## Endomorphism modifiers

`corecMod_endo` supports modifier payloads that are functions on the thunk itself. This is the direct way to express an update like `map` on a recursive result.

```lean
def corecMod_endo
    {F : TypeFun n.succ} {α : TypeVec n} {Mod : Type u}
    [MvFunctor F] [MvQPF F]
    [CoeeFun Mod (fun _ => UncurriedMod F Mod (α ::: β) → UncurriedMod F Mod (α ::: β))]
    (f : β → UncurriedMod F Mod (α ::: β))
    : β → Cofix F α
```

This helper treats each modifier as a function and applies it directly. It is useful when the modifier type is already a function or carries a coercion to one.

## Usage

Import the module and the relevant functors for your construction. If you want a low-friction entry point, start with `corecMod_id` and then switch to `corecMod_with` once you need custom modifier behavior. If your modifiers form a small DSL, use `corecMod_list` with a single interpreter function.
