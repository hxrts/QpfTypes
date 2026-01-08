import Qpf

/-!
# Interaction Trees: Core Definitions

This module defines the core `ITree` coinductive type and its basic structural lemmas.

## Main Definitions

- `ITree α ε ρ`: The interaction tree type
- `ITree.corec`: Corecursion principle for defining ITrees
- `ITree.cases`: Case eliminator for ITrees
- `ITree.spin`: The diverging tree (infinite tau sequence)

## Implementation Notes

### Ideal Definition (Not Yet Supported)

We would like to define interaction trees with dependent events:
```
codata ITree (ε : Type → Type) ρ where
  | ret (r : ρ)
  | tau (t : ITree ε ρ)
  | vis {α : Type} (e : ε α) (k : α → ITree ε ρ)
```

However, the `vis` constructor involves a dependent arrow, which the QPF framework
does not currently support. As a workaround, we fix the response type `α` as a
parameter of the entire type.

### QPF Quotient Encoding

The `codata` command generates ITrees as a quotient of polynomial functors (QPF).
This encoding has implications for proofs:
- Direct case analysis on ITree constructors can fail due to quotient elimination
- We provide `dest_*` lemmas that work via the underlying `Cofix.dest` operation
- Constructor injectivity/distinctness lemmas are derived from these

## References

- [Interaction Trees (POPL 2020)](https://arxiv.org/abs/1906.00046)
- [Coq ITree Library](https://github.com/DeepSpec/InteractionTrees)
-/

/-!
## ITree Definition
-/

/-- Interaction trees with fixed response type `α`, event type `ε`, and return type `ρ`.

An ITree represents a computation that can:
- `ret r`: Return a value `r : ρ`
- `tau t`: Perform a silent/internal step, then continue as `t`
- `vis e k`: Perform visible event `e : ε`, receive response `a : α`, continue as `k a` -/
codata ITree (α : Type) ε ρ where
  | ret (r : ρ)
  | tau (t : ITree α ε ρ)
  | vis : ε → (α → ITree α ε ρ) → ITree α ε ρ

namespace ITree

/-!
## Corecursion and Elimination
-/

/-- The ITree base functor is a QPF (derived from the macro-generated polynomial). -/
instance instMvQPF_ITreeBase {α : Type} : MvQPF (TypeFun.ofCurried (ITree.Base α)) := by
  infer_instance

/-- Corecursion principle for ITrees.

Given a transition function `f : β → ITree.Base α ε ρ β` and initial state `b : β`,
produces an ITree by repeatedly applying `f` to generate the tree structure.

This is the low-level way of defining an ITree from a state machine. -/
def corec {β α ε ρ : Type} (f : β → ITree.Base α ε ρ β) (b : β) : ITree α ε ρ :=
  MvQPF.Cofix.corec (F := TypeFun.ofCurried (ITree.Base α)) f b

/-- Case eliminator for ITrees.

Allows defining functions on ITrees by providing handlers for each constructor.
Uses the underlying QPF machinery via `Cofix.dest`. -/
@[cases_eliminator, elab_as_elim]
def cases {α ε ρ : Type} {motive : ITree α ε ρ → Sort u}
    (ret : (r : ρ) → motive (.ret r))
    (tau : (x : ITree α ε ρ) → motive (.tau x))
    (vis : (e : ε) → (k : α → ITree α ε ρ) → motive (.vis e k)) :
    ∀ (x : ITree α ε ρ), motive x :=
  fun x =>
    match h : MvQPF.Cofix.dest x with
    | .ret r =>
      have h : x = ITree.ret r := by
        apply_fun MvQPF.Cofix.mk at h
        simpa [MvQPF.Cofix.mk_dest] using h
      h ▸ ret r
    | .tau y =>
      have h : x = ITree.tau y := by
        apply_fun MvQPF.Cofix.mk at h
        simpa [MvQPF.Cofix.mk_dest] using h
      h ▸ tau y
    | .vis e k =>
      have h : x = ITree.vis e k := by
        apply_fun MvQPF.Cofix.mk at h
        simpa [MvQPF.Cofix.mk_dest] using h
      h ▸ vis e k

/-!
## Notable ITrees
-/

/-- The diverging tree: an infinite sequence of tau nodes.

`spin` represents non-termination. It satisfies `spin = tau spin`. -/
def spin : ITree α ε ρ :=
  corec (fun () => .tau ()) ()

/-!
## Destructor Lemmas

These lemmas characterize the `dest` of each constructor. They are the foundation
for proving constructor injectivity and distinctness without triggering QPF
quotient elimination failures.
-/

/-- The destructor of `ret r` is `Base.ret r`. -/
theorem dest_ret {r : ρ} : MvQPF.Cofix.dest (ITree.ret r : ITree α ε ρ) = .ret r := by
  simp only [ITree.ret, MvQPF.Cofix.dest_mk]

/-- The destructor of `tau t` is `Base.tau t`. -/
theorem dest_tau {t : ITree α ε ρ} : MvQPF.Cofix.dest (ITree.tau t) = .tau t := by
  simp only [ITree.tau, MvQPF.Cofix.dest_mk]

/-- The destructor of `vis e k` is `Base.vis e k`. -/
theorem dest_vis {e : ε} {k : α → ITree α ε ρ} : MvQPF.Cofix.dest (ITree.vis e k) = .vis e k := by
  simp only [ITree.vis, MvQPF.Cofix.dest_mk]

/-!
## Constructor Injectivity

These lemmas establish that each constructor is injective.
-/

/-- `tau` is injective: `tau t₁ = tau t₂ → t₁ = t₂`. -/
theorem tau_inj {t₁ t₂ : ITree α ε ρ} (h : ITree.tau t₁ = ITree.tau t₂) : t₁ = t₂ := by
  have h1 := dest_tau (t := t₁)
  have h2 := dest_tau (t := t₂)
  rw [h] at h1
  simp only [h1] at h2
  cases h2
  rfl

/-- `ret` is injective: `ret r₁ = ret r₂ → r₁ = r₂`. -/
theorem ret_inj {r₁ r₂ : ρ} (h : (ITree.ret r₁ : ITree α ε ρ) = ITree.ret r₂) : r₁ = r₂ := by
  have h1 := dest_ret (r := r₁) (α := α) (ε := ε)
  have h2 := dest_ret (r := r₂) (α := α) (ε := ε)
  rw [h] at h1
  simp only [h1] at h2
  cases h2
  rfl

/-- `vis` is injective in both the event and continuation. -/
theorem vis_inj {e₁ e₂ : ε} {k₁ k₂ : α → ITree α ε ρ}
    (h : ITree.vis e₁ k₁ = ITree.vis e₂ k₂) : e₁ = e₂ ∧ k₁ = k₂ := by
  have h1 := dest_vis (e := e₁) (k := k₁)
  have h2 := dest_vis (e := e₂) (k := k₂)
  rw [h] at h1
  simp only [h1] at h2
  cases h2
  exact ⟨rfl, rfl⟩

/-!
## Constructor Distinctness

These lemmas establish that different constructors produce different values.
-/

/-- `tau` and `ret` are distinct: `tau t ≠ ret r`. -/
theorem tau_ne_ret {t : ITree α ε ρ} {r : ρ} : ITree.tau t ≠ ITree.ret r := by
  intro h
  have h1 := dest_tau (t := t)
  have h2 := dest_ret (r := r) (α := α) (ε := ε)
  rw [h] at h1
  simp only [h1] at h2
  cases h2

/-- `ret` and `tau` are distinct: `ret r ≠ tau t`. -/
theorem ret_ne_tau {r : ρ} {t : ITree α ε ρ} : ITree.ret r ≠ ITree.tau t :=
  fun h => tau_ne_ret h.symm

/-- `tau` and `vis` are distinct: `tau t ≠ vis e k`. -/
theorem tau_ne_vis {t : ITree α ε ρ} {e : ε} {k : α → ITree α ε ρ} : ITree.tau t ≠ ITree.vis e k := by
  intro h
  have h1 := dest_tau (t := t)
  have h2 := dest_vis (e := e) (k := k)
  rw [h] at h1
  simp only [h1] at h2
  cases h2

/-- `ret` and `vis` are distinct: `ret r ≠ vis e k`. -/
theorem ret_ne_vis {r : ρ} {e : ε} {k : α → ITree α ε ρ} : ITree.ret r ≠ ITree.vis e k := by
  intro h
  have h1 := dest_ret (r := r) (α := α) (ε := ε)
  have h2 := dest_vis (e := e) (k := k)
  rw [h] at h1
  simp only [h1] at h2
  cases h2

end ITree
