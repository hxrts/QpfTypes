import Qpf.ITree.Basic

/-!
# Membership-Based Weak Bisimulation

This module defines weak bisimulation using observable behaviors rather than
structural F-functor matching. This approach avoids the QPF quotient elimination
issues that make the F-based `EquivUTT` formulation challenging.

## Key Insight

Instead of matching on ITree constructors (which fails due to QPF encoding),
we define equivalence in terms of what behaviors a tree can exhibit:
- **Termination**: What values can the tree return after some tau steps?
- **Events**: What visible events can the tree perform after some tau steps?

The predicates `Terminates` and `CanDo` capture these behaviors without having
ITree constructors in their indices, making them amenable to case analysis.

## Main Definitions

- `Terminates t r`: Tree `t` can return value `r` after zero or more tau steps
- `CanDo t e k`: Tree `t` can perform event `e` with continuation `k` after tau steps
- `Bisim.F`: One-step functor for membership-based bisimulation
- `Bisim`: Greatest fixpoint of `Bisim.F` (weak bisimulation)

## Comparison with EquivUTT

| Aspect       | Bisim                 | EquivUTT                   |
|--------------|-----------------------|----------------------------|
| Index types  | `ρ`, `ε`, `α → ITree` | ITree constructors         |
| Transitivity | Complete proof        | 8 sorries (QPF limitation) |
| Style        | Behavioral/membership | Structural/F-functor       |

For practical use, prefer `Bisim` as it has complete proofs.
-/

namespace ITree

/-!
## Observable Behavior Predicates

These predicates capture what a tree "can do" after stripping away tau steps.
Crucially, they don't have ITree constructors in their indices, so we can
freely case-analyze proofs of these predicates.
-/

/-- A tree can terminate with value `r` after some tau steps.

`Terminates t r` holds when `t` eventually reaches `ret r` through zero or more
tau transitions. This captures the "termination behavior" of a tree. -/
inductive Terminates : ITree α ε ρ → ρ → Prop
  | ret : Terminates (.ret r) r
  | tau : Terminates t r → Terminates (.tau t) r

/-- A tree can perform visible event `e` with continuation `k` after some tau steps.

`CanDo t e k` holds when `t` eventually reaches `vis e k` through zero or more
tau transitions. This captures the "event behavior" of a tree. -/
inductive CanDo : ITree α ε ρ → ε → (α → ITree α ε ρ) → Prop
  | vis : CanDo (.vis e k) e k
  | tau : CanDo t e k → CanDo (.tau t) e k

/-!
## Tau-Unwrapping Lemmas

These lemmas let us "peel" taus from the ITree argument of `Terminates` and `CanDo`.
The proof technique uses induction with generalization and the ITree distinctness
lemmas from `Basic.lean` to avoid direct case analysis on concrete ITree shapes.
-/

/-- Unwrap a tau from a `Terminates` proof: `Terminates (.tau t) r → Terminates t r`. -/
theorem Terminates.of_tau {t : ITree α ε ρ} (h : Terminates (.tau t) r) : Terminates t r := by
  generalize hx : (ITree.tau t : ITree α ε ρ) = x at h
  induction h with
  | ret => exact absurd hx ITree.tau_ne_ret
  | tau _ ih =>
    have : t = _ := ITree.tau_inj hx
    subst this
    assumption

/-- Termination is invariant under tau: `Terminates (.tau t) r ↔ Terminates t r`. -/
theorem Terminates.tau_iff {t : ITree α ε ρ} : Terminates (.tau t) r ↔ Terminates t r :=
  ⟨Terminates.of_tau, .tau⟩

/-- Unwrap a tau from a `CanDo` proof: `CanDo (.tau t) e k → CanDo t e k`. -/
theorem CanDo.of_tau {t : ITree α ε ρ} (h : CanDo (.tau t) e k) : CanDo t e k := by
  generalize hx : (ITree.tau t : ITree α ε ρ) = x at h
  induction h with
  | vis => exact absurd hx ITree.tau_ne_vis
  | tau _ ih =>
    have : t = _ := ITree.tau_inj hx
    subst this
    assumption

/-- CanDo is invariant under tau: `CanDo (.tau t) e k ↔ CanDo t e k`. -/
theorem CanDo.tau_iff {t : ITree α ε ρ} : CanDo (.tau t) e k ↔ CanDo t e k :=
  ⟨CanDo.of_tau, .tau⟩

/-!
## Bisimulation Definition

We define bisimulation as the greatest fixpoint of a functor `Bisim.F` that
relates trees with the same observable behaviors.
-/

/-- One-step functor for membership-based weak bisimulation.

Two trees are related by `Bisim.F R` if they have:
1. The same termination behavior (both terminate to `r`, or neither does)
2. The same event behavior with `R`-related continuations

Unlike `EquivUTT.F`, this functor doesn't have ITree constructors in its indices,
which avoids QPF quotient elimination issues. -/
def Bisim.F (R : ITree α ε ρ → ITree α ε ρ → Prop) (t₁ t₂ : ITree α ε ρ) : Prop :=
  -- Same termination behavior
  (∀ r, Terminates t₁ r ↔ Terminates t₂ r) ∧
  -- Same visible events with R-related continuations (left-to-right)
  (∀ e k₁, CanDo t₁ e k₁ → ∃ k₂, CanDo t₂ e k₂ ∧ ∀ a, R (k₁ a) (k₂ a)) ∧
  -- Same visible events with R-related continuations (right-to-left)
  (∀ e k₂, CanDo t₂ e k₂ → ∃ k₁, CanDo t₁ e k₁ ∧ ∀ a, R (k₁ a) (k₂ a))

/-- Membership-based weak bisimulation (greatest fixpoint of `Bisim.F`).

Two trees are bisimilar if there exists a relation `R` that:
1. Is a post-fixpoint of `Bisim.F` (i.e., `R ⊆ Bisim.F R`)
2. Contains the pair `(t₁, t₂)`

This is equivalent to saying `t₁` and `t₂` have the same observable behaviors
at all depths. -/
def Bisim (t₁ t₂ : ITree α ε ρ) : Prop :=
  ∃ R, (∀ a b, R a b → Bisim.F R a b) ∧ R t₁ t₂

namespace Bisim

/-!
## Bisim is an Equivalence Relation

We prove reflexivity, symmetry, and transitivity for `Bisim`.
The key insight is that transitivity works because `Bisim.F` doesn't have
ITree indices, so we can freely compose witness relations.
-/

/-- Bisim is reflexive: every tree is bisimilar to itself. -/
theorem refl (t : ITree α ε ρ) : Bisim t t := by
  refine ⟨(· = ·), ?_, rfl⟩
  intro a b hab
  subst hab
  exact ⟨fun _ => Iff.rfl, fun e k h => ⟨k, h, fun _ => rfl⟩, fun e k h => ⟨k, h, fun _ => rfl⟩⟩

/-- Bisim is symmetric: if `t₁ ∼ t₂` then `t₂ ∼ t₁`. -/
theorem symm {t₁ t₂ : ITree α ε ρ} : Bisim t₁ t₂ → Bisim t₂ t₁ := by
  rintro ⟨R, hR, h⟩
  refine ⟨flip R, ?_, h⟩
  intro a b hab
  obtain ⟨hterm, hvis₁, hvis₂⟩ := hR b a hab
  exact ⟨fun r => (hterm r).symm, hvis₂, hvis₁⟩

/-- Bisim is transitive: if `t₁ ∼ t₂` and `t₂ ∼ t₃` then `t₁ ∼ t₃`.

This proof works because `Bisim.F` doesn't have ITree indices! The witness
relation for transitivity is the composition `R' a c := ∃ b, R₁ a b ∧ R₂ b c`. -/
theorem trans {t₁ t₂ t₃ : ITree α ε ρ} : Bisim t₁ t₂ → Bisim t₂ t₃ → Bisim t₁ t₃ := by
  rintro ⟨R₁, hR₁, h₁⟩ ⟨R₂, hR₂, h₂⟩
  -- Witness: composition of relations
  let R' (a c) := ∃ b, R₁ a b ∧ R₂ b c
  refine ⟨R', ?_, ⟨t₂, h₁, h₂⟩⟩
  -- Show R' is a post-fixpoint of Bisim.F
  intro a c ⟨b, hab, hbc⟩
  obtain ⟨hterm₁, hvis₁_lr, hvis₁_rl⟩ := hR₁ a b hab
  obtain ⟨hterm₂, hvis₂_lr, hvis₂_rl⟩ := hR₂ b c hbc
  constructor
  -- Termination: transitivity of ↔
  · intro r
    exact (hterm₁ r).trans (hterm₂ r)
  constructor
  -- Visible events (left-to-right): compose through b
  · intro e k₁ hk₁
    obtain ⟨k₂, hk₂, hcont₁⟩ := hvis₁_lr e k₁ hk₁
    obtain ⟨k₃, hk₃, hcont₂⟩ := hvis₂_lr e k₂ hk₂
    exact ⟨k₃, hk₃, fun a => ⟨k₂ a, hcont₁ a, hcont₂ a⟩⟩
  -- Visible events (right-to-left): compose through b
  · intro e k₃ hk₃
    obtain ⟨k₂, hk₂, hcont₂⟩ := hvis₂_rl e k₃ hk₃
    obtain ⟨k₁, hk₁, hcont₁⟩ := hvis₁_rl e k₂ hk₂
    exact ⟨k₁, hk₁, fun a => ⟨k₂ a, hcont₁ a, hcont₂ a⟩⟩

/-!
## Typeclass Instances
-/

instance : Trans (Bisim (α := α) (ε := ε) (ρ := ρ)) Bisim Bisim where
  trans := Bisim.trans

instance : Equivalence (Bisim (α := α) (ε := ε) (ρ := ρ)) where
  refl := Bisim.refl
  symm := Bisim.symm
  trans := Bisim.trans

/-!
## Tau-Peeling for Bisimulation

These lemmas allow stripping tau from either side of a bisimulation.
This works because `Terminates` and `CanDo` are regular inductives that
we can case-analyze, unlike the QPF-generated ITree type.
-/

/-- Bisim is a post-fixpoint of `Bisim.F`.

This is a key structural property: any bisimilar pair satisfies `Bisim.F Bisim`. -/
theorem Bisim_isFixpoint : ∀ x y, Bisim (α := α) (ε := ε) (ρ := ρ) x y → F Bisim x y := by
  intro x y ⟨R, isFixpoint, hR⟩
  obtain ⟨hterm, hvis_lr, hvis_rl⟩ := isFixpoint _ _ hR
  exact ⟨hterm,
    fun e k₁ h => let ⟨k₂, hk, hc⟩ := hvis_lr e k₁ h
                  ⟨k₂, hk, fun a => ⟨R, isFixpoint, hc a⟩⟩,
    fun e k₂ h => let ⟨k₁, hk, hc⟩ := hvis_rl e k₂ h
                  ⟨k₁, hk, fun a => ⟨R, isFixpoint, hc a⟩⟩⟩

/-- Stripping tau from the left preserves bisimulation: `(.tau t) ∼ b → t ∼ b`. -/
theorem tau_left {t : ITree α ε ρ} {b : ITree α ε ρ} : Bisim (.tau t) b → Bisim t b := by
  intro ⟨R, isFixpoint, hR⟩
  -- Use R' = fun x y => R (.tau x) y ∨ R x y as the witness
  -- This avoids circularity while capturing the tau-stripped relation
  let R' := fun x y => R (.tau x) y ∨ R x y
  refine ⟨R', ?isPostFixpoint, Or.inl hR⟩
  -- Show R' is a post-fixpoint of Bisim.F
  intro x y hxy
  cases hxy with
  | inl h =>
    -- h : R (.tau x) y
    obtain ⟨hterm', hvis_lr', hvis_rl'⟩ := isFixpoint _ _ h
    constructor
    · -- Termination: use tau_iff to strip tau from Terminates (.tau x)
      intro r
      exact Terminates.tau_iff.symm.trans (hterm' r)
    constructor
    · -- CanDo left-to-right
      intro e k₁ hk₁
      obtain ⟨k₂, hk₂, hcont⟩ := hvis_lr' e k₁ (CanDo.tau hk₁)
      exact ⟨k₂, hk₂, fun a => Or.inr (hcont a)⟩
    · -- CanDo right-to-left: unwrap CanDo (.tau x) using tau_iff
      intro e k₂ hk₂
      obtain ⟨k₁, hk₁, hcont⟩ := hvis_rl' e k₂ hk₂
      exact ⟨k₁, CanDo.tau_iff.mp hk₁, fun a => Or.inr (hcont a)⟩
  | inr h =>
    -- h : R x y, directly use the post-fixpoint property
    obtain ⟨hterm', hvis_lr', hvis_rl'⟩ := isFixpoint _ _ h
    exact ⟨hterm',
      fun e k₁ hk₁ => let ⟨k₂, hk₂, hc⟩ := hvis_lr' e k₁ hk₁
                      ⟨k₂, hk₂, fun a => Or.inr (hc a)⟩,
      fun e k₂ hk₂ => let ⟨k₁, hk₁, hc⟩ := hvis_rl' e k₂ hk₂
                      ⟨k₁, hk₁, fun a => Or.inr (hc a)⟩⟩

/-- Stripping tau from the right preserves bisimulation: `a ∼ (.tau t) → a ∼ t`. -/
theorem tau_right {a : ITree α ε ρ} {t : ITree α ε ρ} : Bisim a (.tau t) → Bisim a t := by
  intro h
  exact Bisim.symm (tau_left (Bisim.symm h))

end Bisim

end ITree
