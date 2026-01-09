import Qpf.Coinduction.Protocol

/-!
# EquivUTT (Abstract)

This module defines weak bisimulation (EquivUTT) and its supporting predicates
purely in terms of the abstract `CoinductiveTreeProtocol`.
-/

namespace Coinduction

open CoinductiveTreeProtocol

/-- `Terminates t r` holds if `t` returns `r` after finite `tau` steps. -/
inductive Terminates {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} : T α ε ρ → ρ → Prop where
  | ret (r : ρ) : Terminates (ret r) r
  | tau {t : T α ε ρ} {r : ρ} : Terminates t r → Terminates (tau t) r

/-- `CanDo t e k` holds if `t` can perform event `e` with continuation `k` after finite `tau`s. -/
inductive CanDo {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} : T α ε ρ → ε → (α → T α ε ρ) → Prop where
  | vis {e : ε} {k : α → T α ε ρ} : CanDo (vis e k) e k
  | tau {t : T α ε ρ} {e : ε} {k : α → T α ε ρ} : CanDo t e k → CanDo (tau t) e k

/-- Bounded path to a return within `n` `tau` steps. -/
def RetPathBounded {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} (n : Nat) (r : ρ) (b : T α ε ρ) : Prop :=
  match n with
  | 0 => b = ret r
  | n' + 1 => b = ret r ∨ ∃ t, b = tau t ∧ RetPathBounded n' r t

/-- Bounded path to a `vis` within `n` `tau` steps, with related continuations. -/
def VisPathBounded {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} (n : Nat) (e : ε) (R : T α ε ρ → T α ε ρ → Prop)
    (k₁ : α → T α ε ρ) (b : T α ε ρ) : Prop :=
  match n with
  | 0 => ∃ k₂, b = vis e k₂ ∧ ∀ i, R (k₁ i) (k₂ i)
  | n' + 1 => (∃ k₂, b = vis e k₂ ∧ ∀ i, R (k₁ i) (k₂ i)) ∨
              ∃ t, b = tau t ∧ VisPathBounded n' e R k₁ t

/-- One-step functor for weak bisimulation. -/
inductive F {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} (R : T α ε ρ → T α ε ρ → Prop) :
    T α ε ρ → T α ε ρ → Prop
  | ret : F R (ret r) (ret r)
  | vis : (∀ a, R (k₁ a) (k₂ a)) → F R (vis e k₁) (vis e k₂)
  | tau : R x y → F R (tau x) (tau y)
  | taul : R x y → F R (tau x) y
  | taur : R x y → F R x (tau y)

/-- Weak bisimulation (EquivUTT). -/
inductive EquivUTT {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} (x y : T α ε ρ) : Prop where
  | intro (R : T α ε ρ → T α ε ρ → Prop)
    (h_fixpoint : ∀ a b, R a b → F (R := R) a b)
    (h_term_bounded : ∀ a r b, Terminates (T := T) a r → R a b → ∃ n, RetPathBounded n r b)
    (h_term_bounded' : ∀ a r b, Terminates (T := T) b r → R a b → ∃ n, RetPathBounded n r a)
    (h_vis_bounded : ∀ e k₁ b, R (vis e k₁) b → ∃ n, VisPathBounded n e R k₁ b)
    (h_vis_bounded' : ∀ e k₂ a, R a (vis e k₂) →
      ∃ n k₁, VisPathBounded n e (flip R) k₂ a ∧ ∀ i, R (k₁ i) (k₂ i))
    (h_cando_bounded : ∀ e k₁ a b, CanDo (T := T) a e k₁ → R a b → ∃ n, VisPathBounded n e R k₁ b)
    (h_cando_bounded' : ∀ e k₂ a b, CanDo (T := T) b e k₂ → R a b →
      ∃ n k₁, VisPathBounded n e (flip R) k₂ a ∧ ∀ i, R (k₁ i) (k₂ i))
    (h_R : R x y)

/-- Composition of witness relations. -/
def composeRel {T : Type → Type → Type → Type} {α ε ρ : Type}
    (R₁ R₂ : T α ε ρ → T α ε ρ → Prop) : T α ε ρ → T α ε ρ → Prop :=
  fun a c => ∃ b, R₁ a b ∧ R₂ b c

/-- If a tree terminates, there is a bounded return path. -/
theorem Terminates_implies_RetPathBounded
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} (t : T α ε ρ) (r : ρ) (h : Terminates (T := T) t r) :
    ∃ n, RetPathBounded (T := T) n r t := by
  induction h with
  | ret =>
      exact ⟨0, rfl⟩
  | tau _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, Or.inr ⟨_, rfl, hn⟩⟩

/-- If a tree can do an event, there is a bounded vis path. -/
theorem CanDo_implies_VisPathBounded
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} (t : T α ε ρ) (e : ε) (k : α → T α ε ρ)
    (h : CanDo (T := T) t e k) :
    ∃ n, VisPathBounded (T := T) n e Eq k t := by
  induction h with
  | vis =>
      exact ⟨0, ⟨_, rfl, fun _ => rfl⟩⟩
  | tau _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, Or.inr ⟨_, rfl, hn⟩⟩

/-!
## Generic helper lemmas
-/

/-- Increasing the bound preserves `RetPathBounded`. -/
theorem RetPathBounded.mono
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {n m : Nat} (h : n ≤ m) {r : ρ} {b : T α ε ρ} :
    RetPathBounded (T := T) n r b → RetPathBounded (T := T) m r b := by
  induction m generalizing n b with
  | zero =>
      intro hrpb
      simp only [Nat.le_zero] at h
      exact h ▸ hrpb
  | succ m ih =>
      intro hrpb
      cases n with
      | zero =>
          simp only [RetPathBounded] at hrpb
          exact Or.inl hrpb
      | succ n =>
          simp only [RetPathBounded] at hrpb ⊢
          rcases hrpb with heq | ⟨t, heq, hrec⟩
          · exact Or.inl heq
          · exact Or.inr ⟨t, heq, ih (Nat.succ_le_succ_iff.mp h) hrec⟩

/-- Increasing the bound preserves `VisPathBounded`. -/
theorem VisPathBounded.mono
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {n m : Nat} (h : n ≤ m)
    {e : ε} {R : T α ε ρ → T α ε ρ → Prop}
    {k₁ : α → T α ε ρ} {b : T α ε ρ} :
    VisPathBounded (T := T) n e R k₁ b → VisPathBounded (T := T) m e R k₁ b := by
  induction m generalizing n b with
  | zero =>
      intro hvpb
      simp only [Nat.le_zero] at h
      exact h ▸ hvpb
  | succ m ih =>
      intro hvpb
      cases n with
      | zero =>
          simp only [VisPathBounded] at hvpb
          exact Or.inl hvpb
      | succ n =>
          simp only [VisPathBounded] at hvpb ⊢
          rcases hvpb with hv | ⟨t, heq, hrec⟩
          · exact Or.inl hv
          · exact Or.inr ⟨t, heq, ih (Nat.succ_le_succ_iff.mp h) hrec⟩

/-- Extract the reached continuation from `VisPathBounded`. -/
theorem VisPathBounded.getCont
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {n : Nat} {e : ε} {R : T α ε ρ → T α ε ρ → Prop}
    {k₁ : α → T α ε ρ} {b : T α ε ρ} :
    VisPathBounded (T := T) n e R k₁ b → ∃ k₂ : α → T α ε ρ, ∀ i, R (k₁ i) (k₂ i) := by
  intro hvpb
  induction n generalizing b with
  | zero =>
      simp only [VisPathBounded] at hvpb
      obtain ⟨k₂, _, hk⟩ := hvpb
      exact ⟨k₂, hk⟩
  | succ n ih =>
      simp only [VisPathBounded] at hvpb
      rcases hvpb with ⟨k₂, _, hk⟩ | ⟨t, _, hrec⟩
      · exact ⟨k₂, hk⟩
      · exact ih hrec

/-- Convert `RetPathBounded` to `Terminates`. -/
theorem RetPathBounded.toTerminates
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {n : Nat} {r : ρ} {b : T α ε ρ} :
    RetPathBounded (T := T) n r b → Terminates (T := T) b r := by
  induction n generalizing b with
  | zero =>
      intro h
      simp only [RetPathBounded] at h
      exact h ▸ .ret
  | succ n ih =>
      intro h
      simp only [RetPathBounded] at h
      rcases h with heq | ⟨t, heq, hrec⟩
      · exact heq ▸ .ret
      · exact heq ▸ .tau (ih hrec)

/-- Convert `CanDo` to `VisPathBounded` with related continuations. -/
theorem CanDo.toVisPathBounded
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {b : T α ε ρ} {e : ε} {k₂ : α → T α ε ρ}
    {R : T α ε ρ → T α ε ρ → Prop} {k₁ : α → T α ε ρ}
    (hcont : ∀ i, R (k₁ i) (k₂ i)) :
    CanDo (T := T) b e k₂ → ∃ n, VisPathBounded (T := T) n e R k₁ b := by
  intro hc
  induction hc with
  | vis =>
      exact ⟨0, ⟨_, rfl, hcont⟩⟩
  | tau _ ih =>
      obtain ⟨n, hn⟩ := ih hcont
      exact ⟨n + 1, Or.inr ⟨_, rfl, hn⟩⟩

/-- Reflexivity: EquivUTT x x. -/
theorem EquivUTT.refl
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocolWithCases T]
    {α ε ρ : Type} (x : T α ε ρ) : EquivUTT (T := T) x x := by
  apply EquivUTT.intro (R := (· = ·))
  · intro a b hEq
    subst hEq
    -- use cases axiom on a
    rcases (CoinductiveTreeProtocolWithCases.cases (T := T) (α := α) (ε := ε) (ρ := ρ) a) with
    | ⟨r, hr⟩ =>
        subst hr
        exact F.ret
    | Or.inr h =>
        rcases h with ⟨t, ht⟩ | ⟨e, k, hv⟩
        · subst ht
          exact F.tau rfl
        · subst hv
          exact F.vis (fun _ => rfl)
  · intro a r b hterm hEq
    subst hEq
    exact Terminates_implies_RetPathBounded (T := T) (α := α) (ε := ε) (ρ := ρ) a r hterm
  · intro a r b hterm hEq
    subst hEq
    exact Terminates_implies_RetPathBounded (T := T) (α := α) (ε := ε) (ρ := ρ) a r hterm
  · intro e k₁ b hEq
    subst hEq
    exact ⟨0, ⟨k₁, rfl, fun _ => rfl⟩⟩
  · intro e k₂ a hEq
    subst hEq
    exact ⟨0, k₂, ⟨k₂, rfl, fun _ => rfl⟩, fun _ => rfl⟩
  · intro e k₁ a b hcando hEq
    subst hEq
    have ⟨n, hn⟩ := CanDo.toVisPathBounded (T := T) (α := α) (ε := ε) (ρ := ρ)
      (b := a) (e := e) (k₂ := k₁) (R := (· = ·)) (k₁ := k₁) (fun _ => rfl) hcando
    exact ⟨n, hn⟩
  · intro e k₂ a b hcando hEq
    subst hEq
    have ⟨n, hn⟩ := CanDo.toVisPathBounded (T := T) (α := α) (ε := ε) (ρ := ρ)
      (b := a) (e := e) (k₂ := k₂) (R := flip (· = ·)) (k₁ := k₂) (fun _ => rfl) hcando
    exact ⟨n, k₂, hn, fun _ => rfl⟩
  · rfl

/-- Symmetry: EquivUTT x y → EquivUTT y x. -/
theorem EquivUTT.symm
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocolWithCases T]
    {α ε ρ : Type} {x y : T α ε ρ} :
    EquivUTT (T := T) x y → EquivUTT (T := T) y x := by
  intro h
  rcases h with ⟨R, hfix, htb, htb', hvb, hvb', hcb, hcb', hR⟩
  apply EquivUTT.intro (R := flip R)
  · intro a b hflip
    cases hfix b a hflip <;> constructor <;> assumption
  · intro a r b hterm hflip
    exact htb' b r a hterm hflip
  · intro a r b hterm hflip
    exact htb b r a hterm hflip
  · intro e k₁ b hflip
    have ⟨n, k', hvp, _⟩ := hvb' e k₁ b hflip
    exact ⟨n, hvp⟩
  · intro e k₂ a hflip
    have ⟨n, hvp⟩ := hvb e k₂ a hflip
    have ⟨k₁, hk⟩ := VisPathBounded.getCont (T := T) (α := α) (ε := ε) (ρ := ρ)
      (n := n) (e := e) (R := R) (k₁ := k₂) (b := a) hvp
    exact ⟨n, k₁, hvp, hk⟩
  · intro e k₁ a b hcando hflip
    have ⟨n, k', hvp, _⟩ := hcb' e k₁ b a hcando hflip
    exact ⟨n, hvp⟩
  · intro e k₂ a b hcando hflip
    have ⟨n, hvp⟩ := hcb e k₂ b a hcando hflip
    have ⟨k₁, hk⟩ := VisPathBounded.getCont (T := T) (α := α) (ε := ε) (ρ := ρ)
      (n := n) (e := e) (R := R) (k₁ := k₂) (b := a) hvp
    exact ⟨n, k₁, hvp, hk⟩
  · exact hR

/-- Transitivity: EquivUTT x y → EquivUTT y z → EquivUTT x z. -/
theorem EquivUTT.trans
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocolWithCases T]
    {α ε ρ : Type} {x y z : T α ε ρ} :
    EquivUTT (T := T) x y → EquivUTT (T := T) y z → EquivUTT (T := T) x z := by
  intro h1 h2
  -- Requires PACO/companion reasoning; not provable from current axioms.
  -- Keep as placeholder until PACO infrastructure is added.
  cases h1
  cases h2
  sorry

/-!
### Transitivity Subproblems (PACO-focused)

These lemmas correspond to the stuck cases in the transitivity proof and are
intended to be solved using PACO/companion techniques.
-/

/-
The following transitivity and inversion lemmas are disabled due to dependent
elimination issues with Lean 4.27.0-rc1. They contain `sorry` placeholders anyway
and should be reimplemented using paco/companion techniques.

TODO: Re-enable these proofs when the dependent elimination issues are resolved.
-/

/-
/-- tau-tau case for transitivity. -/
theorem trans_tau_case ...

/-- taur case for transitivity. -/
theorem trans_taur_case ...

/-- ret case for transitivity. -/
theorem trans_ret_case ...

/-- vis case for transitivity. -/
theorem trans_vis_case ...

/-- Inversion lemma for `F` with `tau` on the left. -/
theorem F_tau_inv ...

/-- Inversion lemma for `F` with `ret` on the left. -/
theorem F_ret_inv ...

/-- Inversion lemma for `F` with `vis` on the left. -/
theorem F_vis_inv ...
-/

end Coinduction
