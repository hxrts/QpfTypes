import Qpf.Coinduction.Protocol

/-!
# EquivUTT (Abstract, Protocol-Based)

This module develops weak bisimulation for any `CoinductiveTreeProtocol`:
- Observable predicates (`Terminates`, `CanDo`) and bounded paths
- F-based EquivUTT with explicit boundedness conditions
- A membership-based Bisim formulation and `EquivUTT ↔ Bisim`
- Transitivity of EquivUTT via the Bisim detour

No concrete coinductive type is required here; concrete instantiations (e.g. ITree)
can import this module and inherit the full equivalence theory.
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
      ∃ n, ∃ k₁ : α → T α ε ρ, VisPathBounded n e (flip R) k₂ a ∧ ∀ i, R (k₁ i) (k₂ i))
    (h_cando_bounded : ∀ e k₁ a b, CanDo (T := T) a e k₁ → R a b → ∃ n, VisPathBounded n e R k₁ b)
    (h_cando_bounded' : ∀ e k₂ a b, CanDo (T := T) b e k₂ → R a b →
      ∃ n, ∃ k₁ : α → T α ε ρ, VisPathBounded n e (flip R) k₂ a ∧ ∀ i, R (k₁ i) (k₂ i))
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
      exact h ▸ Terminates.ret r
  | succ n ih =>
      intro h
      simp only [RetPathBounded] at h
      rcases h with heq | ⟨t, heq, hrec⟩
      · exact heq ▸ Terminates.ret r
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
    {α ε ρ : Type} (x : T α ε ρ) : EquivUTT x x := by
  apply EquivUTT.intro (R := (· = ·))
  · intro a b hEq
    subst hEq
    -- use cases axiom on a
    match CoinductiveTreeProtocolWithCases.cases (T := T) (α := α) (ε := ε) (ρ := ρ) a with
    | Or.inl ⟨r, hr⟩ =>
        subst hr
        exact F.ret
    | Or.inr (Or.inl ⟨t, ht⟩) =>
        subst ht
        exact F.tau rfl
    | Or.inr (Or.inr ⟨e, k, hv⟩) =>
        subst hv
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
    EquivUTT x y → EquivUTT y x := by
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

/-!
## Membership-Based Weak Bisimulation (Abstract)

We use the observable predicates (`Terminates`, `CanDo`) to define a
membership-based bisimulation that avoids constructor matching issues.
This relation is equivalent to EquivUTT and provides a clean transitivity proof.
-/

theorem tau_ne_ret
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {t : T α ε ρ} {r : ρ} :
    (tau t : T α ε ρ) ≠ ret r := by
  intro h
  exact ret_ne_tau (r := r) (t := t) h.symm

theorem vis_ne_tau
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {t : T α ε ρ} {e : ε} {k : α → T α ε ρ} :
    (vis e k : T α ε ρ) ≠ tau t := by
  intro h
  exact tau_ne_vis (t := t) (e := e) (k := k) h.symm

theorem Terminates.of_tau
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {t : T α ε ρ} {r : ρ} :
    Terminates (T := T) (tau t) r → Terminates (T := T) t r := by
  intro h
  generalize hx : (tau t : T α ε ρ) = x at h
  induction h with
  | ret =>
      exact False.elim (tau_ne_ret (T := T) (α := α) (ε := ε) (ρ := ρ) hx)
  | tau _ ih =>
      have : t = _ := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) hx
      subst this
      exact ih

theorem Terminates.tau_iff
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {t : T α ε ρ} {r : ρ} :
    Terminates (T := T) (tau t) r ↔ Terminates (T := T) t r :=
  ⟨Terminates.of_tau (T := T) (α := α) (ε := ε) (ρ := ρ), Terminates.tau⟩

theorem CanDo.of_tau
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {t : T α ε ρ} {e : ε} {k : α → T α ε ρ} :
    CanDo (T := T) (tau t) e k → CanDo (T := T) t e k := by
  intro h
  generalize hx : (tau t : T α ε ρ) = x at h
  induction h with
  | vis =>
      exact False.elim (vis_ne_tau (T := T) (α := α) (ε := ε) (ρ := ρ) hx.symm)
  | tau _ ih =>
      have : t = _ := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) hx
      subst this
      exact ih

theorem CanDo.tau_iff
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {t : T α ε ρ} {e : ε} {k : α → T α ε ρ} :
    CanDo (T := T) (tau t) e k ↔ CanDo (T := T) t e k :=
  ⟨CanDo.of_tau (T := T) (α := α) (ε := ε) (ρ := ρ), CanDo.tau⟩

/-!
### Bisimulation (membership-based)
-/

def Bisim.F
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} (R : T α ε ρ → T α ε ρ → Prop) (t₁ t₂ : T α ε ρ) : Prop :=
  (∀ r, Terminates (T := T) t₁ r ↔ Terminates (T := T) t₂ r) ∧
  (∀ e k₁, CanDo (T := T) t₁ e k₁ →
    ∃ k₂, CanDo (T := T) t₂ e k₂ ∧ ∀ a, R (k₁ a) (k₂ a)) ∧
  (∀ e k₂, CanDo (T := T) t₂ e k₂ →
    ∃ k₁, CanDo (T := T) t₁ e k₁ ∧ ∀ a, R (k₁ a) (k₂ a))

def Bisim
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} (t₁ t₂ : T α ε ρ) : Prop :=
  ∃ R, (∀ a b, R a b → Bisim.F (T := T) (α := α) (ε := ε) (ρ := ρ) R a b) ∧ R t₁ t₂

namespace Bisim

theorem refl
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} (t : T α ε ρ) : Bisim (T := T) (α := α) (ε := ε) (ρ := ρ) t t := by
  refine ⟨(· = ·), ?_, rfl⟩
  intro a b hab
  subst hab
  exact ⟨fun _ => Iff.rfl, fun e k h => ⟨k, h, fun _ => rfl⟩,
    fun e k h => ⟨k, h, fun _ => rfl⟩⟩

theorem symm
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {t₁ t₂ : T α ε ρ} :
    Bisim (T := T) (α := α) (ε := ε) (ρ := ρ) t₁ t₂ →
    Bisim (T := T) (α := α) (ε := ε) (ρ := ρ) t₂ t₁ := by
  rintro ⟨R, hR, h⟩
  refine ⟨flip R, ?_, h⟩
  intro a b hab
  obtain ⟨hterm, hvis₁, hvis₂⟩ := hR b a hab
  exact ⟨fun r => (hterm r).symm, hvis₂, hvis₁⟩

theorem trans
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {t₁ t₂ t₃ : T α ε ρ} :
    Bisim (T := T) (α := α) (ε := ε) (ρ := ρ) t₁ t₂ →
    Bisim (T := T) (α := α) (ε := ε) (ρ := ρ) t₂ t₃ →
    Bisim (T := T) (α := α) (ε := ε) (ρ := ρ) t₁ t₃ := by
  rintro ⟨R₁, hR₁, h₁⟩ ⟨R₂, hR₂, h₂⟩
  let R' (a c) := ∃ b, R₁ a b ∧ R₂ b c
  refine ⟨R', ?_, ⟨t₂, h₁, h₂⟩⟩
  intro a c ⟨b, hab, hbc⟩
  obtain ⟨hterm₁, hvis₁_lr, hvis₁_rl⟩ := hR₁ a b hab
  obtain ⟨hterm₂, hvis₂_lr, hvis₂_rl⟩ := hR₂ b c hbc
  constructor
  · intro r
    exact (hterm₁ r).trans (hterm₂ r)
  constructor
  · intro e k₁ hk₁
    obtain ⟨k₂, hk₂, hcont₁⟩ := hvis₁_lr e k₁ hk₁
    obtain ⟨k₃, hk₃, hcont₂⟩ := hvis₂_lr e k₂ hk₂
    exact ⟨k₃, hk₃, fun a => ⟨k₂ a, hcont₁ a, hcont₂ a⟩⟩
  · intro e k₃ hk₃
    obtain ⟨k₂, hk₂, hcont₂⟩ := hvis₂_rl e k₃ hk₃
    obtain ⟨k₁, hk₁, hcont₁⟩ := hvis₁_rl e k₂ hk₂
    exact ⟨k₁, hk₁, fun a => ⟨k₂ a, hcont₁ a, hcont₂ a⟩⟩

theorem Bisim_isFixpoint
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} :
    ∀ x y, Bisim (T := T) (α := α) (ε := ε) (ρ := ρ) x y →
      Bisim.F (T := T) (α := α) (ε := ε) (ρ := ρ) Bisim x y := by
  intro x y ⟨R, isFixpoint, hR⟩
  obtain ⟨hterm, hvis_lr, hvis_rl⟩ := isFixpoint _ _ hR
  exact ⟨hterm,
    fun e k₁ h => let ⟨k₂, hk, hc⟩ := hvis_lr e k₁ h
                  ⟨k₂, hk, fun a => ⟨R, isFixpoint, hc a⟩⟩,
    fun e k₂ h => let ⟨k₁, hk, hc⟩ := hvis_rl e k₂ h
                  ⟨k₁, hk, fun a => ⟨R, isFixpoint, hc a⟩⟩⟩

theorem tau_left
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {t : T α ε ρ} {b : T α ε ρ} :
    Bisim (T := T) (α := α) (ε := ε) (ρ := ρ) (tau t) b →
    Bisim (T := T) (α := α) (ε := ε) (ρ := ρ) t b := by
  intro ⟨R, isFixpoint, hR⟩
  let R' := fun x y => R (tau x) y ∨ R x y
  refine ⟨R', ?_, Or.inl hR⟩
  intro x y hxy
  cases hxy with
  | inl h =>
      obtain ⟨hterm', hvis_lr', hvis_rl'⟩ := isFixpoint _ _ h
      constructor
      · intro r
        exact (Terminates.tau_iff (T := T) (α := α) (ε := ε) (ρ := ρ) (t := x) (r := r)).symm.trans
          (hterm' r)
      constructor
      · intro e k₁ hk₁
        obtain ⟨k₂, hk₂, hcont⟩ := hvis_lr' e k₁ (CanDo.tau hk₁)
        exact ⟨k₂, hk₂, fun a => Or.inr (hcont a)⟩
      · intro e k₂ hk₂
        obtain ⟨k₁, hk₁, hcont⟩ := hvis_rl' e k₂ hk₂
        exact ⟨k₁, (CanDo.tau_iff (T := T) (α := α) (ε := ε) (ρ := ρ) (t := x) (e := e)
          (k := k₁)).mp hk₁, fun a => Or.inr (hcont a)⟩
  | inr h =>
      obtain ⟨hterm', hvis_lr', hvis_rl'⟩ := isFixpoint _ _ h
      exact ⟨hterm',
        fun e k₁ hk₁ => let ⟨k₂, hk₂, hc⟩ := hvis_lr' e k₁ hk₁
                        ⟨k₂, hk₂, fun a => Or.inr (hc a)⟩,
        fun e k₂ hk₂ => let ⟨k₁, hk₁, hc⟩ := hvis_rl' e k₂ hk₂
                        ⟨k₁, hk₁, fun a => Or.inr (hc a)⟩⟩

theorem tau_right
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {a : T α ε ρ} {t : T α ε ρ} :
    Bisim (T := T) (α := α) (ε := ε) (ρ := ρ) a (tau t) →
    Bisim (T := T) (α := α) (ε := ε) (ρ := ρ) a t := by
  intro h
  exact Bisim.symm (T := T) (α := α) (ε := ε) (ρ := ρ)
    (tau_left (T := T) (α := α) (ε := ε) (ρ := ρ) (t := t) (b := a)
      (Bisim.symm (T := T) (α := α) (ε := ε) (ρ := ρ) h))

end Bisim

/-!
### EquivUTT ↔ Bisim
-/

theorem Bisim.toEquivUTT
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocolWithCases T]
    {α ε ρ : Type} {t₁ t₂ : T α ε ρ} :
    Bisim (T := T) (α := α) (ε := ε) (ρ := ρ) t₁ t₂ →
    EquivUTT (T := T) (α := α) (ε := ε) (ρ := ρ) t₁ t₂ := by
  intro hbisim
  apply EquivUTT.intro (R := Bisim)
  · intro a b hab
    rcases (CoinductiveTreeProtocolWithCases.cases (T := T) (α := α) (ε := ε) (ρ := ρ) a) with
    | ⟨r, hr⟩ =>
        subst hr
        have ⟨R, isFixpoint, hR⟩ := hab
        have ⟨hterm, _, _⟩ := isFixpoint _ _ hR
        have hb_term : Terminates (T := T) b r := (hterm r).mp .ret
        induction hb_term with
        | ret => exact .ret
        | tau _ ih => exact .taur (Bisim.tau_right (T := T) (α := α) (ε := ε) (ρ := ρ) hab)
    | Or.inr h =>
        rcases h with ⟨t, ht⟩ | ⟨e, k, hv⟩
        · subst ht
          exact .taul (Bisim.tau_left (T := T) (α := α) (ε := ε) (ρ := ρ) hab)
        · subst hv
          have ⟨R, isFixpoint, hR⟩ := hab
          have ⟨_, hvis_lr, _⟩ := isFixpoint _ _ hR
          have ⟨k₂, hk₂, hcont⟩ := hvis_lr e k .vis
          induction hk₂ with
          | vis =>
              apply EquivUTT.F.vis
              intro i
              exact ⟨R, isFixpoint, hcont i⟩
          | tau _ ih =>
              exact .taur (Bisim.tau_right (T := T) (α := α) (ε := ε) (ρ := ρ) hab)
  · intro a r b hterm hab
    have hF := Bisim.Bisim_isFixpoint (T := T) (α := α) (ε := ε) (ρ := ρ) a b hab
    have ⟨hterm_iff, _, _⟩ := hF
    have ht : Terminates (T := T) b r := (hterm_iff r).mp hterm
    exact Terminates_implies_RetPathBounded (T := T) (α := α) (ε := ε) (ρ := ρ) b r ht
  · intro a r b hterm hab
    have hF := Bisim.Bisim_isFixpoint (T := T) (α := α) (ε := ε) (ρ := ρ) a b hab
    have ⟨hterm_iff, _, _⟩ := hF
    have ht : Terminates (T := T) a r := (hterm_iff r).mpr hterm
    exact Terminates_implies_RetPathBounded (T := T) (α := α) (ε := ε) (ρ := ρ) a r ht
  · intro e k₁ b hab
    have hF := Bisim.Bisim_isFixpoint (T := T) (α := α) (ε := ε) (ρ := ρ) (vis e k₁) b hab
    have ⟨_, hvis_lr, _⟩ := hF
    have ⟨k₂, hk₂, hcont⟩ := hvis_lr e k₁ .vis
    exact CanDo.toVisPathBounded (T := T) (α := α) (ε := ε) (ρ := ρ)
      (b := b) (e := e) (k₂ := k₂) (R := Bisim) (k₁ := k₁) hcont hk₂
  · intro e k₂ a hab
    have hF := Bisim.Bisim_isFixpoint (T := T) (α := α) (ε := ε) (ρ := ρ) a (vis e k₂) hab
    have ⟨_, _, hvis_rl⟩ := hF
    have ⟨k₁, hk₁, hcont⟩ := hvis_rl e k₂ .vis
    have ⟨n, hvpb⟩ := CanDo.toVisPathBounded (T := T) (α := α) (ε := ε) (ρ := ρ)
      (b := a) (e := e) (k₂ := k₁) (R := flip Bisim) (k₁ := k₂) (fun i => hcont i) hk₁
    exact ⟨n, k₁, hvpb, hcont⟩
  · intro e k₁ a b hcando hab
    have hF := Bisim.Bisim_isFixpoint (T := T) (α := α) (ε := ε) (ρ := ρ) a b hab
    have ⟨_, hvis_lr, _⟩ := hF
    have ⟨k₂, hk₂, hcont⟩ := hvis_lr e k₁ hcando
    exact CanDo.toVisPathBounded (T := T) (α := α) (ε := ε) (ρ := ρ)
      (b := b) (e := e) (k₂ := k₂) (R := Bisim) (k₁ := k₁) hcont hk₂
  · intro e k₂ a b hcando hab
    have hF := Bisim.Bisim_isFixpoint (T := T) (α := α) (ε := ε) (ρ := ρ) a b hab
    have ⟨_, _, hvis_rl⟩ := hF
    have ⟨k₁, hk₁, hcont⟩ := hvis_rl e k₂ hcando
    have ⟨n, hvpb⟩ := CanDo.toVisPathBounded (T := T) (α := α) (ε := ε) (ρ := ρ)
      (b := a) (e := e) (k₂ := k₁) (R := flip Bisim) (k₁ := k₂) (fun i => hcont i) hk₁
    exact ⟨n, k₁, hvpb, hcont⟩
  · exact hbisim

theorem VisPathBounded.toCanDo
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {n : Nat} {e : ε} {R : T α ε ρ → T α ε ρ → Prop}
    {k₁ : α → T α ε ρ} {b : T α ε ρ} :
    VisPathBounded (T := T) n e R k₁ b →
    ∃ k₂, CanDo (T := T) b e k₂ ∧ ∀ i, R (k₁ i) (k₂ i) := by
  induction n generalizing b with
  | zero =>
      intro h
      simp only [VisPathBounded] at h
      obtain ⟨k₂, heq, hk⟩ := h
      exact ⟨k₂, heq ▸ .vis, hk⟩
  | succ n ih =>
      intro h
      simp only [VisPathBounded] at h
      rcases h with ⟨k₂, heq, hk⟩ | ⟨t, heq, hrec⟩
      · exact ⟨k₂, heq ▸ .vis, hk⟩
      · let ⟨k₂, hk₂, hcont⟩ := ih hrec
        exact ⟨k₂, heq ▸ .tau hk₂, hcont⟩

private theorem bound_decreases_ret_tau
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {n : Nat} {r : ρ} {b b' : T α ε ρ}
    (hb : b = tau b') (hn : RetPathBounded (T := T) (α := α) (ε := ε) (ρ := ρ) (n + 1) r b) :
    RetPathBounded (T := T) (α := α) (ε := ε) (ρ := ρ) n r b' := by
  simp only [RetPathBounded] at hn
  rcases hn with heq | ⟨t, heq, hrec⟩
  · exact False.elim (tau_ne_ret (T := T) (α := α) (ε := ε) (ρ := ρ) (t := b') (r := r)
      (hb.symm.trans heq))
  · exact (tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) (hb.symm.trans heq)) ▸ hrec

private theorem bound_decreases_vis_tau
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {n : Nat} {e : ε} {R : T α ε ρ → T α ε ρ → Prop}
    {k₁ : α → T α ε ρ} {b b' : T α ε ρ}
    (hb : b = tau b') (hn : VisPathBounded (T := T) (α := α) (ε := ε) (ρ := ρ) (n + 1) e R k₁ b) :
    VisPathBounded (T := T) (α := α) (ε := ε) (ρ := ρ) n e R k₁ b' := by
  simp only [VisPathBounded] at hn
  rcases hn with ⟨k₂, heq, hk⟩ | ⟨t, heq, hrec⟩
  · exact False.elim (tau_ne_vis (T := T) (α := α) (ε := ε) (ρ := ρ) (t := b') (e := e)
      (k := k₂) (hb.symm.trans heq))
  · exact (tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) (hb.symm.trans heq)) ▸ hrec

private theorem EquivUTT.F_cases_x
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {R : T α ε ρ → T α ε ρ → Prop}
    {P : Prop} {a y : T α ε ρ} (hF : F (T := T) (α := α) (ε := ε) (ρ := ρ) R a y)
    (hret : ∀ r, a = ret r → y = ret r → P)
    (hvis : ∀ e k₁ k₂, a = vis e k₁ → y = vis e k₂ → (∀ i, R (k₁ i) (k₂ i)) → P)
    (htau : ∀ x' y', a = tau x' → y = tau y' → R x' y' → P)
    (htaul : ∀ x', a = tau x' → R x' y → P)
    (htaur : ∀ y', y = tau y' → R a y' → P) : P := by
  cases hF with
  | ret => exact hret _ rfl rfl
  | vis hk => exact hvis _ _ _ rfl rfl hk
  | tau h => exact htau _ _ rfl rfl h
  | taul h => exact htaul _ rfl h
  | taur h => exact htaur _ rfl h

private theorem peel_taus_term_fwd
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {R : T α ε ρ → T α ε ρ → Prop}
    (isFixpoint : ∀ a b, R a b → F (T := T) (α := α) (ε := ε) (ρ := ρ) R a b)
    {t : T α ε ρ} {r : ρ}
    (ih : ∀ b, R t b → Terminates (T := T) b r)
    {n : Nat} {b : T α ε ρ}
    (hR : R (tau t) b)
    (hbound : RetPathBounded (T := T) (α := α) (ε := ε) (ρ := ρ) n r b) :
    Terminates (T := T) b r := by
  induction n generalizing b with
  | zero =>
      simp only [RetPathBounded] at hbound
      exact hbound ▸ .ret
  | succ n ih_n =>
      apply EquivUTT.F_cases_x (T := T) (α := α) (ε := ε) (ρ := ρ) (R := R) (a := tau t)
        (y := b) (hF := isFixpoint _ _ hR)
      · intro r ha _; exact False.elim (tau_ne_ret (T := T) (α := α) (ε := ε) (ρ := ρ)
        (by simpa using ha))
      · intro e k₁ k₂ ha _ _; exact False.elim (tau_ne_vis (T := T) (α := α) (ε := ε) (ρ := ρ)
        (by simpa using ha))
      · intro t' y' ha hb hR'
        have hx := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) ha
        exact hb ▸ .tau (ih y' (hx ▸ hR'))
      · intro t' ha hR'
        have hx := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) ha
        exact ih b (hx ▸ hR')
      · intro b' hb hRb'
        have hbound' := bound_decreases_ret_tau (T := T) (α := α) (ε := ε) (ρ := ρ) hb hbound
        exact hb ▸ .tau (ih_n hRb' hbound')

private theorem peel_taus_term_bwd
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {R : T α ε ρ → T α ε ρ → Prop}
    (isFixpoint : ∀ a b, R a b → F (T := T) (α := α) (ε := ε) (ρ := ρ) R a b)
    {t : T α ε ρ} {r : ρ}
    (ih : ∀ a, R a t → Terminates (T := T) a r)
    {n : Nat} {a : T α ε ρ}
    (hR : R a (tau t))
    (hbound : RetPathBounded (T := T) (α := α) (ε := ε) (ρ := ρ) n r a) :
    Terminates (T := T) a r := by
  induction n generalizing a with
  | zero =>
      simp only [RetPathBounded] at hbound
      exact hbound ▸ .ret
  | succ n ih_n =>
      apply EquivUTT.F_cases_x (T := T) (α := α) (ε := ε) (ρ := ρ) (R := R) (a := a)
        (y := tau t) (hF := isFixpoint _ _ hR)
      · intro r _ hb; exact False.elim (tau_ne_ret (T := T) (α := α) (ε := ε) (ρ := ρ)
        (by simpa using hb))
      · intro e k₁ k₂ _ hb _; exact False.elim (tau_ne_vis (T := T) (α := α) (ε := ε) (ρ := ρ)
        (by simpa using hb))
      · intro x' t' ha hb hR'
        have hy := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) hb
        exact ha ▸ .tau (ih x' (hy ▸ hR'))
      · intro a' ha hR'
        have hbound' := bound_decreases_ret_tau (T := T) (α := α) (ε := ε) (ρ := ρ) ha hbound
        exact ha ▸ .tau (ih_n hR' hbound')
      · intro t' hb hR'
        have hy := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) hb
        exact ih a (hy ▸ hR')

theorem EquivUTT.toBisim
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {t₁ t₂ : T α ε ρ} :
    EquivUTT (T := T) (α := α) (ε := ε) (ρ := ρ) t₁ t₂ →
    Bisim (T := T) (α := α) (ε := ε) (ρ := ρ) t₁ t₂ := by
  rintro ⟨R, isFixpoint, h_term_bounded, h_term_bounded', h_vis_bounded, h_vis_bounded',
    h_cando_bounded, h_cando_bounded', hR⟩
  refine ⟨R, ?_, hR⟩
  intro a b hab
  constructor
  · intro r
    constructor
    · intro ht
      induction ht generalizing b with
      | ret =>
          have ⟨n, hn⟩ := h_term_bounded _ _ b .ret hab
          exact RetPathBounded.toTerminates (T := T) (α := α) (ε := ε) (ρ := ρ) hn
      | tau ht ih =>
          apply EquivUTT.F_cases_x (T := T) (α := α) (ε := ε) (ρ := ρ) (R := R)
            (a := a) (y := b) (hF := isFixpoint _ _ hab)
          · intro r ha _; exact False.elim (tau_ne_ret (T := T) (α := α) (ε := ε) (ρ := ρ)
            (by simpa using ha))
          · intro e k₁ k₂ ha _ _; exact False.elim (tau_ne_vis (T := T) (α := α) (ε := ε) (ρ := ρ)
            (by simpa using ha))
          · intro x' y' ha hy hR'
            have hx := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) ha
            exact hy ▸ .tau (ih y' (hx ▸ hR'))
          · intro x' ha hR'
            have hx := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) ha
            exact ih b (hx ▸ hR')
          · intro b' hb hRb'
            apply EquivUTT.F_cases_x (T := T) (α := α) (ε := ε) (ρ := ρ) (R := R)
              (a := a) (y := b') (hF := isFixpoint _ _ hRb')
            · intro r ha' _
              exact False.elim (tau_ne_ret (T := T) (α := α) (ε := ε) (ρ := ρ)
                (by simpa using ha'))
            · intro e k₁ k₂ ha' _ _
              exact False.elim (tau_ne_vis (T := T) (α := α) (ε := ε) (ρ := ρ)
                (by simpa using ha'))
            · intro _ y'' ha' hb' hR''
              have hx := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) ha'
              exact hb ▸ .tau (hb' ▸ .tau (ih y'' (hx ▸ hR'')))
            · intro _ ha' hR''
              have hx := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) ha'
              exact hb ▸ .tau (ih b' (hx ▸ hR''))
            · intro b'' hb' hRb''
              have ⟨n, hn⟩ := h_term_bounded _ _ b'' (.tau ht) hRb''
              exact hb ▸ .tau (hb' ▸ .tau (RetPathBounded.toTerminates (T := T) (α := α) (ε := ε)
                (ρ := ρ) hn))
    · intro ht
      induction ht generalizing a with
      | ret =>
          have ⟨n, hn⟩ := h_term_bounded' a _ _ .ret hab
          exact RetPathBounded.toTerminates (T := T) (α := α) (ε := ε) (ρ := ρ) hn
      | tau ht ih =>
          apply EquivUTT.F_cases_x (T := T) (α := α) (ε := ε) (ρ := ρ) (R := R)
            (a := a) (y := b) (hF := isFixpoint _ _ hab)
          · intro r _ hb; exact False.elim (tau_ne_ret (T := T) (α := α) (ε := ε) (ρ := ρ)
            (by simpa using hb))
          · intro e k₁ k₂ _ hb _
            exact False.elim (tau_ne_vis (T := T) (α := α) (ε := ε) (ρ := ρ)
              (by simpa using hb))
          · intro x' y' hx hy hR'
            have heq := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) hy
            exact hx ▸ .tau (ih x' (heq ▸ hR'))
          · intro a' ha hR'
            apply EquivUTT.F_cases_x (T := T) (α := α) (ε := ε) (ρ := ρ) (R := R)
              (a := a') (y := b) (hF := isFixpoint _ _ hR')
            · intro r _ hb'
              exact False.elim (tau_ne_ret (T := T) (α := α) (ε := ε) (ρ := ρ)
                (by simpa using hb'))
            · intro e k₁ k₂ _ hb' _
              exact False.elim (tau_ne_vis (T := T) (α := α) (ε := ε) (ρ := ρ)
                (by simpa using hb'))
            · intro x'' _ ha' hb' hR''
              have hy := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) hb'
              exact ha ▸ .tau (ha' ▸ .tau (ih x'' (hy ▸ hR'')))
            · intro a'' ha' hR''
              have ⟨n, hn⟩ := h_term_bounded' a'' _ _ (.tau ht) hR''
              exact ha ▸ .tau (ha' ▸ .tau (RetPathBounded.toTerminates (T := T) (α := α) (ε := ε)
                (ρ := ρ) hn))
            · intro y' hb' hRy'
              have hy := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) hb'
              exact ha ▸ .tau (ih a' (hy ▸ hRy'))
          · intro y' hy hRy'
            have heq := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) hy
            exact ih a (heq ▸ hRy')
  constructor
  · intro e k₁ hc
    revert b
    induction hc with
    | vis =>
        intro b hab
        have ⟨n, hn⟩ := h_vis_bounded _ _ b hab
        exact VisPathBounded.toCanDo (T := T) (α := α) (ε := ε) (ρ := ρ) hn
    | tau hinner ih =>
        intro b hab
        apply EquivUTT.F_cases_x (T := T) (α := α) (ε := ε) (ρ := ρ) (R := R)
          (a := a) (y := b) (hF := isFixpoint _ _ hab)
        · intro r ha _; exact False.elim (tau_ne_ret (T := T) (α := α) (ε := ε) (ρ := ρ)
          (by simpa using ha))
        · intro e k₁ k₂ ha _ _; exact False.elim (tau_ne_vis (T := T) (α := α) (ε := ε) (ρ := ρ)
          (by simpa using ha))
        · intro x' y' ha hb hR'
          have hx := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) ha
          let ⟨k₂, hk₂, hcont⟩ := ih y' (hx ▸ hR')
          exact ⟨k₂, hb ▸ CanDo.tau hk₂, hcont⟩
        · intro x' ha hR'
          have hx := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) ha
          exact ih b (hx ▸ hR')
        · intro b' hb hRb'
          apply EquivUTT.F_cases_x (T := T) (α := α) (ε := ε) (ρ := ρ) (R := R)
            (a := a) (y := b') (hF := isFixpoint _ _ hRb')
          · intro r ha' _; exact False.elim (tau_ne_ret (T := T) (α := α) (ε := ε) (ρ := ρ)
            (by simpa using ha'))
          · intro e k₁ k₂ ha' _ _; exact False.elim (tau_ne_vis (T := T) (α := α) (ε := ε) (ρ := ρ)
            (by simpa using ha'))
          · intro x'' y'' ha' hb' hR''
            have hx := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) ha'
            let ⟨k₂, hk₂, hcont⟩ := ih y'' (hx ▸ hR'')
            exact ⟨k₂, hb ▸ CanDo.tau (hb' ▸ CanDo.tau hk₂), hcont⟩
          · intro x'' ha' hR''
            have hx := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) ha'
            let ⟨k₂, hk₂, hcont⟩ := ih b' (hx ▸ hR'')
            exact ⟨k₂, hb ▸ CanDo.tau hk₂, hcont⟩
          · intro b'' hb' hRb''
            have ⟨n, hn⟩ := h_cando_bounded _ _ _ b'' (CanDo.tau hinner) hRb''
            let ⟨k₂, hk₂, hcont⟩ := VisPathBounded.toCanDo (T := T) (α := α) (ε := ε)
              (ρ := ρ) hn
            exact ⟨k₂, hb ▸ CanDo.tau (hb' ▸ CanDo.tau hk₂), hcont⟩
  · intro e k₂ hc
    revert a
    induction hc with
    | vis =>
        intro a hab
        have ⟨n, _, hvp, hcont⟩ := h_vis_bounded' _ _ a hab
        let ⟨k₁', hk₁, hcont'⟩ := VisPathBounded.toCanDo (T := T) (α := α) (ε := ε)
          (ρ := ρ) hvp
        exact ⟨k₁', hk₁, hcont'⟩
    | tau hinner ih =>
        intro a hab
        apply EquivUTT.F_cases_x (T := T) (α := α) (ε := ε) (ρ := ρ) (R := R)
          (a := a) (y := b) (hF := isFixpoint _ _ hab)
        · intro r _ hb; exact False.elim (tau_ne_ret (T := T) (α := α) (ε := ε) (ρ := ρ)
          (by simpa using hb))
        · intro e k₁ k₂ _ hb _
          exact False.elim (tau_ne_vis (T := T) (α := α) (ε := ε) (ρ := ρ)
            (by simpa using hb))
        · intro x' y' ha hb hR'
          have hy := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) hb
          let ⟨k₁, hk₁, hcont⟩ := ih x' (hy ▸ hR')
          exact ⟨k₁, ha ▸ CanDo.tau hk₁, hcont⟩
        · intro a' ha hR'
          apply EquivUTT.F_cases_x (T := T) (α := α) (ε := ε) (ρ := ρ) (R := R)
            (a := a') (y := b) (hF := isFixpoint _ _ hR')
          · intro r _ hb'; exact False.elim (tau_ne_ret (T := T) (α := α) (ε := ε) (ρ := ρ)
            (by simpa using hb'))
          · intro e k₁ k₂ _ hb' _; exact False.elim (tau_ne_vis (T := T) (α := α) (ε := ε) (ρ := ρ)
            (by simpa using hb'))
          · intro x'' y'' ha' hb' hR''
            have hy := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) hb'
            let ⟨k₁, hk₁, hcont⟩ := ih x'' (hy ▸ hR'')
            exact ⟨k₁, ha ▸ CanDo.tau (ha' ▸ CanDo.tau hk₁), hcont⟩
          · intro a'' ha' hR''
            have ⟨n, k₁', hn, hcont⟩ := h_cando_bounded' _ _ a'' _ (CanDo.tau hinner) hR''
            let ⟨k₁'', hk₁, hcont'⟩ := VisPathBounded.toCanDo (T := T) (α := α) (ε := ε)
              (ρ := ρ) hn
            exact ⟨k₁'', ha ▸ CanDo.tau (ha' ▸ CanDo.tau hk₁), hcont'⟩
          · intro y'' hb' hRy''
            have hy := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) hb'
            let ⟨k₁, hk₁, hcont⟩ := ih a' (hy ▸ hRy'')
            exact ⟨k₁, ha ▸ CanDo.tau hk₁, hcont⟩
        · intro y' hy hRy'
          have heq := tau_inj (T := T) (α := α) (ε := ε) (ρ := ρ) hy
          exact ih a (heq ▸ hRy')

theorem Bisim.iff_EquivUTT
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocolWithCases T]
    {α ε ρ : Type} {t₁ t₂ : T α ε ρ} :
    Bisim (T := T) (α := α) (ε := ε) (ρ := ρ) t₁ t₂ ↔
    EquivUTT (T := T) (α := α) (ε := ε) (ρ := ρ) t₁ t₂ :=
  ⟨Bisim.toEquivUTT, EquivUTT.toBisim⟩

/-- Transitivity: EquivUTT x y → EquivUTT y z → EquivUTT x z. -/
theorem EquivUTT.trans
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocolWithCases T]
    {α ε ρ : Type} {x y z : T α ε ρ} :
    EquivUTT x y → EquivUTT y z → EquivUTT x z := by
  intro h1 h2
  exact Bisim.toEquivUTT (Bisim.trans (EquivUTT.toBisim h1) (EquivUTT.toBisim h2))

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
