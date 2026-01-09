import Qpf.Coinduction.Protocol

/-!
# EquivUTT (Abstract)

This module defines weak bisimulation (EquivUTT) and its supporting predicates
purely in terms of the abstract `CoinductiveTreeProtocol`. It mirrors the
statements from `Qpf/Problems/P1/R1_07_1897e3e4-1174-413e-adf1-8c51950d29da-output.lean`
without committing to any concrete coinductive representation.
-/-

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
  sorry

/-- If a tree can do an event, there is a bounded vis path. -/
theorem CanDo_implies_VisPathBounded
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} (t : T α ε ρ) (e : ε) (k : α → T α ε ρ)
    (h : CanDo (T := T) t e k) :
    ∃ n, VisPathBounded (T := T) n e Eq k t := by
  sorry

/-- Reflexivity: EquivUTT x x. -/
theorem EquivUTT.refl
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocolWithCases T]
    {α ε ρ : Type} (x : T α ε ρ) : EquivUTT (T := T) x x := by
  sorry

/-- Symmetry: EquivUTT x y → EquivUTT y x. -/
theorem EquivUTT.symm
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocolWithCases T]
    {α ε ρ : Type} {x y : T α ε ρ} :
    EquivUTT (T := T) x y → EquivUTT (T := T) y x := by
  sorry

/-- Transitivity: EquivUTT x y → EquivUTT y z → EquivUTT x z. -/
theorem EquivUTT.trans
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocolWithCases T]
    {α ε ρ : Type} {x y z : T α ε ρ} :
    EquivUTT (T := T) x y → EquivUTT (T := T) y z → EquivUTT (T := T) x z := by
  sorry

/-- Inversion lemma for `F` with `tau` on the left. -/
theorem F_tau_inv
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {R : T α ε ρ → T α ε ρ → Prop} {x c : T α ε ρ} :
    F (T := T) R (tau x) c →
    (∃ y, c = tau y ∧ R x y) ∨
    R x c ∨
    (∃ y, c = tau y ∧ F (T := T) R (tau x) y) := by
  sorry

/-- Inversion lemma for `F` with `ret` on the left. -/
theorem F_ret_inv
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {R : T α ε ρ → T α ε ρ → Prop} {r : ρ} {c : T α ε ρ} :
    F (T := T) R (ret r) c →
    c = ret r ∨ (∃ y, c = tau y ∧ F (T := T) R (ret r) y) := by
  sorry

/-- Inversion lemma for `F` with `vis` on the left. -/
theorem F_vis_inv
    {T : Type → Type → Type → Type} [CoinductiveTreeProtocol T]
    {α ε ρ : Type} {R : T α ε ρ → T α ε ρ → Prop}
    {e : ε} {k : α → T α ε ρ} {c : T α ε ρ} :
    F (T := T) R (vis e k) c →
    (∃ k', c = vis e k' ∧ ∀ i, R (k i) (k' i)) ∨
    (∃ y, c = tau y ∧ F (T := T) R (vis e k) y) := by
  sorry

end Coinduction
