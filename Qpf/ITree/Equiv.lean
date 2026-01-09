import Qpf.ITree.Bisim
import Qpf.ITree.EquivUTT

/-!
# Equivalence of Bisim and EquivUTT

This module proves that the membership-based `Bisim` and the F-based `EquivUTT`
define the same relation on ITrees.

## Main results

- `Bisim.toEquivUTT`: Membership-based equivalence implies F-based equivalence
- `EquivUTT.toBisim`: F-based equivalence implies membership-based equivalence
- `Bisim.iff_EquivUTT`: The two relations are equivalent

## Key techniques

The proofs use ITree constructor injectivity/distinctness lemmas (`tau_inj`,
`tau_ne_ret`, etc.) derived via `dest` to avoid QPF quotient elimination issues.
The tau-peeling lemmas (`Bisim.tau_left`, `Bisim.tau_right`) allow stripping
taus from bisimulations, enabling construction of `EquivUTT.F` terms.

The boundedness conditions in EquivUTT ensure that tau chains are finite,
making the EquivUTT → Bisim direction provable.

## Completeness

The `EquivUTT.toBisim` proof is complete. All edge cases are handled by the
boundedness conditions in EquivUTT:
- `h_term_bounded` conditions handle nested tau chains for Terminates
- `h_cando_bounded` conditions handle nested tau chains for CanDo

The equivalence `Bisim ↔ EquivUTT` is fully proven.
-/

namespace ITree

/-! ## Bisim → EquivUTT direction

The key insight is to use the tau-peeling lemmas from Bisim.lean:
- `Bisim.tau_left : Bisim (.tau t) b → Bisim t b`
- `Bisim.tau_right : Bisim a (.tau t) → Bisim a t`

These let us strip taus when constructing `EquivUTT.F` terms. -/

/-- Bisim implies EquivUTT.

Uses tau-peeling lemmas to handle the tau cases. -/
theorem Bisim.toEquivUTT {t₁ t₂ : ITree α ε ρ} : Bisim t₁ t₂ → EquivUTT t₁ t₂ := by
  intro hbisim
  -- Use Bisim itself as the witness relation for EquivUTT
  apply EquivUTT.intro (R := Bisim)
  · -- h_fixpoint
    intro a b hab
    -- Need to show EquivUTT.F Bisim a b from Bisim a b
    -- We case on a using ITree.cases
    cases a with
    | tau t =>
      -- a = .tau t: use EquivUTT.F.taul with Bisim.tau_left
      exact .taul (Bisim.tau_left hab)
    | ret r =>
      -- a = .ret r: need to determine b's structure from termination
      have ⟨R, isFixpoint, hR⟩ := hab
      have ⟨hterm, _, _⟩ := isFixpoint _ _ hR
      -- Terminates (.ret r) r, so Terminates b r
      have hb_term : Terminates b r := (hterm r).mp .ret
      -- Induct on how b terminates to find its structure
      induction hb_term with
      | ret => exact .ret
      | tau _ ih =>
        -- b = .tau b', use taur and strip the tau from the bisim
        exact .taur (Bisim.tau_right hab)
    | vis e k =>
      -- a = .vis e k: need to determine b's structure from CanDo
      have ⟨R, isFixpoint, hR⟩ := hab
      have ⟨_, hvis_lr, _⟩ := isFixpoint _ _ hR
      -- CanDo (.vis e k) e k, so ∃ k₂, CanDo b e k₂
      have ⟨k₂, hk₂, hcont⟩ := hvis_lr e k .vis
      -- Induct on how b can do e to find its structure
      induction hk₂ with
      | vis =>
        -- b = .vis e k₂
        apply EquivUTT.F.vis
        intro i
        exact ⟨R, isFixpoint, hcont i⟩
      | tau _ ih =>
        -- b = .tau b', use taur and strip the tau from the bisim
        exact .taur (Bisim.tau_right hab)
  · -- h_term_bounded: Terminates a r → Bisim a b → ∃ n, RetPathBounded n r b
    intro a r b hterm hab
    have hF := Bisim.Bisim_isFixpoint _ _ hab
    have ⟨hterm_iff, _, _⟩ := hF
    have ht : Terminates b r := (hterm_iff r).mp hterm
    exact Terminates.toRetPathBounded ht
  · -- h_term_bounded': Terminates b r → Bisim a b → ∃ n, RetPathBounded n r a
    intro a r b hterm hab
    have hF := Bisim.Bisim_isFixpoint _ _ hab
    have ⟨hterm_iff, _, _⟩ := hF
    have ht : Terminates a r := (hterm_iff r).mpr hterm
    exact Terminates.toRetPathBounded ht
  · -- h_vis_bounded: Bisim (.vis e k₁) b → ∃ n, VisPathBounded n e Bisim k₁ b
    intro e k₁ b hab
    have hF := Bisim.Bisim_isFixpoint _ _ hab
    have ⟨_, hvis_lr, _⟩ := hF
    have ⟨k₂, hk₂, hcont⟩ := hvis_lr e k₁ .vis
    exact CanDo.toVisPathBounded hcont hk₂
  · -- h_vis_bounded': Bisim a (.vis e k₂) → ∃ n k₁, VisPathBounded n e (flip Bisim) k₂ a ∧ ∀ i, Bisim (k₁ i) (k₂ i)
    intro e k₂ a hab
    have hF := Bisim.Bisim_isFixpoint _ _ hab
    have ⟨_, _, hvis_rl⟩ := hF
    have ⟨k₁, hk₁, hcont⟩ := hvis_rl e k₂ .vis
    have ⟨n, hvpb⟩ := CanDo.toVisPathBounded (R := flip Bisim) (fun i => hcont i) hk₁
    exact ⟨n, k₁, hvpb, hcont⟩
  · -- h_cando_bounded: CanDo a e k₁ → Bisim a b → ∃ n, VisPathBounded n e Bisim k₁ b
    intro e k₁ a b hcando hab
    have hF := Bisim.Bisim_isFixpoint _ _ hab
    have ⟨_, hvis_lr, _⟩ := hF
    have ⟨k₂, hk₂, hcont⟩ := hvis_lr e k₁ hcando
    exact CanDo.toVisPathBounded hcont hk₂
  · -- h_cando_bounded': CanDo b e k₂ → Bisim a b → ∃ n k₁, VisPathBounded n e (flip Bisim) k₂ a ∧ ∀ i, Bisim (k₁ i) (k₂ i)
    intro e k₂ a b hcando hab
    have hF := Bisim.Bisim_isFixpoint _ _ hab
    have ⟨_, _, hvis_rl⟩ := hF
    have ⟨k₁, hk₁, hcont⟩ := hvis_rl e k₂ hcando
    have ⟨n, hvpb⟩ := CanDo.toVisPathBounded (R := flip Bisim) (fun i => hcont i) hk₁
    exact ⟨n, k₁, hvpb, hcont⟩
  · exact hbisim

/-! ## EquivUTT → Bisim direction

Since EquivUTT now includes boundedness conditions, this direction is
straightforward. The boundedness conditions directly provide the bounds
needed for termination and CanDo proofs. -/

/-- VisPathBounded implies CanDo with related continuations -/
theorem VisPathBounded.toCanDo {n : ℕ} {e : ε} {R : ITree α ε ρ → ITree α ε ρ → Prop}
    {k₁ : α → ITree α ε ρ} {b : ITree α ε ρ} :
    VisPathBounded n e R k₁ b → ∃ k₂, CanDo b e k₂ ∧ ∀ i, R (k₁ i) (k₂ i) := by
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

/-- The bound decreases when we peel a tau from the RHS of RetPathBounded -/
private theorem bound_decreases_ret_tau {n : ℕ} {r : ρ} {b b' : ITree α ε ρ}
    (hb : b = .tau b') (hn : RetPathBounded (n+1) r b) :
    RetPathBounded n r b' := by
  simp only [RetPathBounded] at hn
  rcases hn with heq | ⟨t, heq, hrec⟩
  · exact absurd (hb.symm.trans heq) tau_ne_ret
  · exact tau_inj (hb.symm.trans heq) ▸ hrec

/-- The bound decreases when we peel a tau from the RHS of VisPathBounded -/
private theorem bound_decreases_vis_tau {n : ℕ} {e : ε} {R : ITree α ε ρ → ITree α ε ρ → Prop}
    {k₁ : α → ITree α ε ρ} {b b' : ITree α ε ρ}
    (hb : b = .tau b') (hn : VisPathBounded (n+1) e R k₁ b) :
    VisPathBounded n e R k₁ b' := by
  simp only [VisPathBounded] at hn
  rcases hn with ⟨k₂, heq, hk⟩ | ⟨t, heq, hrec⟩
  · exact absurd (hb.symm.trans heq) tau_ne_vis
  · exact tau_inj (hb.symm.trans heq) ▸ hrec

/-- Helper: case analysis on EquivUTT.F with first argument abstracted -/
private theorem EquivUTT.F_cases_x {R : ITree α ε ρ → ITree α ε ρ → Prop}
    {P : Prop} {a y : ITree α ε ρ} (hF : EquivUTT.F R a y)
    (hret : ∀ r, a = .ret r → y = .ret r → P)
    (hvis : ∀ e k₁ k₂, a = .vis e k₁ → y = .vis e k₂ → (∀ i, R (k₁ i) (k₂ i)) → P)
    (htau : ∀ x' y', a = .tau x' → y = .tau y' → R x' y' → P)
    (htaul : ∀ x', a = .tau x' → R x' y → P)
    (htaur : ∀ y', y = .tau y' → R a y' → P) : P := by
  cases hF with
  | ret => exact hret _ rfl rfl
  | vis hk => exact hvis _ _ _ rfl rfl hk
  | tau h => exact htau _ _ rfl rfl h
  | taul h => exact htaul _ rfl h
  | taur h => exact htaur _ rfl h

/-- Given R (.tau t) b with a ret-path bound, peel taus until we can use the IH.

This helper handles the nested taur cases in EquivUTT.toBisim by using strong
induction on the bound. Each taur step decreases the bound, so we eventually
reach a tau or taul case where we can apply the induction hypothesis. -/
private theorem peel_taus_term_fwd
    {R : ITree α ε ρ → ITree α ε ρ → Prop}
    (isFixpoint : ∀ a b, R a b → EquivUTT.F R a b)
    {t : ITree α ε ρ} {r : ρ}
    (ih : ∀ b, R t b → Terminates b r)
    {n : ℕ} {b : ITree α ε ρ}
    (hR : R (.tau t) b)
    (hbound : RetPathBounded n r b) :
    Terminates b r := by
  induction n generalizing b with
  | zero =>
    simp only [RetPathBounded] at hbound
    exact hbound ▸ .ret
  | succ n ih_n =>
    apply EquivUTT.F_cases_x (isFixpoint _ _ hR)
    · intro _ ha _; exact absurd ha tau_ne_ret
    · intro _ _ _ ha _ _; exact absurd ha tau_ne_vis
    · intro t' y' ha hb hR'
      have hx := tau_inj ha
      exact hb ▸ .tau (ih y' (hx ▸ hR'))
    · intro t' ha hR'
      have hx := tau_inj ha
      exact ih b (hx ▸ hR')
    · intro b' hb hRb'
      have hbound' := bound_decreases_ret_tau hb hbound
      exact hb ▸ .tau (ih_n hRb' hbound')

/-- Symmetric version: peel taus from LHS to prove Terminates a r -/
private theorem peel_taus_term_bwd
    {R : ITree α ε ρ → ITree α ε ρ → Prop}
    (isFixpoint : ∀ a b, R a b → EquivUTT.F R a b)
    {t : ITree α ε ρ} {r : ρ}
    (ih : ∀ a, R a t → Terminates a r)
    {n : ℕ} {a : ITree α ε ρ}
    (hR : R a (.tau t))
    (hbound : RetPathBounded n r a) :
    Terminates a r := by
  induction n generalizing a with
  | zero =>
    simp only [RetPathBounded] at hbound
    exact hbound ▸ .ret
  | succ n ih_n =>
    apply EquivUTT.F_cases_x (isFixpoint _ _ hR)
    · intro _ _ hb; exact absurd hb tau_ne_ret
    · intro _ _ _ _ hb _; exact absurd hb tau_ne_vis
    · intro x' t' ha hb hR'
      have hy := tau_inj hb
      exact ha ▸ .tau (ih x' (hy ▸ hR'))
    · intro a' ha hR'
      have hbound' := bound_decreases_ret_tau ha hbound
      exact ha ▸ .tau (ih_n hR' hbound')
    · intro t' hb hR'
      have hy := tau_inj hb
      exact ih a (hy ▸ hR')

/-- Given R (.tau (.ret r)) b with a known RetPathBound on b, find the actual bound.

This helper uses strong induction on the bound. In the taur case, the bound decreases
because each taur peels one tau from b. -/
private theorem find_ret_bound_aux
    {R : ITree α ε ρ → ITree α ε ρ → Prop}
    (isFixpoint : ∀ a b, R a b → EquivUTT.F R a b)
    (h_ret_bounded : ∀ r b, R (.ret r) b → ∃ n, RetPathBounded n r b)
    {r : ρ} {n : ℕ} {b : ITree α ε ρ}
    (hR : R (.tau (.ret r)) b)
    (hbound : RetPathBounded n r b) :
    ∃ m, RetPathBounded m r b := by
  induction n generalizing b with
  | zero =>
    -- b = .ret r by bound
    simp only [RetPathBounded] at hbound
    exact ⟨0, hbound⟩
  | succ n ih =>
    apply EquivUTT.F_cases_x (isFixpoint _ _ hR)
    · intro _ ha _; exact absurd ha tau_ne_ret
    · intro _ _ _ ha _ _; exact absurd ha tau_ne_vis
    · intro t' b' ha hb hR'
      -- tau: R t' b' where .tau (.ret r) = .tau t', so t' = .ret r
      have heq : t' = .ret r := (tau_inj ha).symm
      have ⟨m, hm⟩ := h_ret_bounded r b' (heq ▸ hR')
      exact ⟨m + 1, .inr ⟨b', hb, hm⟩⟩
    · intro t' ha hR'
      -- taul: R t' b where t' = .ret r
      have heq : t' = .ret r := (tau_inj ha).symm
      exact h_ret_bounded r b (heq ▸ hR')
    · intro b' hb hRb'
      -- taur: R (.tau (.ret r)) b' where b = .tau b'
      -- The bound on b' is one less since b = .tau b'
      have hbound' := bound_decreases_ret_tau hb hbound
      have ⟨m, hm⟩ := ih hRb' hbound'
      exact ⟨m + 1, .inr ⟨b', hb, hm⟩⟩

/-- Given R (.tau t) b with an ih that handles R t _, prove Terminates b r.

This uses strong induction on an explicit bound. In the taur case, the bound
decreases because b = .tau b'. In tau/taul cases, ih applies directly.

This helper is used to eliminate the nested taur cases in EquivUTT.toBisim. -/
private theorem terminates_from_tau_with_bound
    {R : ITree α ε ρ → ITree α ε ρ → Prop}
    (isFixpoint : ∀ a b, R a b → EquivUTT.F R a b)
    {t : ITree α ε ρ} {r : ρ}
    (ih : ∀ b, R t b → Terminates b r)
    {n : ℕ} {b : ITree α ε ρ}
    (hR : R (.tau t) b)
    (hbound : RetPathBounded n r b) :
    Terminates b r := by
  induction n generalizing b with
  | zero =>
    simp only [RetPathBounded] at hbound
    exact hbound ▸ .ret
  | succ n ih_n =>
    apply EquivUTT.F_cases_x (isFixpoint _ _ hR)
    · intro _ ha _; exact absurd ha tau_ne_ret
    · intro _ _ _ ha _ _; exact absurd ha tau_ne_vis
    · intro t' b' ha hb hR'
      have heq : t' = t := (tau_inj ha).symm
      exact hb ▸ .tau (ih b' (heq ▸ hR'))
    · intro t' ha hR'
      have heq : t' = t := (tau_inj ha).symm
      exact ih b (heq ▸ hR')
    · intro b' hb hRb'
      have hbound' := bound_decreases_ret_tau hb hbound
      exact hb ▸ .tau (ih_n hRb' hbound')

/-- Symmetric: prove Terminates a r from R a (.tau t) with bound on a -/
private theorem terminates_from_tau_with_bound'
    {R : ITree α ε ρ → ITree α ε ρ → Prop}
    (isFixpoint : ∀ a b, R a b → EquivUTT.F R a b)
    {t : ITree α ε ρ} {r : ρ}
    (ih : ∀ a, R a t → Terminates a r)
    {n : ℕ} {a : ITree α ε ρ}
    (hR : R a (.tau t))
    (hbound : RetPathBounded n r a) :
    Terminates a r := by
  induction n generalizing a with
  | zero =>
    simp only [RetPathBounded] at hbound
    exact hbound ▸ .ret
  | succ n ih_n =>
    apply EquivUTT.F_cases_x (isFixpoint _ _ hR)
    · intro _ _ hb; exact absurd hb tau_ne_ret
    · intro _ _ _ _ hb _; exact absurd hb tau_ne_vis
    · intro a' t' ha hb hR'
      have heq : t' = t := (tau_inj hb).symm
      exact ha ▸ .tau (ih a' (heq ▸ hR'))
    · intro a' ha hR'
      have hbound' := bound_decreases_ret_tau ha hbound
      exact ha ▸ .tau (ih_n hR' hbound')
    · intro t' hb hR'
      have heq : t' = t := (tau_inj hb).symm
      exact ih a (heq ▸ hR')

/-- EquivUTT implies Bisim.

The proof uses the boundedness conditions from EquivUTT to show that
termination and CanDo behaviors are preserved. -/
theorem EquivUTT.toBisim {t₁ t₂ : ITree α ε ρ} : EquivUTT t₁ t₂ → Bisim t₁ t₂ := by
  rintro ⟨R, isFixpoint, h_term_bounded, h_term_bounded', h_vis_bounded, h_vis_bounded',
         h_cando_bounded, h_cando_bounded', hR⟩
  -- Use R as the witness relation for Bisim
  refine ⟨R, ?_, hR⟩
  -- Need to show R is a post-fixpoint of Bisim.F
  intro a b hab
  constructor
  -- Termination: ∀ r, Terminates a r ↔ Terminates b r
  · intro r
    constructor
    · -- Forward: Terminates a r → Terminates b r
      intro ht
      induction ht generalizing b with
      | ret =>
        -- a = .ret r, use h_term_bounded with Terminates.ret
        have ⟨n, hn⟩ := h_term_bounded _ _ b .ret hab
        exact RetPathBounded.toTerminates hn
      | tau ht ih =>
        -- a = .tau t, ht : Terminates t r, ih : ∀ b, R t b → Terminates b r
        apply EquivUTT.F_cases_x (isFixpoint _ _ hab)
        · intro _ ha _
          exact absurd ha tau_ne_ret
        · intro _ _ _ ha _ _
          exact absurd ha tau_ne_vis
        · intro x' y' ha hy hR'
          have hx := tau_inj ha
          exact hy ▸ .tau (ih y' (hx ▸ hR'))
        · intro x' ha hR'
          have hx := tau_inj ha
          exact ih b (hx ▸ hR')
        · intro b' hb hRb'
          -- hRb' : R a b' where a = .tau t, need to peel tau
          apply EquivUTT.F_cases_x (isFixpoint _ _ hRb')
          · intro _ ha' _
            exact absurd ha' tau_ne_ret
          · intro _ _ _ ha' _ _
            exact absurd ha' tau_ne_vis
          · intro _ y'' ha' hb' hR''
            have hx := tau_inj ha'
            exact hb ▸ .tau (hb' ▸ .tau (ih y'' (hx ▸ hR'')))
          · intro _ ha' hR''
            have hx := tau_inj ha'
            exact hb ▸ .tau (ih b' (hx ▸ hR''))
          · intro b'' hb' hRb''
            -- Nested taur: R (.tau t) b'', need Terminates b'' r
            -- Use h_term_bounded with Terminates (.tau t) r = .tau ht
            have ⟨n, hn⟩ := h_term_bounded _ _ b'' (.tau ht) hRb''
            exact hb ▸ .tau (hb' ▸ .tau (RetPathBounded.toTerminates hn))
    · -- Backward: Terminates b r → Terminates a r
      intro ht
      induction ht generalizing a with
      | ret =>
        -- b = .ret r, use h_term_bounded' with Terminates.ret
        have ⟨n, hn⟩ := h_term_bounded' a _ _ .ret hab
        exact RetPathBounded.toTerminates hn
      | tau ht ih =>
        -- b = .tau t, ht : Terminates t r, ih : ∀ a, R a t → Terminates a r
        apply EquivUTT.F_cases_x (isFixpoint _ _ hab)
        · intro _ _ hb
          exact absurd hb tau_ne_ret
        · intro _ _ _ _ hb _
          exact absurd hb tau_ne_vis
        · intro x' y' hx hy hR'
          have heq := tau_inj hy
          exact hx ▸ .tau (ih x' (heq ▸ hR'))
        · intro a' ha hR'
          -- hR' : R a' b where b = .tau t, need to peel tau
          apply EquivUTT.F_cases_x (isFixpoint _ _ hR')
          · intro _ _ hb'
            exact absurd hb' tau_ne_ret
          · intro _ _ _ _ hb' _
            exact absurd hb' tau_ne_vis
          · intro x'' _ ha' hb' hR''
            have hy := tau_inj hb'
            exact ha ▸ .tau (ha' ▸ .tau (ih x'' (hy ▸ hR'')))
          · intro a'' ha' hR''
            -- Nested taul: R a'' (.tau t), need Terminates a'' r
            -- Use h_term_bounded' with Terminates (.tau t) r = .tau ht
            have ⟨n, hn⟩ := h_term_bounded' a'' _ _ (.tau ht) hR''
            exact ha ▸ .tau (ha' ▸ .tau (RetPathBounded.toTerminates hn))
          · intro y' hb' hRy'
            have hy := tau_inj hb'
            exact ha ▸ .tau (ih a' (hy ▸ hRy'))
        · intro y' hy hRy'
          have heq := tau_inj hy
          exact ih a (heq ▸ hRy')
  constructor
  -- CanDo left-to-right
  · intro e k₁ hc
    revert b
    induction hc with
    | vis =>
      intro b hab
      -- a = .vis e k₁, use h_vis_bounded
      have ⟨n, hn⟩ := h_vis_bounded _ _ b hab
      exact VisPathBounded.toCanDo hn
    | tau hinner ih =>
      -- a = .tau t, hinner : CanDo t e k₁
      intro b hab
      apply EquivUTT.F_cases_x (isFixpoint _ _ hab)
      · intro _ ha _
        exact absurd ha tau_ne_ret
      · intro _ _ _ ha _ _
        exact absurd ha tau_ne_vis
      · intro x' y' ha hb hR'
        have hx := tau_inj ha
        let ⟨k₂, hk₂, hcont⟩ := ih y' (hx ▸ hR')
        exact ⟨k₂, hb ▸ CanDo.tau hk₂, hcont⟩
      · intro x' ha hR'
        have hx := tau_inj ha
        exact ih b (hx ▸ hR')
      · intro b' hb hRb'
        -- hRb' : R a b' where a = .tau t, so R (.tau t) b'
        -- Need to peel the tau from a to use ih
        -- Apply F_cases_x again to peel the tau
        apply EquivUTT.F_cases_x (isFixpoint _ _ hRb')
        · intro _ ha' _
          exact absurd ha' tau_ne_ret
        · intro _ _ _ ha' _ _
          exact absurd ha' tau_ne_vis
        · intro x'' y'' ha' hb' hR''
          have hx := tau_inj ha'
          let ⟨k₂, hk₂, hcont⟩ := ih y'' (hx ▸ hR'')
          exact ⟨k₂, hb ▸ CanDo.tau (hb' ▸ CanDo.tau hk₂), hcont⟩
        · intro x'' ha' hR''
          have hx := tau_inj ha'
          let ⟨k₂, hk₂, hcont⟩ := ih b' (hx ▸ hR'')
          exact ⟨k₂, hb ▸ CanDo.tau hk₂, hcont⟩
        · intro b'' hb' hRb''
          -- Nested taur: R (.tau _) b''
          -- Use h_cando_bounded with .tau hinner
          have ⟨n, hn⟩ := h_cando_bounded _ _ _ b'' (CanDo.tau hinner) hRb''
          let ⟨k₂, hk₂, hcont⟩ := VisPathBounded.toCanDo hn
          exact ⟨k₂, hb ▸ CanDo.tau (hb' ▸ CanDo.tau hk₂), hcont⟩
  -- CanDo right-to-left
  · intro e k₂ hc
    revert a
    induction hc with
    | vis =>
      intro a hab
      -- b = .vis e k₂, use h_vis_bounded'
      have ⟨n, _, hvp, hcont⟩ := h_vis_bounded' _ _ a hab
      let ⟨k₁', hk₁, hcont'⟩ := VisPathBounded.toCanDo hvp
      -- hcont' : ∀ i, (flip R) (k₂ i) (k₁' i) = ∀ i, R (k₁' i) (k₂ i)
      exact ⟨k₁', hk₁, hcont'⟩
    | tau hinner ih =>
      -- b = .tau t, hinner : CanDo t e k₂
      intro a hab
      apply EquivUTT.F_cases_x (isFixpoint _ _ hab)
      · intro _ _ hb
        exact absurd hb tau_ne_ret
      · intro _ _ _ _ hb _
        exact absurd hb tau_ne_vis
      · intro x' y' ha hb hR'
        have hy := tau_inj hb
        let ⟨k₁, hk₁, hcont⟩ := ih x' (hy ▸ hR')
        exact ⟨k₁, ha ▸ CanDo.tau hk₁, hcont⟩
      · intro a' ha hR'
        -- hR' : R a' b where b = .tau t, so R a' (.tau t)
        -- Need to peel the tau from b to use ih
        apply EquivUTT.F_cases_x (isFixpoint _ _ hR')
        · intro _ _ hb'
          exact absurd hb' tau_ne_ret
        · intro _ _ _ _ hb' _
          exact absurd hb' tau_ne_vis
        · intro x'' y'' ha' hb' hR''
          have hy := tau_inj hb'
          let ⟨k₁, hk₁, hcont⟩ := ih x'' (hy ▸ hR'')
          exact ⟨k₁, ha ▸ CanDo.tau (ha' ▸ CanDo.tau hk₁), hcont⟩
        · intro a'' ha' hR''
          -- Nested taul: R a'' (.tau _)
          -- Use h_cando_bounded' with .tau hinner
          have ⟨n, k₁', hn, hcont⟩ := h_cando_bounded' _ _ a'' _ (CanDo.tau hinner) hR''
          let ⟨k₁'', hk₁, hcont'⟩ := VisPathBounded.toCanDo hn
          exact ⟨k₁'', ha ▸ CanDo.tau (ha' ▸ CanDo.tau hk₁), hcont'⟩
        · intro y'' hb' hRy''
          have hy := tau_inj hb'
          let ⟨k₁, hk₁, hcont⟩ := ih a' (hy ▸ hRy'')
          exact ⟨k₁, ha ▸ CanDo.tau hk₁, hcont⟩
      · intro y' hy hRy'
        have heq := tau_inj hy
        exact ih a (heq ▸ hRy')

/-- Bisim and EquivUTT are equivalent relations. -/
theorem Bisim.iff_EquivUTT {t₁ t₂ : ITree α ε ρ} : Bisim t₁ t₂ ↔ EquivUTT t₁ t₂ :=
  ⟨Bisim.toEquivUTT, EquivUTT.toBisim⟩

/-- Transitivity for EquivUTT via the Bisim detour.

This provides a transitivity proof by routing through the
membership-based `Bisim` formulation, which has a direct transitivity proof.
The equivalence `Bisim ↔ EquivUTT` lets us convert back and forth.

Use this if you stay in the concrete `Qpf.ITree.EquivUTT` development. -/
theorem EquivUTT.trans' {x y z : ITree α ε ρ} :
    EquivUTT x y → EquivUTT y z → EquivUTT x z :=
  fun h1 h2 => Bisim.toEquivUTT (Bisim.trans (EquivUTT.toBisim h1) (EquivUTT.toBisim h2))

end ITree
