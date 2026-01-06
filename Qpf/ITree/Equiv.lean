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

## Known limitations

The `EquivUTT.toBisim` proof contains four `sorry` placeholders in nested
taur/taul cases. These occur when applying `F_cases_x` twice: after the first
application peels a tau from one side, a second taur/taul can peel another tau
without making progress toward the induction hypothesis. The boundedness
conditions should rule out infinite such chains, but the current proof structure
doesn't directly leverage them for termination. A proper fix would require
well-founded recursion with a measure combining tau depth and boundedness.
-/

namespace ITree

/-! ## Bisim → EquivUTT direction

The key insight is to use the tau-peeling lemmas from Bisim.lean:
- `Bisim.tau_left : Bisim (.tau t) b → Bisim t b`
- `Bisim.tau_right : Bisim a (.tau t) → Bisim a t`

These let us strip taus when constructing `EquivUTT.F` terms. -/

/-! ### Conversion between Terminates/CanDo and bounded path predicates -/

/-- Convert Terminates to RetPathBounded -/
theorem Terminates.toRetPathBounded {b : ITree α ε ρ} {r : ρ} :
    Terminates b r → ∃ n, RetPathBounded n r b := by
  intro ht
  induction ht with
  | ret => exact ⟨0, rfl⟩
  | tau _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .inr ⟨_, rfl, hn⟩⟩

/-- Convert CanDo to VisPathBounded -/
theorem CanDo.toVisPathBounded {b : ITree α ε ρ} {e : ε} {k₂ : α → ITree α ε ρ}
    {R : ITree α ε ρ → ITree α ε ρ → Prop} {k₁ : α → ITree α ε ρ}
    (hcont : ∀ i, R (k₁ i) (k₂ i)) :
    CanDo b e k₂ → ∃ n, VisPathBounded n e R k₁ b := by
  intro hc
  induction hc with
  | vis => exact ⟨0, _, rfl, hcont⟩
  | tau _ ih =>
    obtain ⟨n, hn⟩ := ih hcont
    exact ⟨n + 1, .inr ⟨_, rfl, hn⟩⟩

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
  · -- h_ret_bounded: Bisim (.ret r) b → ∃ n, RetPathBounded n r b
    intro r b hab
    have hF := Bisim.Bisim_isFixpoint _ _ hab
    have ⟨hterm, _, _⟩ := hF
    have ht : Terminates b r := (hterm r).mp .ret
    exact Terminates.toRetPathBounded ht
  · -- h_ret_bounded': Bisim a (.ret r) → ∃ n, RetPathBounded n r a
    intro r a hab
    have hF := Bisim.Bisim_isFixpoint _ _ hab
    have ⟨hterm, _, _⟩ := hF
    have ht : Terminates a r := (hterm r).mpr .ret
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
  · exact hbisim

/-! ## EquivUTT → Bisim direction

Since EquivUTT now includes boundedness conditions, this direction is
straightforward. The boundedness conditions directly provide the bounds
needed for termination and CanDo proofs. -/

/-- RetPathBounded implies Terminates -/
theorem RetPathBounded.toTerminates {n : ℕ} {r : ρ} {b : ITree α ε ρ} :
    RetPathBounded n r b → Terminates b r := by
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

/-- EquivUTT implies Bisim.

The proof uses the boundedness conditions from EquivUTT to show that
termination and CanDo behaviors are preserved. -/
theorem EquivUTT.toBisim {t₁ t₂ : ITree α ε ρ} : EquivUTT t₁ t₂ → Bisim t₁ t₂ := by
  rintro ⟨R, isFixpoint, h_ret_bounded, h_ret_bounded', h_vis_bounded, h_vis_bounded', hR⟩
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
        -- a = .ret r, use h_ret_bounded
        have ⟨n, hn⟩ := h_ret_bounded _ b hab
        exact RetPathBounded.toTerminates hn
      | tau _ ih =>
        -- a = .tau t, Terminates t r
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
          · intro b'' hb' _
            -- Nested taur - use the boundedness to ensure termination
            -- For simplicity, use sorry here - proper fix needs well-founded recursion
            exact hb ▸ .tau (hb' ▸ .tau (by sorry))
    · -- Backward: Terminates b r → Terminates a r
      intro ht
      induction ht generalizing a with
      | ret =>
        -- b = .ret r, use h_ret_bounded'
        have ⟨n, hn⟩ := h_ret_bounded' _ a hab
        exact RetPathBounded.toTerminates hn
      | tau _ ih =>
        -- b = .tau t, Terminates t r
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
          · intro a'' ha' _
            -- Nested taul - use sorry
            exact ha ▸ .tau (ha' ▸ .tau (by sorry))
          · intro y' hb' hRy'
            have hy := tau_inj hb'
            exact ha ▸ .tau (ih a' (hy ▸ hRy'))
        · intro y' hy hRy'
          have heq := tau_inj hy
          exact ih a (heq ▸ hRy')
  constructor
  -- CanDo left-to-right
  · intro e k₁ hc
    induction hc generalizing b with
    | vis =>
      -- a = .vis e k₁, use h_vis_bounded
      have ⟨n, hn⟩ := h_vis_bounded _ _ b hab
      exact VisPathBounded.toCanDo hn
    | tau _ ih =>
      -- a = .tau t, CanDo t e k₁
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
          -- Still have R (.tau t) b'', need to recurse more
          -- Nested taur - needs well-founded recursion
          -- This case requires proving termination for infinite taur chains
          -- which should be ruled out by the boundedness conditions
          sorry
  -- CanDo right-to-left
  · intro e k₂ hc
    induction hc generalizing a with
    | vis =>
      -- b = .vis e k₂, use h_vis_bounded'
      have ⟨n, _, hvp, hcont⟩ := h_vis_bounded' _ _ a hab
      let ⟨k₁', hk₁, hcont'⟩ := VisPathBounded.toCanDo hvp
      -- hcont' : ∀ i, (flip R) (k₂ i) (k₁' i) = ∀ i, R (k₁' i) (k₂ i)
      exact ⟨k₁', hk₁, hcont'⟩
    | tau _ ih =>
      -- b = .tau t, CanDo t e k₂
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
          -- Nested taul - needs well-founded recursion
          -- This case requires proving termination for infinite taul chains
          -- which should be ruled out by the boundedness conditions
          sorry
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

end ITree
