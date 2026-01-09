import Qpf.Builtins.List
import Mathlib.Data.List.Perm.Basic

open scoped MvFunctor

namespace MvQPF
namespace List

/-!
# Permutation API for QPF lists

This module provides a small, public API for permutation lemmas on the QPF list
representation (both curried and uncurried), so downstream code doesn't need to
reach into `box`/`unbox` details.
-/

-- `TypeFun.ofCurried` reverses arguments, so `Vec.reverse Γ 0` is definitional `Γ 0`.
@[simp] lemma vec_reverse_fz {Γ : TypeVec 1} : Vec.reverse Γ 0 = Γ 0 := by
  rfl

instance {Γ} : Membership (Γ 0) (List' Γ) := by
  dsimp [List', TypeFun.ofCurried, TypeFun.ofCurriedAux, TypeFun.reverseArgs]
  simpa using (inferInstance : Membership (Γ 0) (List (Γ 0)))

/-!
## Helpers: map/box/unbox
-/

lemma vec_toList_map {α β} (f : α → β) : ∀ {n} (v : Vec α n),
    Vec.toList (fun i => f (v i)) = List.map f (Vec.toList v) := by
  intro n v
  induction n with
  | zero =>
      simp [Vec.toList]
  | succ n ih =>
      simp [Vec.toList, Vec.last]
      have h := ih (v := v.drop)
      simpa [Vec.drop] using h

lemma unbox_map {Γ₁ Γ₂ : TypeVec 1} (f : Γ₁ ⟹ Γ₂) (x : QpfList' Γ₁) :
    unbox (MvFunctor.map f x) =
      List.map (f 0) (unbox x) := by
  rcases x with ⟨a, g⟩
  simp [unbox, MvPFunctor.map_eq, TypeVec.comp, vec_toList_map]

lemma unbox_box {Γ} (a : List' Γ) : unbox (box a) = a := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
      simp only [box, unbox, Vec.ofList, Vec.toList]
      congr

lemma list_map_eq {Γ₁ Γ₂ : TypeVec 1} (f : Γ₁ ⟹ Γ₂) (a : List' Γ₁) :
    f <$$> a = List.map (f 0) a := by
  -- Map for `List'` is defined via box/unbox
  dsimp [instMvFunctorList', MvFunctor.ofIsomorphism]
  calc
    unbox (MvFunctor.map f (box a)) =
        List.map (f 0) (unbox (box a)) := by
          simpa using (unbox_map (f := f) (x := box a))
    _ = List.map (f 0) a := by
          simp [unbox_box]

/-!
## Permutation on QPF lists
-/

/-- Permutation on the uncurried QPF list representation. -/
abbrev perm {Γ} (x y : QpfList' Γ) : Prop :=
  List.Perm (unbox x) (unbox y)

/-- Permutation on the curried list representation. -/
abbrev permCurried ⦃Γ⦄ : List' Γ → List' Γ → Prop := List.Perm

theorem perm_equivalence (Γ : TypeVec 1) : Equivalence (@perm Γ) :=
  ⟨
    (by intro x; exact List.Perm.refl _),
    (by intro x y h; exact List.Perm.symm h),
    (by intro x y z h1 h2; exact List.Perm.trans h1 h2)
  ⟩

/-- Permutation is preserved by `MvFunctor.map` on QPF lists. -/
theorem perm_functorial :
    ∀ (Γ₁ Γ₂ : TypeVec 1) (f : Γ₁ ⟹ Γ₂) (a b : QpfList' Γ₁),
      perm a b → perm (MvFunctor.map f a) (MvFunctor.map f b) := by
  intro Γ₁ Γ₂ f a b h
  dsimp [perm] at h ⊢
  simpa [unbox_map] using (List.Perm.map (f := f 0) h)

/-- Permutation is functorial on the curried list representation. -/
theorem permCurried_functorial :
    ∀ (Γ₁ Γ₂ : TypeVec 1) (a b : List' Γ₁) (f : Γ₁ ⟹ Γ₂),
      permCurried a b → permCurried (f <$$> a) (f <$$> b) := by
  intro Γ₁ Γ₂ a b f h
  -- Reduce to `List.map` and use `List.Perm.map`.
  simpa [list_map_eq] using (List.Perm.map (f := f 0) h)

/-- Append-right preserves permutation (curried). -/
theorem permCurried_append_right {Γ} {as bs : List' Γ} (cs : List' Γ) :
    permCurried as bs → permCurried (List.append as cs) (List.append bs cs) := by
  intro h
  simpa using (List.Perm.append_right (t₁ := cs) h)

/-- Append-left preserves permutation (curried). -/
theorem permCurried_append_left {Γ} (as : List' Γ) {bs cs : List' Γ} :
    permCurried bs cs → permCurried (List.append as bs) (List.append as cs) := by
  intro h
  simpa using (List.Perm.append_left (l := as) h)

/-- Appending permuted lists yields permuted results (curried). -/
theorem permCurried_append {Γ} {as₁ as₂ bs₁ bs₂ : List' Γ} :
    permCurried as₁ as₂ → permCurried bs₁ bs₂ →
    permCurried (List.append as₁ bs₁) (List.append as₂ bs₂) := by
  intro h₁ h₂
  simpa using (List.Perm.append h₁ h₂)

/-- Reversing preserves permutation (curried). -/
theorem permCurried_reverse {Γ} {as bs : List' Γ} :
    permCurried as bs → permCurried as.reverse bs.reverse := by
  intro h
  exact (List.reverse_perm as).trans (h.trans (List.reverse_perm bs).symm)

/-- Permutation preserves membership (curried). -/
theorem permCurried_mem {Γ} {as bs : List' Γ} (h : permCurried as bs) (x : Γ 0) :
    x ∈ as ↔ x ∈ bs := h.mem_iff

end List
end MvQPF
