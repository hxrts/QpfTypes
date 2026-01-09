import Qpf.Builtins.List
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.QPF.Multivariate.Constructions.Quot

open scoped MvFunctor

namespace MvQPF
namespace List

/-!
# Multiset as a Quotient of QPF List

This module ports the permutation-based multiset construction to the real QPF
list representation and its functor map.
-/

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

/-!
## Multiset as a quotient
-/

noncomputable def Multiset : TypeFun 1 :=
  MvQPF.Quot1 permCurried

noncomputable instance : MvQPF Multiset :=
  MvQPF.relQuot permCurried permCurried_functorial

end List
end MvQPF
