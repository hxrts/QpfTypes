import Qpf
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.QPF.Multivariate.Constructions.Quot

open scoped MvFunctor

set_option pp.analyze true

abbrev List' : TypeFun 1 := TypeFun.ofCurried List

abbrev List'.perm ⦃Γ⦄ : List' Γ → List' Γ → Prop :=
  List.Perm

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

lemma unbox_map {Γ₁ Γ₂ : TypeVec 1} (f : Γ₁ ⟹ Γ₂) (x : MvQPF.List.QpfList' Γ₁) :
    MvQPF.List.unbox (MvFunctor.map f x) =
      List.map (f 0) (MvQPF.List.unbox x) := by
  rcases x with ⟨a, g⟩
  simp [MvQPF.List.unbox, MvPFunctor.map_eq, TypeVec.comp, vec_toList_map]

lemma unbox_box {Γ} (a : List' Γ) : MvQPF.List.unbox (MvQPF.List.box a) = a := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
      simp only [MvQPF.List.box, MvQPF.List.unbox, Vec.ofList, Vec.toList]
      congr

lemma list_map_eq {Γ₁ Γ₂ : TypeVec 1} (f : Γ₁ ⟹ Γ₂) (a : List' Γ₁) :
    f <$$> a = List.map (f 0) a := by
  -- Map for `List'` is defined via box/unbox
  dsimp [MvQPF.List.instMvFunctorList', MvFunctor.ofIsomorphism]
  calc
    MvQPF.List.unbox (MvFunctor.map f (MvQPF.List.box a)) =
        List.map (f 0) (MvQPF.List.unbox (MvQPF.List.box a)) := by
          simpa using (unbox_map (f := f) (x := MvQPF.List.box a))
    _ = List.map (f 0) a := by
          simp [unbox_box]

theorem perm_functorial :
    ∀ (Γ₁ Γ₂ : TypeVec 1) (a b : List' Γ₁) (f : Γ₁ ⟹ Γ₂),
      List'.perm a b → List'.perm (f <$$> a) (f <$$> b) := by
  intro Γ₁ Γ₂ a b f h
  -- Reduce to `List.map` and use `List.Perm.map`.
  simpa [list_map_eq] using (List.Perm.map (f := f 0) h)

noncomputable def MultiSet : TypeFun 1 :=
  MvQPF.Quot1 List'.perm

noncomputable instance : MvQPF MultiSet :=
  MvQPF.relQuot List'.perm perm_functorial
