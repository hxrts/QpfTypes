import Mathlib.Data.QPF.Multivariate.Basic

/-!
# Cardinality-annotated polynomial functors

This module introduces a `Card` index to distinguish finite from infinite child
families in polynomial functors. Finite families are encoded by their cardinality
(`Fin n`), enabling vector-style pattern matching.
-/

universe u

/-- A cardinality descriptor for child positions. -/
inductive Card where
  | fin : Nat → Card
  | infinite : Type u → Card

namespace Card

/-- Interpret a `Card` as a type of positions. -/
def toType : Card.{u} → Type u
  | fin n => ULift (Fin n)
  | infinite α => α

end Card

/-- A cardinality-vector indexed by `Fin2 n`. -/
abbrev CardVec (n : Nat) : Type (u + 1) := Fin2 n → Card.{u}

namespace CardVec

/-- Interpret a `CardVec` as a `TypeVec`. -/
def toTypeVec (c : CardVec n) : TypeVec.{u} n := fun i => (c i).toType

end CardVec

/-- Multivariate polynomial functor with cardinality-annotated children. -/
structure MvPFunctorCard (n : Nat) where
  /-- The head type. -/
  A : Type u
  /-- The child family, recorded as cardinalities per parameter. -/
  B : A → CardVec.{u} n

namespace MvPFunctorCard

/-- Forgetful map to the usual `MvPFunctor`. -/
def toMvPFunctor (P : MvPFunctorCard.{u} n) : MvPFunctor.{u} n where
  A := P.A
  B := fun a i => (P.B a i).toType

instance : Coe (MvPFunctorCard.{u} n) (MvPFunctor.{u} n) where
  coe := toMvPFunctor

end MvPFunctorCard
