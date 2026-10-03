/-
Copyright (c) 2026 The contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# N0: Reductions for the coherence of one-relator groups

This file sets up the vocabulary of the `ORReductions` chapter:
* `FreeGroup.gens`: the finite set of free generators occurring in a word;
* `Group.FGOneRelator`: the class of finitely generated one-relator groups;
* `Subgroup.leftCosetSetoid`: the equivalence relation whose classes are the *left* cosets
  `gH` of a subgroup (used to decompose a group algebra over a subgroup algebra).

Main references: Jaikin-Zapirain--Linton, *On the coherence of one-relator groups and their group
algebras*, Annals of Math. 201 (2025).
-/
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.Ideal
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import ChallengeDeps

set_option autoImplicit false

open OnCoherenceOfOneRelatorGroups

/-! ### Vocabulary -/

/-- A group is *finitely generated one-relator* if it is the quotient of a free group on
`Fin n` by the normal closure of a single element. -/
def Group.FGOneRelator (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (r : FreeGroup (Fin n)), Nonempty (PresentedGroup {r} ≃* G)

namespace FreeGroup

variable {α : Type*}

/-- The set of free generators occurring in (the reduced word representing) `x`.
This is a *finite* set, but we only need it as a `Set`. -/
noncomputable def gens (x : FreeGroup α) : Set α :=
  letI : DecidableEq α := Classical.decEq α
  {a : α | List.Sublist [(a, true)] x.toWord ∨ List.Sublist [(a, false)] x.toWord}


end FreeGroup

namespace Subgroup

variable {G : Type*} [Group G]

/-- The equivalence relation on `G` whose classes are the left cosets `gH = {g * h | h ∈ H}`. -/
def leftCosetSetoid (H : Subgroup G) : Setoid G where
  r g g' := g⁻¹ * g' ∈ H
  iseqv := by
    constructor
    · intro g; simpa using H.one_mem
    · intro g g' h; simpa [inv_mul_eq_iff_eq_mul] using H.inv_mem h
    · intro g g' g'' h h'; simpa [mul_assoc] using H.mul_mem h h'

@[simp]
theorem leftCosetSetoid_r {H : Subgroup G} {g g' : G} :
    (leftCosetSetoid H).r g g' ↔ g⁻¹ * g' ∈ H := Iff.rfl

end Subgroup
