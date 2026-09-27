import Mathlib
import Submission.Work.EKLContract.Defs

/-!
# Every subset of a second-countable space has a countable dense subset

This file proves `Work.EKLC6Core.countable_dense_subgroup`: every subgroup `U ≤ SL₃(ℝ)` carries a
countable subset `D ⊆ U` which is dense in `U` for the subspace topology.

The mathematical content is the standard fact that *second countability is hereditary* (`Subtype.secondCountableTopology`)
and that a second-countable space is separable (`TopologicalSpace.SecondCountableTopology.to_separableSpace`),
applied to the subtype `↥U`.  All of the space-specific work is to record that the topology that
`Matrix.SpecialLinearGroup` carries is the subspace topology induced from the matrix space, so that
second countability of `SL₃(ℝ)` can be deduced from second countability of `Matrix (Fin 3) (Fin 3) ℝ`
(which is the product topology on a finite product of copies of `ℝ`).
-/

open Topology

namespace Work.EKLC6Core

/-- A subset of a second-countable space has a countable dense subset.  Concretely: there is a
countable `D ⊆ U` meeting every open set which meets `U`. -/
theorem exists_countable_dense_subset_of_secondCountable
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X] (U : Set X) :
    ∃ D : Set X, D.Countable ∧ D ⊆ U ∧
      ∀ O : Set X, IsOpen O → (O ∩ U).Nonempty → (O ∩ D).Nonempty := by
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense ↥U
  refine ⟨(fun g : ↥U => (g : X)) '' s, hsc.image _, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · intro O hO hne
    obtain ⟨x, hxO, hxU⟩ := hne
    have hO' : IsOpen {y : ↥U | (y : X) ∈ O} := hO.preimage continuous_subtype_val
    have hne' : {y : ↥U | (y : X) ∈ O}.Nonempty := ⟨⟨x, hxU⟩, hxO⟩
    obtain ⟨y, hys, hyO⟩ := hsd.exists_mem_open hO' hne'
    exact ⟨(y : X), hyO, y, hys, rfl⟩

/-- `SL₃(ℝ)` is second countable: its topology is the subspace topology coming from the finite
product `Matrix (Fin 3) (Fin 3) ℝ ≅ (Fin 3 → Fin 3 → ℝ)`. -/
theorem secondCountableTopology_SL3 : SecondCountableTopology Work.EKLContract.SL3 := by
  have hM : SecondCountableTopology (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → ℝ))
  exact TopologicalSpace.secondCountableTopology_induced Work.EKLContract.SL3
    (Matrix (Fin 3) (Fin 3) ℝ)
    (fun g : Work.EKLContract.SL3 => (g : Matrix (Fin 3) (Fin 3) ℝ))

theorem countable_dense_subgroup (U : Subgroup Work.EKLContract.SL3) :
    ∃ D : Set Work.EKLContract.SL3, D.Countable ∧ D ⊆ (U : Set Work.EKLContract.SL3) ∧
      ∀ O : Set Work.EKLContract.SL3, IsOpen O →
        (O ∩ (U : Set Work.EKLContract.SL3)).Nonempty → (O ∩ D).Nonempty := by
  have hSC : SecondCountableTopology Work.EKLContract.SL3 := secondCountableTopology_SL3
  exact exists_countable_dense_subset_of_secondCountable (U : Set Work.EKLContract.SL3)

end Work.EKLC6Core
