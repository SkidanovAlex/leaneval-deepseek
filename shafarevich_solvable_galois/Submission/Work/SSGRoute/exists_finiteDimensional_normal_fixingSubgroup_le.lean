import Mathlib.FieldTheory.KrullTopology
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open scoped Topology

/-- In a Galois extension, every open subgroup of the Galois group (Krull topology) contains the
fixing subgroup of a finite-dimensional normal intermediate field. -/
theorem exists_finiteDimensional_normal_fixingSubgroup_le
    {U L : Type*} [Field U] [Field L] [Algebra U L] [IsGalois U L]
    (H : Subgroup (L ≃ₐ[U] L)) (hH : IsOpen (H : Set (L ≃ₐ[U] L))) :
    ∃ M : IntermediateField U L, FiniteDimensional U M ∧ Normal U ↥M ∧ M.fixingSubgroup ≤ H := by
  have hmem : (H : Set (L ≃ₐ[U] L)) ∈ 𝓝 1 := by
    rw [isOpen_iff_mem_nhds] at hH
    exact hH 1 H.one_mem
  obtain ⟨E, hEfin, hEnorm, hsub⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal U L (H : Set (L ≃ₐ[U] L))).mp hmem
  exact ⟨E, hEfin, hEnorm, hsub⟩

end Work.SSGRoute
