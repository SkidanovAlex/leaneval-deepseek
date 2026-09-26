import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs

namespace Work.Topology.SphereSlicing

open Set

/-- A `2π`-periodic curve attains every one of its values in the fundamental interval
`[0, 2π)`: the range of a `ClosedCurve` is the image of that interval. -/
lemma range_closedCurve_eq_image_Ico {P : Work.CoreTopology.ParamTorus}
    (γ : Work.CoreTopology.ClosedCurve P) :
    Set.range γ.γ = γ.γ '' Set.Ico 0 (2 * Real.pi) := by
  refine Set.Subset.antisymm ?_ (Set.image_subset_range _ _)
  rintro y ⟨t, rfl⟩
  obtain ⟨k, hk, -⟩ :=
    existsUnique_sub_zsmul_mem_Ico (a := 2 * Real.pi) (by positivity) t 0
  refine ⟨t - k • (2 * Real.pi), by simpa using hk, ?_⟩
  conv_rhs => rw [← sub_add_cancel t (k • (2 * Real.pi))]
  exact (Function.Periodic.zsmul γ.periodic k (t - k • (2 * Real.pi))).symm

theorem encard_range_inter_le_encard_param {P : Work.CoreTopology.ParamTorus}
    (γ : Work.CoreTopology.ClosedCurve P) (T : Set LeanEval.KnotTheory.PardonDistortion.R3) :
    Set.encard (Set.range γ.γ ∩ T) ≤
      Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ γ.γ t ∈ T} := by
  have hS : Set.range γ.γ ∩ T = γ.γ '' (Set.Ico 0 (2 * Real.pi) ∩ γ.γ ⁻¹' T) := by
    rw [range_closedCurve_eq_image_Ico γ]
    ext y
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hyT⟩
      exact ⟨t, ⟨ht, hyT⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hyT⟩, rfl⟩
      exact ⟨⟨t, ht, rfl⟩, hyT⟩
  rw [hS]
  exact Set.encard_image_le γ.γ (Set.Ico 0 (2 * Real.pi) ∩ γ.γ ⁻¹' T)

end Work.Topology.SphereSlicing
