import Mathlib
import Submission.Work.EKLCompSym.Basic

namespace Work.EKLCompSym

/-- The relative-cross-section predicate is transported by the `S₃`-symmetry `iso τ` of `X₃`,
with the subgroups conjugated by `conjPerm τ`.  The conull set `B` is transported to
`(iso τ⁻¹) ⁻¹' B`, whose preimage under `iso τ` is again `B` (as `iso τ⁻¹` inverts `iso τ`), and
the defining property is read off from `iso_smul` together with `conjPerm_symm_left`. -/
theorem relCrossSection_map_iso {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (τ : Equiv.Perm (Fin 3))
    {H L : Subgroup Work.EKLContract.SL3} (h : Work.EKLContract.RelCrossSection μ H L) :
    Work.EKLContract.RelCrossSection (MeasureTheory.Measure.map (Work.EKLCompSym.iso τ) μ)
      (H.map (Work.EKLCompSym.conjPerm τ)) (L.map (Work.EKLCompSym.conjPerm τ)) := by
  obtain ⟨B, hBmeas, hBnull, hBprop⟩ := h
  refine ⟨(iso τ⁻¹) ⁻¹' B, (measurable_iso τ⁻¹) hBmeas, ?_, ?_⟩
  · rw [MeasureTheory.Measure.map_apply (measurable_iso τ)
      ((measurable_iso τ⁻¹) hBmeas).compl]
    have hpre : (iso τ) ⁻¹' ((iso τ⁻¹) ⁻¹' B) = B := by
      ext x; simp only [Set.mem_preimage]; rw [iso_symm_left]
    rw [Set.preimage_compl, hpre, hBnull]
  · intro x hx h' hh' hh'x
    obtain ⟨h₀, hh₀H, rfl⟩ := (Subgroup.mem_map.mp hh')
    have h2 : h₀ • (iso τ⁻¹ x) ∈ B := by
      have h3 := hh'x
      simp only [Set.mem_preimage] at h3
      rwa [iso_smul τ⁻¹ (conjPerm τ h₀) x, conjPerm_symm_left τ h₀] at h3
    exact Subgroup.mem_map.mpr ⟨h₀, hBprop (iso τ⁻¹ x) hx h₀ hh₀H h2, rfl⟩

end Work.EKLCompSym
