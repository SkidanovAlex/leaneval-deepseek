import Mathlib
import Submission.Work.EKLCompSym.Basic

namespace Work.EKLCompSym

/-- `CrossSection` pulls back along the permutation symmetry `iso τ` of `X₃`: if the image
measure has a conull cross-section for `H.map (conjPerm τ)`, then `μ` has one for `H`.
Concretely, a cross-section set `B` for the image measure pulls back to `iso τ ⁻¹' B`
(with the same conullness, since `iso τ` is measurable and `τ` is invertible). -/
theorem crossSection_preimage_iso {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (τ : Equiv.Perm (Fin 3))
    {H : Subgroup Work.EKLContract.SL3}
    (h : Work.EKLContract.CrossSection (MeasureTheory.Measure.map (Work.EKLCompSym.iso τ) μ)
      (H.map (Work.EKLCompSym.conjPerm τ))) :
    Work.EKLContract.CrossSection μ H := by
  obtain ⟨B, hB, hBc, hBprop⟩ := h
  refine ⟨iso τ ⁻¹' B, measurable_iso τ hB, ?_, ?_⟩
  · rw [← Set.preimage_compl, ← MeasureTheory.Measure.map_apply (measurable_iso τ) hB.compl]
    exact hBc
  · intro x hx u hu hux
    have hux' : conjPerm τ u • iso τ x ∈ B := by
      rw [← iso_smul τ u x]; exact hux
    have hmem : conjPerm τ u ∈ H.map (conjPerm τ) := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    have h1 := hBprop (iso τ x) hx (conjPerm τ u) hmem hux'
    exact (conjPerm_eq_one_iff τ).mp h1

end Work.EKLCompSym
