import Mathlib.MeasureTheory.Function.L2Space
import Submission.Commons.MeasureTheory.integrableOn_volume_of_memLp_withDensity_exp_neg

open MeasureTheory
open scoped ENNReal

namespace Commons.MeasureTheory.LocallyIntegrable

/-- If `V` is `L²` for the weighted measure `e^{-φ} dz`, with `φ` continuous, then on every
compact set `K` the density `e^{-φ}` is bounded below by a positive constant.  Hence the
weighted measure dominates Lebesgue measure on `K`, so `V` is still `L²` for the restricted
Lebesgue measure `volume.restrict K`. -/
theorem memLp_restrict_of_memLp_withDensity_exp_neg {d : ℕ} {φ : (Fin d → ℂ) → ℝ}
    (hφ : Continuous φ) {F : (Fin d → ℂ) → ℂ}
    (hF : MeasureTheory.MemLp F 2
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).withDensity
        (fun z => ENNReal.ofReal (Real.exp (-(φ z))))))
    {K : Set (Fin d → ℂ)} (hK : IsCompact K) :
    MeasureTheory.MemLp F 2 ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).restrict K) := by
  -- `φ` is bounded above on the compact set `K`.
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z ∈ K, φ z ≤ M := by
    rcases hK.bddAbove_image hφ.continuousOn with ⟨M, hM⟩
    exact ⟨M, fun z hz => hM ⟨z, hz, rfl⟩⟩
  let g : (Fin d → ℂ) → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (-(φ z)))
  let cst : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-M))
  let C : ℝ≥0∞ := cst⁻¹
  have hcst0 : cst ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hcsttop : cst ≠ ∞ := ENNReal.ofReal_ne_top
  have hCtop : C ≠ ∞ := ENNReal.inv_ne_top.mpr hcst0
  have hK_meas : MeasurableSet K := hK.measurableSet
  -- On `K` the density is bounded below by `cst > 0`, so the restricted Lebesgue measure is
  -- dominated by `C • μ` where `μ = volume.withDensity g`.
  have hle : (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).restrict K
      ≤ C • ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).withDensity g) := by
    have hpoint : (K.indicator (1 : (Fin d → ℂ) → ℝ≥0∞)) ≤ (C • g) := by
      intro z
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz]
        show (1 : ℝ≥0∞) ≤ C * g z
        have hgz : cst ≤ g z :=
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg (hM z hz)))
        calc (1 : ℝ≥0∞) = C * cst := (ENNReal.inv_mul_cancel hcst0 hcsttop).symm
          _ ≤ C * g z := by gcongr
      · rw [Set.indicator_of_notMem hz]
        exact zero_le
    have hthis := MeasureTheory.withDensity_mono
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))
      (Filter.Eventually.of_forall hpoint)
    rw [MeasureTheory.withDensity_indicator_one hK_meas,
      MeasureTheory.withDensity_smul' C g hCtop] at hthis
    exact hthis
  exact MeasureTheory.MemLp.mono_measure hle (hF.smul_measure hCtop)

theorem of_memLp_withDensity_exp_neg {d : ℕ} {φ : (Fin d → ℂ) → ℝ}
    (hφ : Continuous φ) {F : (Fin d → ℂ) → ℂ}
    (hF : MeasureTheory.MemLp F 2 ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).withDensity
      (fun z => ENNReal.ofReal (Real.exp (-(φ z)))))) :
    MeasureTheory.LocallyIntegrable F (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) ∧
      MeasureTheory.LocallyIntegrable (fun z => ‖F z‖ ^ 2)
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) := by
  constructor
  · rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    exact Commons.MeasureTheory.integrableOn_volume_of_memLp_withDensity_exp_neg hφ hF hK
  · rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    exact (memLp_two_iff_integrable_sq_norm
      (memLp_restrict_of_memLp_withDensity_exp_neg hφ hF hK).1).mp
        (memLp_restrict_of_memLp_withDensity_exp_neg hφ hF hK)

end Commons.MeasureTheory.LocallyIntegrable