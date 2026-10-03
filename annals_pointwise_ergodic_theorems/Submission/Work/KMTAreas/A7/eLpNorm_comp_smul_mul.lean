import Mathlib

namespace Work.KMTAreas.A7

/-- Reflecting the level sets of `‖(c : ℂ) • ψ (c * x)‖` through the dilation `x ↦ c * x` shows that
the `L¹` `eLpNorm` of `c • ψ (c * ·)` does not see the dilation: the factor `‖c‖` gained by the
scalar multiplication is exactly compensated by the Jacobian `c⁻¹` of `x ↦ c * x`. -/
theorem eLpNorm_comp_smul_mul {ψ : ℝ → ℂ} (hψ : Measurable ψ) {c : ℝ} (hc : 0 < c) :
    MeasureTheory.eLpNorm (fun x : ℝ => (c : ℂ) • ψ (c * x)) 1 MeasureTheory.volume
      = MeasureTheory.eLpNorm ψ 1 MeasureTheory.volume := by
  -- `‖(c : ℂ)‖ₑ = ofReal c`, since `c > 0`.
  have hcn : ‖(c : ℂ)‖ₑ = ENNReal.ofReal c := by
    rw [enorm_eq_nnnorm, Complex.nnnorm_real, ← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp [Real.norm_eq_abs, abs_of_pos hc]
  -- The dilation `x ↦ c * x` pushes Lebesgue measure forward to `ofReal c⁻¹ • volume`.
  have hmap : MeasureTheory.Measure.map (fun x : ℝ => c * x) (MeasureTheory.volume)
      = ENNReal.ofReal c⁻¹ • (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    have h := MeasureTheory.Measure.map_addHaar_smul
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hc.ne'
    simpa [smul_eq_mul, Module.finrank_self, abs_of_pos (inv_pos.2 hc)] using h
  -- Change of variables `x ↦ c * x` in the `eLpNorm` of `ψ`.
  have hstep : MeasureTheory.eLpNorm (fun x : ℝ => ψ (c * x)) 1 MeasureTheory.volume
      = ENNReal.ofReal c⁻¹ * MeasureTheory.eLpNorm ψ 1 MeasureTheory.volume := by
    rw [show (fun x : ℝ => ψ (c * x)) = ψ ∘ (fun x : ℝ => c * x) from rfl]
    rw [← MeasureTheory.eLpNorm_map_measure (f := fun x : ℝ => c * x) (g := ψ)
        hψ.aestronglyMeasurable (by fun_prop)]
    rw [hmap, MeasureTheory.eLpNorm_one_smul_measure]
  -- Pull the constant out of the `eLpNorm`, then use the change of variables.
  rw [show (fun x : ℝ => (c : ℂ) • ψ (c * x)) = (c : ℂ) • (fun x : ℝ => ψ (c * x)) from by
        ext x; rfl]
  rw [MeasureTheory.eLpNorm_const_smul (c := (c : ℂ)) (f := fun x : ℝ => ψ (c * x))
      (p := 1) (μ := MeasureTheory.volume)]
  rw [hstep, hcn]
  rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one, one_mul]

end Work.KMTAreas.A7
