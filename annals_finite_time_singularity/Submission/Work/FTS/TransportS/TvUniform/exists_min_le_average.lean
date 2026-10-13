import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.TransportS.TvUniform

/-- **First moment method on `[0, π/2]`.** A function that is continuous and integrable on
`[0, π/2]` is at most its own average `(2/π) ∫_0^{π/2} f` at some point of the interval.

The only ingredient needed is Mathlib's `MeasureTheory.exists_le_setAverage` (the minimum of an
integrable function is smaller than its mean), together with the computation
`volume.real (Icc 0 (π/2)) = π/2`, whence the set-average is `(π/2)⁻¹ • ∫ = (2/π) * ∫`.
Continuity is not used, but is part of the requested statement. -/
theorem exists_min_le_average {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn f (Set.Icc 0 (Real.pi / 2))) :
    ∃ θ₀ ∈ Set.Icc 0 (Real.pi / 2),
      f θ₀ ≤ (2 / Real.pi) * (∫ θ in Set.Icc 0 (Real.pi / 2), f θ) := by
  have hπ : 0 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hμ0 : MeasureTheory.volume (Set.Icc 0 (Real.pi / 2)) ≠ 0 := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith [Real.pi_pos])
  have hμtop : MeasureTheory.volume (Set.Icc 0 (Real.pi / 2)) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  obtain ⟨x, hx, hle⟩ := MeasureTheory.exists_le_setAverage (μ := MeasureTheory.volume)
    (s := Set.Icc 0 (Real.pi / 2)) (f := f) hμ0 hμtop hint
  refine ⟨x, hx, ?_⟩
  rw [MeasureTheory.setAverage_eq MeasureTheory.volume f (Set.Icc 0 (Real.pi / 2)),
      Real.volume_real_Icc_of_le hπ] at hle
  simp only [sub_zero, smul_eq_mul, inv_div] at hle
  exact hle

end Work.FTS.TransportS.TvUniform
