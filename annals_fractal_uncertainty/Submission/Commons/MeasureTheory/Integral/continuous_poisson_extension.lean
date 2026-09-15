import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Commons.MeasureTheory.Integral

/-- **Continuity of the Poisson extension.**  For a continuous compactly supported `f`, the
function `(x, y) ↦ ∫ t, f (x + t • y) * (1 + t^2)⁻¹` is continuous on `ℝ^d × ℝ^d`. -/
theorem continuous_poisson_extension {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Continuous f) (hfs : HasCompactSupport f) :
    Continuous fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      MeasureTheory.integral MeasureTheory.volume fun t : ℝ =>
        f (p.1 + t • p.2) * (1 + t ^ 2)⁻¹ := by
  obtain ⟨M, hM⟩ := hfs.exists_bound_of_continuous hf
  apply MeasureTheory.continuous_of_dominated (bound := fun t : ℝ => M * (1 + t ^ 2)⁻¹)
  · intro p
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact hf.comp (continuous_const.add (continuous_id.smul continuous_const))
    · apply Continuous.inv₀
      · fun_prop
      · intro t; positivity
  · intro p
    filter_upwards with t
    have hc : (0 : ℝ) ≤ (1 + t ^ 2)⁻¹ := by positivity
    rw [norm_mul, Real.norm_of_nonneg hc]
    exact mul_le_mul_of_nonneg_right (hM _) hc
  · exact integrable_inv_one_add_sq.const_mul M
  · filter_upwards with t
    apply Continuous.mul
    · exact hf.comp (continuous_fst.add (continuous_snd.const_smul t))
    · exact continuous_const

end Commons.MeasureTheory.Integral