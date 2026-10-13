import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.FstarOde

theorem not_integrableOn_of_rpow_lower {f : ℝ → ℝ} {m b q : ℝ} (hm : 0 < m) (hb : 0 < b)
    (hq : q ≤ -1) (hlow : ∀ z ∈ Set.Ioo (0 : ℝ) b, m * z ^ q ≤ f z) :
    ¬ MeasureTheory.IntegrableOn f (Set.Ioo (0 : ℝ) b) := by
  -- `z ↦ z ^ q` is *not* integrable on `(0,b)` when `q ≤ -1`.
  intro hf
  have hmne : m ≠ 0 := ne_of_gt hm
  have hinv : 0 < (1 : ℝ) / m := by positivity
  have hnot : ¬ MeasureTheory.IntegrableOn (fun z : ℝ => z ^ q) (Set.Ioo (0 : ℝ) b) := by
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff hb]
    exact not_lt.mpr hq
  -- `f` dominates `m * z ^ q` on `(0,b)`, hence dominates `z ^ q` up to the positive
  -- constant `1/m`; a function dominated by an integrable one (and nonnegative) is integrable.
  apply hnot
  refine MeasureTheory.Integrable.mono' (g := fun z : ℝ => (1 / m) * f z) ?_ ?_ ?_
  · exact hf.const_mul (1 / m)
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    exact continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt hz.1))
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
    have hz0 : 0 < z := hz.1
    have hzq : 0 ≤ z ^ q := Real.rpow_nonneg (le_of_lt hz0) q
    rw [Real.norm_eq_abs, abs_of_nonneg hzq]
    calc z ^ q = (m⁻¹ * m) * z ^ q := by rw [inv_mul_cancel₀ hmne, one_mul]
      _ = (1 / m) * (m * z ^ q) := by ring
      _ ≤ (1 / m) * f z := mul_le_mul_of_nonneg_left (hlow z hz) (le_of_lt hinv)

end Work.FTS_EllLimOK.FstarOde
