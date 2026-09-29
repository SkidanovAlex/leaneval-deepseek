import Mathlib

namespace Work.TMComp.MAnalytic

open Set Metric

/-- The exponential of a point whose real part is at most `log (2R)` has norm at most `2R`. -/
private lemma norm_exp_le_two_mul {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hw : w.re ≤ Real.log (2 * R)) : ‖Complex.exp w‖ ≤ 2 * R := by
  have hR2 : (0 : ℝ) < 2 * R := by linarith
  rw [Complex.norm_exp]
  calc Real.exp w.re ≤ Real.exp (Real.log (2 * R)) := Real.exp_le_exp.mpr hw
    _ = 2 * R := Real.exp_log hR2

/-- The closure of an open vertical strip is contained in the closed vertical strip. -/
private lemma closure_verticalStrip_subset {R : ℝ} (hR : 0 < R) :
    closure (Complex.HadamardThreeLines.verticalStrip (Real.log R) (Real.log (2 * R)))
      ⊆ Complex.HadamardThreeLines.verticalClosedStrip (Real.log R) (Real.log (2 * R)) := by
  have hloglt : Real.log R < Real.log (2 * R) := Real.log_lt_log hR (by linarith)
  intro w hw
  have h1 : w.re ∈ closure (Set.Ioo (Real.log R) (Real.log (2 * R))) :=
    Complex.continuous_re.closure_preimage_subset (Set.Ioo (Real.log R) (Real.log (2 * R))) hw
  rw [closure_Ioo (ne_of_lt hloglt)] at h1
  exact h1

theorem strip_diffContOnCl {W : Set ℂ} {a : ℂ} {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (han : AnalyticOnNhd ℂ g W) (hball : Metric.closedBall a (2 * R) ⊆ W) :
    DiffContOnCl ℂ (fun w : ℂ => g (a + Complex.exp w))
      (Complex.HadamardThreeLines.verticalStrip (Real.log R) (Real.log (2 * R))) := by
  have hR2 : (0 : ℝ) < 2 * R := by linarith
  refine ⟨?_, ?_⟩
  · -- differentiability on the open strip
    have hmaps : MapsTo (fun w : ℂ => a + Complex.exp w)
        (Complex.HadamardThreeLines.verticalStrip (Real.log R) (Real.log (2 * R))) W := by
      intro w hw
      apply hball
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hwle : w.re ≤ Real.log (2 * R) := by
        simp only [Complex.HadamardThreeLines.verticalStrip, mem_preimage, mem_Ioo] at hw
        exact le_of_lt hw.2
      rw [add_sub_cancel_left]
      exact norm_exp_le_two_mul hR hwle
    have hdiff : DifferentiableOn ℂ (fun w : ℂ => a + Complex.exp w)
        (Complex.HadamardThreeLines.verticalStrip (Real.log R) (Real.log (2 * R))) :=
      ((Complex.differentiable_exp.const_add a).differentiableOn)
    exact han.differentiableOn.comp hdiff hmaps
  · -- continuity on the closure of the strip
    have hmapsCl : MapsTo (fun w : ℂ => a + Complex.exp w)
        (closure (Complex.HadamardThreeLines.verticalStrip (Real.log R) (Real.log (2 * R)))) W := by
      intro w hw
      apply hball
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h1 : w.re ∈ Set.Icc (Real.log R) (Real.log (2 * R)) :=
        closure_verticalStrip_subset hR hw
      simp only [mem_Icc] at h1
      rw [add_sub_cancel_left]
      exact norm_exp_le_two_mul hR h1.2
    have hcont : ContinuousOn (fun w : ℂ => a + Complex.exp w)
        (closure (Complex.HadamardThreeLines.verticalStrip (Real.log R) (Real.log (2 * R)))) :=
      (Complex.continuous_exp.const_add a).continuousOn
    exact han.continuousOn.comp hcont hmapsCl

end Work.TMComp.MAnalytic
