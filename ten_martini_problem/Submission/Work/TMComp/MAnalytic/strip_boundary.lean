import Mathlib

namespace Work.TMComp.MAnalytic

theorem strip_boundary {W : Set ℂ} {a : ℂ} {R δ : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (hbd : ∀ z ∈ Metric.closedBall a (2 * R), ‖g z‖ ≤ 1)
    (hsm : ∀ z ∈ Metric.closedBall a R, ‖g z‖ ≤ Real.exp (-δ)) :
    BddAbove ((norm ∘ (fun w : ℂ => g (a + Complex.exp w))) ''
        Complex.HadamardThreeLines.verticalClosedStrip (Real.log R) (Real.log (2 * R))) ∧
      (∀ z ∈ Complex.re ⁻¹' {Real.log R}, ‖g (a + Complex.exp z)‖ ≤ Real.exp (-δ)) ∧
      (∀ z ∈ Complex.re ⁻¹' {Real.log (2 * R)}, ‖g (a + Complex.exp z)‖ ≤ 1) := by
  have h2R : (0 : ℝ) < 2 * R := by linarith
  have hlogR : Real.exp (Real.log R) = R := Real.exp_log hR
  have hlog2R : Real.exp (Real.log (2 * R)) = 2 * R := Real.exp_log h2R
  -- points with real part `log R` lie in the closed ball of radius `R` around `a`
  have hmemR : ∀ z : ℂ, z.re = Real.log R → a + Complex.exp z ∈ Metric.closedBall a R := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp, hz, hlogR]
  -- points with real part `log (2 * R)` lie in the closed ball of radius `2 * R`
  have hmem2R : ∀ z : ℂ, z.re = Real.log (2 * R) →
      a + Complex.exp z ∈ Metric.closedBall a (2 * R) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp, hz, hlog2R]
  refine ⟨?_, ?_, ?_⟩
  · rw [bddAbove_def]
    refine ⟨1, ?_⟩
    rintro x ⟨w, hw, rfl⟩
    simp only [Function.comp_apply]
    apply hbd
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
    calc Real.exp w.re ≤ Real.exp (Real.log (2 * R)) := Real.exp_le_exp.mpr hw.2
      _ = 2 * R := hlog2R
  · intro z hz
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hz
    exact hsm _ (hmemR z hz)
  · intro z hz
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hz
    exact hbd _ (hmem2R z hz)

end Work.TMComp.MAnalytic
