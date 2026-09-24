import Mathlib
import Submission.Work.GM.Affine.fine_setup

/-!
# The local lower bound `T ∫_{B(y,1/(8T))} f ≤ f̃(y)` (GM §9, Lemma 9.2)

For the smoothing kernel `ψ = psiSmooth` of Lemma 9.2 (nonnegative, `∫ψ = 1`, supported in
`[-1,1]`, and `≥ 1` on `[-1/8,1/8]`) and the smoothed function
`f̃(y) = smoothed ψ T f y = T ∫ ψ(T(y-u')) f(u') du'`, the ball of radius `1/(8T)` around `y`
already contributes at least `T ∫_{B(y,1/(8T))} f`:

  `T * ∫ u' in closedBall y (1/(8T)), f u' ≤ f̃(y)`.

Indeed, for `|u' - y| ≤ 1/(8T)` we have `|T(y-u')| ≤ 1/8`, so `ψ(T(y-u')) ≥ 1` and hence
`f(u') ≤ ψ(T(y-u')) f(u')` (using `f ≥ 0`); the claim follows by monotonicity of the integral
and the fact that the full integral dominates the integral over any set.
-/

open MeasureTheory

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- A crude bound for the smoothing kernel: `psiSmooth ≤ 4` everywhere. -/
lemma psiSmooth_le_four (x : ℝ) : psiSmooth x ≤ 4 := by
  have h := ContDiffBump.normed_le_div_measure_closedBall_rIn (f := psiBump)
    (μ := (volume : Measure ℝ)) x
  have hr : psiBump.rIn = 1 / 8 := rfl
  rw [hr] at h
  have hv : (volume : Measure ℝ).real (Metric.closedBall (0 : ℝ) (1 / 8)) = 2 * (1 / 8) :=
    Real.volume_real_closedBall (by norm_num)
  rw [hv] at h
  rw [show psiSmooth x = psiBump.normed volume x from rfl]
  linarith [h]

/-- The product `ψ(T(y - ·)) f` of the bounded kernel with an integrable, nonnegative `f` is
integrable. -/
lemma integrable_psiSmooth_mul {T : ℝ} {f : ℝ → ℝ} (hf : Integrable f)
    (hnn : ∀ u, 0 ≤ f u) (y : ℝ) :
    Integrable (fun u' => psiSmooth (T * (y - u')) * f u') := by
  have hFnn : ∀ u', 0 ≤ psiSmooth (T * (y - u')) * f u' :=
    fun u' => mul_nonneg (psiSmooth_nonneg _) (hnn u')
  refine Integrable.mono' (g := fun u' => 4 * f u') (hf.const_mul 4) ?_ ?_
  · have h1 : AEStronglyMeasurable (fun u' : ℝ => psiSmooth (T * (y - u'))) volume :=
      (psiSmooth_contDiff.continuous.comp (by fun_prop)).aestronglyMeasurable
    exact h1.mul hf.aestronglyMeasurable
  · filter_upwards with u'
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn u')]
    exact mul_le_mul_of_nonneg_right (psiSmooth_le_four _) (hnn u')

theorem smoothed_local {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ} (hnn : ∀ u, 0 ≤ f u)
    (hf : MeasureTheory.Integrable f) (y : ℝ) :
    T * ∫ u' in Metric.closedBall y (1 / (8 * T)), f u' ≤ smoothed psiSmooth T f y := by
  rw [smoothed]
  apply mul_le_mul_of_nonneg_left _ hT.le
  have hFnn : ∀ u', 0 ≤ psiSmooth (T * (y - u')) * f u' :=
    fun u' => mul_nonneg (psiSmooth_nonneg _) (hnn u')
  have hFint : Integrable (fun u' => psiSmooth (T * (y - u')) * f u') :=
    integrable_psiSmooth_mul hf hnn y
  have hpt : ∀ u' ∈ Metric.closedBall y (1 / (8 * T)),
      f u' ≤ psiSmooth (T * (y - u')) * f u' := by
    intro u' hu'
    have hdist : |u' - y| ≤ 1 / (8 * T) := by
      rw [Metric.mem_closedBall, Real.dist_eq] at hu'
      exact hu'
    have h1 : |T * (y - u')| ≤ 1 / 8 := by
      rw [abs_mul, abs_of_pos hT, abs_sub_comm]
      calc T * |u' - y| ≤ T * (1 / (8 * T)) := mul_le_mul_of_nonneg_left hdist hT.le
        _ = 1 / 8 := by field_simp
    have h2 : 1 ≤ psiSmooth (T * (y - u')) :=
      psiSmooth_ge_one (by rw [Metric.mem_closedBall, Real.dist_eq]; simpa using h1)
    simpa using mul_le_mul_of_nonneg_right h2 (hnn u')
  calc ∫ u' in Metric.closedBall y (1 / (8 * T)), f u'
      ≤ ∫ u' in Metric.closedBall y (1 / (8 * T)),
          psiSmooth (T * (y - u')) * f u' :=
        MeasureTheory.setIntegral_mono_on hf.integrableOn hFint.integrableOn
          measurableSet_closedBall hpt
    _ ≤ ∫ u', psiSmooth (T * (y - u')) * f u' :=
        MeasureTheory.setIntegral_le_integral hFint (ae_of_all _ hFnn)

end

end Work.GM.Affine
