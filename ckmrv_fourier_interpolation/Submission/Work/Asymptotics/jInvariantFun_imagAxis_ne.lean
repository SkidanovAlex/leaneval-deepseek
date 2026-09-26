import Mathlib
import Submission.Work.Asymptotics.jInvariantFun_imagAxis_atTop

namespace Work.Asymptotics

open UpperHalfPlane

/-- **`j` is not constant on the imaginary axis.**  For every `c : ℂ` there is `t > 0` with
`j(it) ≠ c`.  This is immediate from the cusp asymptotics `jInvariantFun_imagAxis_atTop`: `j(it)`
is bounded below by `c₀ e^{2πt}`, hence unbounded as `t → ∞`, so it cannot be constantly equal to
any fixed value. -/
theorem jInvariantFun_imagAxis_ne (c : ℂ) :
    ∃ t : ℝ, 0 < t ∧
      Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I)) ≠ c := by
  obtain ⟨c0, T, hc0, hT, htop⟩ := jInvariantFun_imagAxis_atTop
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  -- Take `t` large enough that the lower bound `c₀ e^{2πt}` exceeds `‖c‖`.
  set t : ℝ := max T (Real.log (‖c‖ / c0 + 1) / (2 * Real.pi) + 1) with ht_def
  have ht : 0 < t := lt_of_lt_of_le hT (le_max_left _ _)
  have hTt : T ≤ t := le_max_left _ _
  refine ⟨t, ht, ?_⟩
  have hb := htop t ht hTt
  have hne : Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) ≠ c := by
    intro h
    rw [h] at hb
    -- `Real.log (‖c‖/c₀ + 1) ≤ 2πt`, because `t` dominates the logarithmic threshold.
    have hlog : Real.log (‖c‖ / c0 + 1) ≤ 2 * Real.pi * t := by
      have h1 : Real.log (‖c‖ / c0 + 1) / (2 * Real.pi) + 1 ≤ t := le_max_right _ _
      have h2 := mul_le_mul_of_nonneg_left h1 h2pi.le
      have h3 : 2 * Real.pi * (Real.log (‖c‖ / c0 + 1) / (2 * Real.pi) + 1)
          = Real.log (‖c‖ / c0 + 1) + 2 * Real.pi := by
        rw [mul_add, mul_div_cancel₀ _ (ne_of_gt h2pi), mul_one]
      linarith [h2, Real.pi_pos]
    have hexp : ‖c‖ / c0 + 1 ≤ Real.exp (2 * Real.pi * t) := by
      have := Real.exp_le_exp.mpr hlog
      rwa [Real.exp_log (by positivity)] at this
    have hmul : ‖c‖ < c0 * Real.exp (2 * Real.pi * t) := by
      have hlt : ‖c‖ / c0 < Real.exp (2 * Real.pi * t) := lt_of_lt_of_le (by linarith) hexp
      have := mul_lt_mul_of_pos_left hlt hc0
      rwa [mul_div_cancel₀ _ (ne_of_gt hc0)] at this
    linarith [hb, hmul]
  -- `ofComplex (it)` is the same point of `ℍ` as `imagAxis t ht`.
  have him : ((t : ℂ) * Complex.I).im = t := by
    rw [Complex.mul_im, Complex.I_im, Complex.I_re]
    simp
  have heq : UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I) = Work.Kernels.imagAxis t ht := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (z := (t : ℂ) * Complex.I) (by rw [him]; exact ht)]
    simp [Work.Kernels.imagAxis]
  rw [heq]
  exact hne

end Work.Asymptotics
