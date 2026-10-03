import Mathlib

/-!
# An area-formula bound for the squared operator norm of the derivative

For an injective `C^1` map `g : ℂ → ℂ` whose derivative satisfies
`‖fderiv g z‖ ^ 2 ≤ C * (fderiv g z).det` everywhere (with `C ≥ 0`), the integral of
`‖fderiv g z‖ ^ 2` over a ball is bounded by `C` times the (planar) measure of the image of
that ball.

This is the standard consequence of the change-of-variables formula
(`MeasureTheory.lintegral_abs_det_fderiv_le_addHaar_image`): pointwise we have
`‖Dg‖ ^ 2 ≤ C * det Dg`, and since the hypothesis forces `det Dg ≥ 0`, the determinant
integral is the area of the image.
-/

namespace Work.Fatou.Analysis

open MeasureTheory Metric

theorem lintegral_normSq_fderiv_le (g : ℂ → ℂ) (C R : ℝ) (hC : 0 ≤ C)
    (hC1 : ContDiff ℝ 1 g) (hinj : Function.Injective g)
    (hpt : ∀ z, ‖fderiv ℝ g z‖ ^ 2 ≤ C * (fderiv ℝ g z).det) :
    ∫⁻ z in Metric.ball (0 : ℂ) R, ENNReal.ofReal (‖fderiv ℝ g z‖ ^ 2) ≤
      ENNReal.ofReal C * MeasureTheory.volume (g '' Metric.ball (0 : ℂ) R) := by
  have hdiff : ∀ z, HasFDerivAt g (fderiv ℝ g z) z :=
    fun z => (hC1.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · -- If `C = 0` the hypothesis forces the derivative to vanish, so both sides vanish.
    subst hC0
    simp only [ENNReal.ofReal_zero, zero_mul]
    have hzero : ∀ z, ENNReal.ofReal (‖fderiv ℝ g z‖ ^ 2) = 0 := by
      intro z
      have h0 : ‖fderiv ℝ g z‖ ^ 2 = 0 := by
        have hz := hpt z
        simp only [zero_mul] at hz
        exact le_antisymm hz (by positivity)
      rw [h0, ENNReal.ofReal_zero]
    rw [lintegral_congr hzero]
    simp
  · -- `C > 0`: the determinant of the derivative is nonnegative, and the
    -- change-of-variables formula bounds its integral by the measure of the image.
    have hdet_nonneg : ∀ z, 0 ≤ (fderiv ℝ g z).det := fun z =>
      (mul_nonneg_iff_of_pos_left hCpos).mp (le_trans (by positivity) (hpt z))
    set s := Metric.ball (0 : ℂ) R with hs_def
    have hs : MeasurableSet s := Metric.isOpen_ball.measurableSet
    have hstep1 : ∫⁻ z in s, ENNReal.ofReal (‖fderiv ℝ g z‖ ^ 2)
        ≤ ∫⁻ z in s, ENNReal.ofReal (C * (fderiv ℝ g z).det) :=
      lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hpt z)
    have hstep2 : ∫⁻ z in s, ENNReal.ofReal (C * (fderiv ℝ g z).det)
        = ENNReal.ofReal C * ∫⁻ z in s, ENNReal.ofReal ((fderiv ℝ g z).det) := by
      rw [show (∫⁻ z in s, ENNReal.ofReal (C * (fderiv ℝ g z).det))
          = (∫⁻ z in s, ENNReal.ofReal C * ENNReal.ofReal ((fderiv ℝ g z).det)) from
        lintegral_congr (f := fun z => ENNReal.ofReal (C * (fderiv ℝ g z).det))
          (g := fun z => ENNReal.ofReal C * ENNReal.ofReal ((fderiv ℝ g z).det))
          (fun z => ENNReal.ofReal_mul hC)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hstep3 : ∫⁻ z in s, ENNReal.ofReal ((fderiv ℝ g z).det)
        ≤ MeasureTheory.volume (g '' s) := by
      rw [show (∫⁻ z in s, ENNReal.ofReal ((fderiv ℝ g z).det))
          = (∫⁻ z in s, ENNReal.ofReal |(fderiv ℝ g z).det|) from
        lintegral_congr (fun z => by rw [abs_of_nonneg (hdet_nonneg z)])]
      exact lintegral_abs_det_fderiv_le_addHaar_image (volume : Measure ℂ) hs
        (fun z _ => (hdiff z).hasFDerivWithinAt) (hinj.injOn)
    calc ∫⁻ z in s, ENNReal.ofReal (‖fderiv ℝ g z‖ ^ 2)
        ≤ ∫⁻ z in s, ENNReal.ofReal (C * (fderiv ℝ g z).det) := hstep1
      _ = ENNReal.ofReal C * ∫⁻ z in s, ENNReal.ofReal ((fderiv ℝ g z).det) := hstep2
      _ ≤ ENNReal.ofReal C * MeasureTheory.volume (g '' s) :=
          mul_le_mul_of_nonneg_left hstep3 (by positivity)

end Work.Fatou.Analysis
