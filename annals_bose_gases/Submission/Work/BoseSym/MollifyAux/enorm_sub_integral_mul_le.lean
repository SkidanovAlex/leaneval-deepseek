import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.MollifyAux

open MeasureTheory

/-- The `ℝ≥0∞`-integral of a nonnegative weight against a nonnegative function, written as the
`ofReal` of the corresponding real integral. -/
private lemma ofReal_integral_eq_lintegral_ofReal' {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {g : α → ℝ} (hg : Integrable g μ) (h0 : ∀ y, 0 ≤ g y) :
    ENNReal.ofReal (∫ y, g y ∂μ) = ∫⁻ y, ENNReal.ofReal (g y) ∂μ :=
  ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall h0)

/-- **Weighted triangle inequality.** If `ρ ≥ 0` has total mass `1` and `F` is a.e. strongly
measurable and bounded, then for any `c : ℝ`,
`‖c - ∫ F ρ‖ₑ ≤ ∫⁻ ρ · ‖c - F‖ₑ`, i.e. the deviation of `c` from the `ρ`-average of `F` is
dominated by the `ρ`-average of the pointwise deviation `|c - F|`.

Indeed `c - ∫ F ρ = ∫ (c - F) ρ` (because `∫ ρ = 1`), and the claim follows from the triangle
inequality for the integral combined with `ofReal_integral_eq_lintegral_ofReal`. -/
theorem enorm_sub_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {F ρ : α → ℝ} {c M : ℝ} (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : MeasureTheory.integral μ ρ = 1)
    (hFm : MeasureTheory.AEStronglyMeasurable F μ) (hFb : ∀ y, ‖F y‖ ≤ M) :
    enorm (c - MeasureTheory.integral μ (fun y => F y * ρ y)) ≤
      MeasureTheory.lintegral μ (fun y => ENNReal.ofReal (ρ y) * ENNReal.ofReal |c - F y|) := by
  -- `∫ ρ = 1 ≠ 0` forces `ρ` to be integrable.
  have hρint : Integrable ρ μ := by
    by_contra h
    have : (1 : ℝ) = 0 := by rw [← hρ1, integral_undef h]
    exact one_ne_zero this
  -- `F` is bounded, so `F * ρ` is integrable.
  have hFρint : Integrable (fun y => F y * ρ y) μ :=
    Integrable.mono' (hρint.const_mul (max M 0))
      (hFm.mul hρint.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => by
        have hFM : |F y| ≤ max M 0 := by
          rw [← Real.norm_eq_abs]
          exact le_trans (hFb y) (le_max_left _ _)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 y)]
        exact mul_le_mul_of_nonneg_right hFM (hρ0 y))
  have hcρint : Integrable (fun y => c * ρ y) μ := hρint.const_mul c
  -- The key identity `c - ∫ F ρ = ∫ (c - F) ρ`.
  have hsplit : ∫ y, (c - F y) * ρ y ∂μ = c - ∫ y, F y * ρ y ∂μ := by
    rw [show (fun y => (c - F y) * ρ y) = fun y => c * ρ y - F y * ρ y from
      funext fun y => by ring]
    rw [integral_sub hcρint hFρint, integral_const_mul, hρ1]
    ring
  have hGFint : Integrable (fun y => (c - F y) * ρ y) μ := by
    rw [show (fun y => (c - F y) * ρ y) = fun y => c * ρ y - F y * ρ y from
      funext fun y => by ring]
    exact hcρint.sub hFρint
  have hAbsInt : Integrable (fun y => |(c - F y) * ρ y|) μ := hGFint.abs
  calc enorm (c - ∫ y, F y * ρ y ∂μ)
      = ENNReal.ofReal |c - ∫ y, F y * ρ y ∂μ| := Real.enorm_eq_ofReal_abs _
    _ = ENNReal.ofReal |∫ y, (c - F y) * ρ y ∂μ| := by rw [hsplit]
    _ ≤ ENNReal.ofReal (∫ y, |(c - F y) * ρ y| ∂μ) :=
        ENNReal.ofReal_le_ofReal abs_integral_le_integral_abs
    _ = ∫⁻ y, ENNReal.ofReal |(c - F y) * ρ y| ∂μ :=
        ofReal_integral_eq_lintegral_ofReal' hAbsInt fun y => abs_nonneg _
    _ = ∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal |c - F y| ∂μ :=
        lintegral_congr fun y => by
          rw [abs_mul, abs_of_nonneg (hρ0 y), ENNReal.ofReal_mul (abs_nonneg (c - F y))]
          exact mul_comm _ _

end Work.BoseSym.MollifyAux
