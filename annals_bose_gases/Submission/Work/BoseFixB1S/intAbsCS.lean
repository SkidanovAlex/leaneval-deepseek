import Mathlib.MeasureTheory.Function.L2Space
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.intAbsCS` — Cauchy–Schwarz (`L²`) for the Bochner integral

Mathlib has Hölder's inequality for the Bochner integral (`integral_mul_norm_le_Lp_mul_Lq`), but
the `p = q = 2` case — the inequality actually used everywhere in the dilute-Bose-gas analysis —
is not packaged: the exponents appear as `rpow`, and the `MemLp` hypotheses are stated with
`ENNReal.ofReal 2`.

This module provides the packaged form,

  `∫ |f·g| ≤ √(∫ f²) · √(∫ g²)`,

for arbitrary real-valued `f, g` which are a.e. strongly measurable with square-integrable
(and, in this development, automatically nonnegative) squares.  Note that the integral of `|f·g|`
is the `Bochner` integral, so no `Integrable` hypothesis on `f·g` itself is needed: this is the
form used by the cross-term estimates, where the extra factor `fib` is *not* known to be
measurable.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1S

/-- **Cauchy–Schwarz in `L²` for the integral.** For a.e. strongly measurable `f, g : α → ℝ`
with square-integrable squares, `∫ |f·g| ≤ √(∫ f²)·√(∫ g²)`.  This is Hölder's inequality at
the conjugate exponents `p = q = 2`. -/
theorem int_abs_mul_le_sqrt_mul_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) (hg2 : Integrable (fun x => g x ^ 2) μ) :
    ∫ x, |f x * g x| ∂μ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have hfl : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using (memLp_two_iff_integrable_sq hf).mpr hf2
  have hgl : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using (memLp_two_iff_integrable_sq hg).mpr hg2
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := f) (g := g)
      (p := 2) (q := 2) Real.HolderConjugate.two_two hfl hgl
  have h1 : ∫ x, |f x * g x| ∂μ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with x
    simp [Real.norm_eq_abs, abs_mul]
  rw [h1]
  have e1 : (∫ a, ‖f a‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) = Real.sqrt (∫ a, f a ^ 2 ∂μ) := by
    rw [← Real.sqrt_eq_rpow]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  have e2 : (∫ a, ‖g a‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) = Real.sqrt (∫ a, g a ^ 2 ∂μ) := by
    rw [← Real.sqrt_eq_rpow]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [e1, e2] at h
  exact h

end Work.BoseFixB1S
