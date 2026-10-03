import Mathlib
import Submission.Commons.Analysis.MeasureTheory.eLpNorm_iSup_of_monotone

namespace Work.A7Hi2

open MeasureTheory

/-- If `p > 0`, then `x ↦ x` is the composite of `x ↦ (x) ^ p` with `y ↦ y ^ p⁻¹`; hence
`ℤ`-function `n ↦ (v n) ^ p` can only be measurable when `v` is. -/
lemma measurable_of_measurable_rpow {p : ℝ} (hp : 0 < p) {v : ℤ → ENNReal}
    (hv : Measurable fun n : ℤ => (v n) ^ p) : Measurable v := by
  have h1 : Measurable fun n : ℤ => ((v n) ^ p) ^ (1 / p) :=
    (ENNReal.continuous_rpow_const (y := 1 / p)).measurable.comp hv
  have heq : (fun n : ℤ => ((v n) ^ p) ^ (1 / p)) = v := by
    funext n
    rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt hp), ENNReal.rpow_one]
  rwa [heq] at h1

/-- **Monotone convergence for the `ℒᵖ` seminorm on `ℤ` with counting measure.**
The `ℒ^{p}` seminorm of the pointwise supremum of an increasing sequence of `ENNReal`-valued
functions is the supremum of the seminorms when `0 < p < ∞`.  (Here `hmeas` is the
measurability of the integrands `(u N ·) ^ p`, as produced by the `ℒᵖ` interface.) -/
theorem eLpNorm_iSup_le {p : ℝ} (hp : 0 < p) {u : ℕ → ℤ → ENNReal} (hmono : Monotone u)
    (hmeas : ∀ N : ℕ, Measurable fun n : ℤ => (u N n) ^ p) :
    MeasureTheory.eLpNorm (fun n : ℤ => ⨆ N : ℕ, u N n) (ENNReal.ofReal p)
        (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ ⨆ N : ℕ, MeasureTheory.eLpNorm (u N) (ENNReal.ofReal p)
        (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  have hu : ∀ N : ℕ, Measurable (u N) := fun N => measurable_of_measurable_rpow hp (hmeas N)
  refine le_of_eq ?_
  exact Commons.Analysis.MeasureTheory.eLpNorm_iSup_of_monotone
    (p := ENNReal.ofReal p) (μ := (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ))
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top hu hmono

end Work.A7Hi2
