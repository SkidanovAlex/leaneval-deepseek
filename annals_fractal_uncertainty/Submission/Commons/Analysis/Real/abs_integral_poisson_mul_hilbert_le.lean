import Mathlib
import Submission.Commons.Analysis.Real.hilbert_poisson_smoothing
import Submission.Commons.Analysis.Real.integral_mul_odd_eq_integral_Ioi_sub_neg
import Submission.Commons.MeasureTheory.Integral.abs_integral_poisson_le

open MeasureTheory Set

namespace Commons.Analysis.Real

/-- **The conjugate-Poisson (Hilbert) transform bound.**

Let `φ : ℝ → ℝ` be `C²` with compact support, and suppose that for every `x` the
Hilbert-type integral `(1/π) ∫_0^∞ (φ'(x+t) - φ'(x-t))/t dt` is bounded in absolute value
by `C₁`.  Then the conjugate Poisson transform of `φ'` at the origin,
`(1/π) ∫_0^∞ (φ'(u) - φ'(-u)) u/(u²+s²) du`, is bounded by the same constant `C₁`. -/
theorem abs_integral_poisson_mul_hilbert_le {φ : ℝ → ℝ} {C₁ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hH : ∀ x : ℝ, |(1 / Real.pi) * ∫ t in Set.Ioi (0 : ℝ),
      (deriv φ (x + t) - deriv φ (x - t)) / t| ≤ C₁)
    {s : ℝ} (hs : 0 < s) :
    |(1 / Real.pi) * ∫ u in Set.Ioi (0 : ℝ),
        (deriv φ u - deriv φ (-u)) * (u / (u ^ 2 + s ^ 2))| ≤ C₁ := by
  set g : ℝ → ℝ := deriv φ with hg_def
  have hg1 : ContDiff ℝ 1 g := by rw [hg_def]; exact hφ.deriv'
  have hcs : HasCompactSupport g := by rw [hg_def]; exact hc.deriv
  have hgcont : Continuous g := hg1.continuous
  have hgint : Integrable g := hgcont.integrable_of_hasCompactSupport hcs
  -- The kernel `u ↦ u/(u²+s²)` is odd, so the full-line integral of `g` against it
  -- equals the half-line integral of `g u - g (-u)` against it.
  have hodd : ∀ x : ℝ,
      (fun x : ℝ => x / (x ^ 2 + s ^ 2)) (-x) = -(fun x : ℝ => x / (x ^ 2 + s ^ 2)) x := by
    intro x; simp only [neg_sq]; ring
  have hbound2 : ∀ᵐ x : ℝ, ‖x / (x ^ 2 + s ^ 2)‖ ≤ 1 / (2 * s) := by
    filter_upwards with x
    have hpos : (0:ℝ) < x^2+s^2 := by positivity
    have h2s : (0:ℝ) < 2*s := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    rw [div_le_iff₀ hpos, one_div, inv_mul_eq_div, le_div_iff₀ h2s]
    have hab : |x| * (2 * s) ≤ x ^ 2 + s ^ 2 := by
      nlinarith [sq_nonneg (|x| - s), sq_abs x, abs_nonneg x]
    linarith [hab]
  have hwmeas : AEStronglyMeasurable (fun x : ℝ => x / (x ^ 2 + s ^ 2)) volume := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.div continuous_id (continuous_id.pow 2 |>.add continuous_const)
    intro x
    have : (0:ℝ) < x^2 + s^2 := by positivity
    positivity
  have hint : Integrable (fun x : ℝ => g x * (x / (x ^ 2 + s ^ 2))) :=
    hgint.mul_bdd hwmeas hbound2
  have hsym : ∫ x : ℝ, g x * (x / (x ^ 2 + s ^ 2))
      = ∫ u in Set.Ioi (0 : ℝ), (g u - g (-u)) * (u / (u ^ 2 + s ^ 2)) :=
    integral_mul_odd_eq_integral_Ioi_sub_neg g (fun x : ℝ => x / (x ^ 2 + s ^ 2)) hodd hint
  -- The Hilbert transform smeared against the Poisson kernel is a Poisson average.
  have hsm : (1 / Real.pi) * ∫ v : ℝ, g v * (v / (v ^ 2 + s ^ 2))
      = ∫ y : ℝ, ((1 / Real.pi) * ∫ t in Set.Ioi (0 : ℝ), (g (y + t) - g (y - t)) / t)
          * (s / (Real.pi * (s ^ 2 + y ^ 2))) :=
    hilbert_poisson_smoothing hg1 hcs hs
  have hA : ∀ y : ℝ,
      |(1 / Real.pi) * ∫ t in Set.Ioi (0 : ℝ), (g (y + t) - g (y - t)) / t| ≤ C₁ := by
    intro y
    simpa [hg_def] using hH y
  have hb := Commons.MeasureTheory.Integral.abs_integral_poisson_le
    (fun y : ℝ => (1 / Real.pi) * ∫ t in Set.Ioi (0 : ℝ), (g (y + t) - g (y - t)) / t) hs hA
  rw [← hsym, hsm]
  exact hb

end Commons.Analysis.Real
