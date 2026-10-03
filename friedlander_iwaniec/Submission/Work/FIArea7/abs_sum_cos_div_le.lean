import Mathlib
import Submission.Work.FIArea7.Defs
import Submission.Work.FIArea7.integral_cos_sub_div_Q
import Submission.Work.FIArea7.abs_integral_P_le
import Submission.Work.FIArea7.integral_sum_cos

/-!
# The tail bound for the Fourier series of `-log(2 |sin(α/2)|)`

For `sin(α/2) ≠ 0` and `K ≥ 1`,

`|∑_{n≤K} cos(nα)/n + log(2|sin(α/2)|)| ≤ 4/(K |sin(α/2)|)`.

Writing `Q α x = 1 - 2x cos α + x²` and
`P α n x = x^n (cos((n+1)α) - x cos(nα)) / Q α x`, the proof goes through the
exact telescoping identity `∑_{n≤K} cos(nα)/n = -log(2|sin(α/2)|) - ∫₀¹ P α K x dx`.
-/

namespace Work.FIArea7

open scoped BigOperators

theorem abs_sum_cos_div_le (α : ℝ) (K : ℕ) (hK : 1 ≤ K) (hs : Real.sin (α / 2) ≠ 0) :
    |(∑ n ∈ Finset.Icc 1 K, Real.cos ((n : ℝ) * α) / (n : ℝ))
        + Real.log (2 * |Real.sin (α / 2)|)|
      ≤ 4 / ((K : ℝ) * |Real.sin (α / 2)|) := by
  -- pointwise rewriting of the partial sum as `P α 0 - P α K`
  have hpt : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      (∑ n ∈ Finset.Icc 1 K, x ^ (n - 1) * Real.cos ((n : ℝ) * α)) = P α 0 x - P α K x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    exact P_tele α K x (Q_ne_zero α x hs hx.1 hx.2)
  have hint2 : (∫ x in (0 : ℝ)..1, ∑ n ∈ Finset.Icc 1 K, x ^ (n - 1) * Real.cos ((n : ℝ) * α))
      = ∫ x in (0 : ℝ)..1, (P α 0 x - P α K x) := intervalIntegral.integral_congr hpt
  have hlin : (∫ x in (0 : ℝ)..1, (P α 0 x - P α K x))
      = (∫ x in (0 : ℝ)..1, P α 0 x) - (∫ x in (0 : ℝ)..1, P α K x) := by
    rw [intervalIntegral.integral_sub
      (continuousOn_P α hs 0).intervalIntegrable (continuousOn_P α hs K).intervalIntegrable]
  have hP0eq : (∫ x in (0 : ℝ)..1, P α 0 x)
      = ∫ x in (0 : ℝ)..1, (Real.cos α - x) / Q α x := by
    apply intervalIntegral.integral_congr
    intro x _
    exact P_zero α x
  have hchain : (∑ n ∈ Finset.Icc 1 K, Real.cos ((n : ℝ) * α) / (n : ℝ))
      = -Real.log (2 * |Real.sin (α / 2)|) - ∫ x in (0 : ℝ)..1, P α K x := by
    rw [← integral_sum_cos α K, hint2, hlin, hP0eq, integral_cos_sub_div_Q α hs]
  have hkey : (∑ n ∈ Finset.Icc 1 K, Real.cos ((n : ℝ) * α) / (n : ℝ))
        + Real.log (2 * |Real.sin (α / 2)|)
      = -(∫ x in (0 : ℝ)..1, P α K x) := by
    rw [hchain]; ring
  rw [hkey, abs_neg]
  exact abs_integral_P_le α K hK hs

end Work.FIArea7
