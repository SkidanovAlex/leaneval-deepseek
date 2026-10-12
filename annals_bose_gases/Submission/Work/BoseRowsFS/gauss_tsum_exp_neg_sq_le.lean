import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Gaussian theta sum is bounded by `1 + 1/c`

For `c > 0`, `∑' n : ℕ, exp (-(c^2 * n^2)) ≤ 1 + 1/c`.

The `n = 0` term contributes exactly `1`.  The remaining terms are bounded by the
half-line Gaussian integral via the integral test for antitone functions
(`AntitoneOn.tsum_le_integral`):
`∑_{n ≥ 1} exp (-(c^2 n^2)) ≤ ∫_0^∞ exp (-(c^2 x^2)) dx = √(π/c^2)/2 = √π/(2c) ≤ 1/c`,
the last step because `√π ≤ 2` (from `π ≤ 4`).
-/

open MeasureTheory

namespace Work.BoseRowsFS

theorem gauss_tsum_exp_neg_sq_le {c : ℝ} (hc : 0 < c) :
    (∑' n : ℕ, Real.exp (-(c ^ 2 * (n : ℝ) ^ 2))) ≤ 1 + 1 / c := by
  -- the summand is antitone on `[0, ∞)`
  have hanti : AntitoneOn (fun x : ℝ => Real.exp (-(c ^ 2 * x ^ 2))) (Set.Ici 0) := by
    intro x hx y hy hxy
    apply Real.exp_le_exp.mpr
    have hx2 : x ^ 2 ≤ y ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg hy hx), sq_nonneg (y - x)]
    nlinarith [mul_le_mul_of_nonneg_left hx2 (by positivity : (0 : ℝ) ≤ c ^ 2)]
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-(c ^ 2 * x ^ 2))) (Set.Ioi 0) := by
    have h := (integrableOn_Ioi_exp_neg_mul_sq_iff (b := c ^ 2)).mpr (by positivity : (0 : ℝ) < c ^ 2)
    simpa only [neg_mul] using h
  have hnonneg : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ Real.exp (-(c ^ 2 * t ^ 2)) :=
    fun t _ => Real.exp_nonneg _
  -- integral test: the series is bounded by its zeroth term plus the integral
  have hmain := hanti.tsum_le_integral hint hnonneg
  have hInt : ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(c ^ 2 * x ^ 2)) =
      Real.sqrt (Real.pi / c ^ 2) / 2 := by
    simpa only [neg_mul] using integral_gaussian_Ioi (c ^ 2)
  have hInt_le : ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(c ^ 2 * x ^ 2)) ≤ 1 / c := by
    rw [hInt]
    have hsqrt : Real.sqrt (Real.pi / c ^ 2) ≤ 2 / c := by
      rw [Real.sqrt_div Real.pi_pos.le (c ^ 2), Real.sqrt_sq hc.le]
      have h2 : Real.sqrt Real.pi ≤ 2 := by
        have h := Real.sqrt_le_sqrt Real.pi_le_four
        have h4 : Real.sqrt (4 : ℝ) = 2 := by norm_num [Real.sqrt_sq]
        linarith [h4 ▸ h]
      exact div_le_div_of_nonneg_right h2 hc.le
    have step : Real.sqrt (Real.pi / c ^ 2) / 2 ≤ (2 / c) / 2 :=
      div_le_div_of_nonneg_right hsqrt (by norm_num)
    have h2 : (2 / c) / 2 = 1 / c := by field_simp
    linarith
  have hf0 : Real.exp (-(c ^ 2 * (0 : ℝ) ^ 2)) = 1 := by norm_num
  calc (∑' n : ℕ, Real.exp (-(c ^ 2 * (n : ℝ) ^ 2)))
      ≤ Real.exp (-(c ^ 2 * (0 : ℝ) ^ 2)) +
          ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(c ^ 2 * x ^ 2)) := hmain
    _ ≤ 1 + 1 / c := by rw [hf0]; linarith

end Work.BoseRowsFS
