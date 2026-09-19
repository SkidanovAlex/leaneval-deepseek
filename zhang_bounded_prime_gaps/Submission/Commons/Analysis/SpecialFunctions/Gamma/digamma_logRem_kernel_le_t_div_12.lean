import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_kernelIntegral

open Real Set MeasureTheory Filter
open scoped Real Topology

namespace Commons.Analysis.SpecialFunctions.Gamma

-- ============================================================
-- pointwise bound  K(t) = 1/(e^t-1) - 1/t + 1/2  ≤  t/12   (t > 0)
-- ============================================================

private lemma exp_gt_one_of_pos {t : ℝ} (ht : 0 < t) : 1 < Real.exp t := by
  simpa using (Real.exp_strictMono ht)

private lemma exp_sub_one_pos {t : ℝ} (ht : 0 < t) : 0 < Real.exp t - 1 := by
  linarith [exp_gt_one_of_pos ht]

private lemma exp_sub_one_ne_zero {t : ℝ} (ht : 0 < t) : Real.exp t - 1 ≠ 0 :=
  ne_of_gt (exp_sub_one_pos ht)

/-- `e^t·(t²−6t+12) − (t²+6t+12) ≥ 0` for `t ≥ 0`.
This is the numerator obtained by multiplying the desired inequality by
the positive number `12·t·(e^t−1)`. -/
private lemma psi_nonneg (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ Real.exp t * (t ^ 2 - 6 * t + 12) - (t ^ 2 + 6 * t + 12) := by
  let S : ℝ := ∑ i ∈ Finset.range 6, t ^ i / (i.factorial : ℝ)
  have hS : S = 1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 + t ^ 5 / 120 := by
    dsimp [S]
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hSum : S ≤ Real.exp t := by
    dsimp [S]
    exact Real.sum_le_exp_of_nonneg ht 6
  have hA : 0 ≤ t ^ 2 - 6 * t + 12 := by
    have hsq : 0 ≤ (t - 3) ^ 2 := sq_nonneg (t - 3)
    nlinarith
  have hdiff1 : 0 ≤ (t ^ 2 - 6 * t + 12) * (Real.exp t - S) :=
    mul_nonneg hA (sub_nonneg.mpr hSum)
  have hquad : 0 ≤ t ^ 2 - t + 2 := by
    have hsq : 0 ≤ (t - 1 / 2) ^ 2 := sq_nonneg (t - 1 / 2)
    nlinarith
  have hRest : 0 ≤ (t ^ 2 - 6 * t + 12) * S - (t ^ 2 + 6 * t + 12) := by
    have hEq : (t ^ 2 - 6 * t + 12) * S - (t ^ 2 + 6 * t + 12) =
        t ^ 5 * (t ^ 2 - t + 2) / 120 := by
      rw [hS]
      ring
    rw [hEq]
    have hnum : 0 ≤ t ^ 5 * (t ^ 2 - t + 2) :=
      mul_nonneg (pow_nonneg ht 5) hquad
    exact div_nonneg hnum (by norm_num)
  have hEqψ : Real.exp t * (t ^ 2 - 6 * t + 12) - (t ^ 2 + 6 * t + 12) =
      (t ^ 2 - 6 * t + 12) * (Real.exp t - S) +
        ((t ^ 2 - 6 * t + 12) * S - (t ^ 2 + 6 * t + 12)) := by
    ring
  rw [hEqψ]
  exact add_nonneg hdiff1 hRest

/-- `K(t) ≤ t/12` for `t > 0` where `K(t) = 1/(e^t-1) - 1/t + 1/2`. -/
private lemma kernel_le_t_div_12 (t : ℝ) (ht : 0 < t) :
    1 / (Real.exp t - 1) - 1 / t + 1 / 2 ≤ t / 12 := by
  have hψ : 0 ≤ Real.exp t * (t ^ 2 - 6 * t + 12) - (t ^ 2 + 6 * t + 12) :=
    psi_nonneg t (le_of_lt ht)
  have hden : 0 < 12 * t * (Real.exp t - 1) :=
    mul_pos (mul_pos (by norm_num) ht) (exp_sub_one_pos ht)
  have hEq : t / 12 - (1 / (Real.exp t - 1) - 1 / t + 1 / 2) =
      (Real.exp t * (t ^ 2 - 6 * t + 12) - (t ^ 2 + 6 * t + 12)) /
        (12 * t * (Real.exp t - 1)) := by
    field_simp [ht.ne', exp_sub_one_ne_zero ht]
    ring
  have hd : 0 ≤ t / 12 - (1 / (Real.exp t - 1) - 1 / t + 1 / 2) := by
    rw [hEq]
    exact div_nonneg hψ (le_of_lt hden)
  linarith

theorem digamma_logRem_kernel_le_t_div_12 (t : ℝ) (ht : 0 < t) :
    1 / (Real.exp t - 1) - 1 / t + 1 / 2 ≤ t / 12 := by
  exact kernel_le_t_div_12 t ht

end Commons.Analysis.SpecialFunctions.Gamma
