import Mathlib
import Submission.Work.Commons.Analysis.Series.sum_Icc_sqrt_div_self_le

namespace Work.Sieve

/-- For `n ≥ 1` the real power `n ^ (-(1/2))` agrees with `√n / n` (equivalently `1/√n`). -/
lemma rpow_neg_half_eq_sqrt_div (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ (-(1/2 : ℝ)) = Real.sqrt (n : ℝ) / (n : ℝ) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hsqn : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = (n:ℝ) := by
    rw [← pow_two]; exact Real.sq_sqrt (le_of_lt hnpos)
  have hrpow : (n:ℝ) ^ (-(1/2:ℝ)) = (Real.sqrt (n:ℝ))⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hnpos), ← Real.sqrt_eq_rpow]
  have hdiv : Real.sqrt (n:ℝ) / (n:ℝ) = (Real.sqrt (n:ℝ))⁻¹ := by
    have hsne : Real.sqrt (n:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnpos)
    field_simp
    rw [pow_two]
    exact hsqn
  rw [hrpow, hdiv]

theorem sum_Icc_rpow_neg_half_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1/2 : ℝ)) ≤ 2 * (((N : ℝ) + 1) ^ (1/2 : ℝ)) := by
  have hcongr : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1/2 : ℝ))
      = ∑ n ∈ Finset.Icc 1 N, Real.sqrt (n : ℝ) / (n : ℝ) :=
    Finset.sum_congr rfl fun n hn => rpow_neg_half_eq_sqrt_div n (Finset.mem_Icc.mp hn).1
  rw [hcongr]
  calc ∑ n ∈ Finset.Icc 1 N, Real.sqrt (n:ℝ)/(n:ℝ)
      ≤ 2*Real.sqrt (N:ℝ) := Work.Commons.Analysis.Series.sum_Icc_sqrt_div_self_le N
    _ ≤ 2*(((N:ℝ)+1)^(1/2:ℝ)) := by
        rw [Real.sqrt_eq_rpow]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)

end Work.Sieve
