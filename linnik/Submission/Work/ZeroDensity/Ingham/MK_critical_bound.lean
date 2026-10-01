import Mathlib
import Submission.Work.ZeroDensity.Ingham.Defs
import Submission.Work.Sieve.sum_Icc_rpow_neg_half_le

namespace Work.ZeroDensity.Ingham

open scoped BigOperators

/-- Termwise bound for the summands of `M_K(s)`: for `n ≥ 1` and `Re s ≥ 1/2`,
`‖μ(n) n^{-s}‖ ≤ n^{-1/2}`. -/
private lemma norm_moebius_mul_cpow_le (n : ℕ) (s : ℂ) (hn : 1 ≤ n) (hs : 1 / 2 ≤ s.re) :
    ‖(ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)‖ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hn0 : (0 : ℕ) < n := by omega
  rw [norm_mul]
  have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  have hle : ‖(n : ℂ) ^ (-s)‖ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
  calc ‖(ArithmeticFunction.moebius n : ℂ)‖ * ‖(n : ℂ) ^ (-s)‖
      ≤ 1 * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul hmu hle (norm_nonneg _) (by norm_num)
    _ = (n : ℝ) ^ (-(1 / 2 : ℝ)) := one_mul _

/-- The truncated Möbius polynomial `M_K(s) = Σ_{n≤K} μ(n) n^{-s}` is bounded on any half-plane
`Re s ≥ 1/2` by `2√K`: since `|μ(n)| ≤ 1` and `‖n^{-s}‖ = n^{-Re s} ≤ n^{-1/2}`, the sum is at most
`Σ_{n=1}^K n^{-1/2} ≤ 1 + ∫_1^K x^{-1/2} dx = 2√K - 1 ≤ 2√K`. -/
theorem MK_critical_bound (K : ℕ) (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    ‖MK K s‖ ≤ 2 * Real.sqrt K := by
  rw [MK]
  calc ‖∑ n ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)‖
      ≤ ∑ n ∈ Finset.Icc 1 K,
          ‖(ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Finset.sum_le_sum fun n hn =>
          norm_moebius_mul_cpow_le n s (Finset.mem_Icc.mp hn).1 hs
    _ = ∑ n ∈ Finset.Icc 1 K, Real.sqrt (n : ℝ) / (n : ℝ) :=
        Finset.sum_congr rfl fun n hn =>
          Work.Sieve.rpow_neg_half_eq_sqrt_div n (Finset.mem_Icc.mp hn).1
    _ ≤ 2 * Real.sqrt K := Work.Commons.Analysis.Series.sum_Icc_sqrt_div_self_le K

end Work.ZeroDensity.Ingham
