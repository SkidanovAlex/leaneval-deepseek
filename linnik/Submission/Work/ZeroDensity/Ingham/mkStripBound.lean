import Mathlib
import Submission.Work.ZeroDensity.Ingham.perronIntDeps

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators

/-- Each summand `μ(n) n^{-s}` of `M_K(s)` has norm at most `n^3` when `-3 ≤ Re s`. Indeed
`‖μ(n) n^{-s}‖ ≤ n^{-Re s} = n^{-s.re}` and `n^{-s.re} ≤ n^3` for `n ≥ 1`. -/
private lemma norm_moebius_mul_cpow_le (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hs : -3 ≤ s.re) :
    ‖(ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)‖ ≤ (n : ℝ) ^ 3 := by
  have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    by_cases h : Squarefree n
    · rw [ArithmeticFunction.moebius_apply_of_squarefree h]; norm_num
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]; norm_num
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnorm : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s).re := by
    have : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
    rw [this, Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
  have hexp : (-s).re ≤ 3 := by simp only [Complex.neg_re]; linarith
  have h2 : (n : ℝ) ^ (-s).re ≤ (n : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast (n : ℝ) 3]
    exact Real.rpow_le_rpow_of_exponent_le (x := (n : ℝ))
      (by exact_mod_cast hn : (1 : ℝ) ≤ (n : ℝ)) hexp
  rw [norm_mul, hnorm]
  calc ‖(ArithmeticFunction.moebius n : ℂ)‖ * (n : ℝ) ^ (-s).re
      ≤ 1 * (n : ℝ) ^ (-s).re :=
        mul_le_mul_of_nonneg_right hmu (Real.rpow_nonneg (by positivity) _)
    _ = (n : ℝ) ^ (-s).re := one_mul _
    _ ≤ (n : ℝ) ^ 3 := h2

theorem mkStripBound (K : ℕ) {s : ℂ} (hs : -3 ≤ s.re) :
    ‖MK K s‖ ≤ ∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ 3 := by
  rw [MK_apply]
  refine le_trans (norm_sum_le _ _) ?_
  exact Finset.sum_le_sum fun n hn =>
    norm_moebius_mul_cpow_le n (Finset.mem_Icc.mp hn).1 s hs

end Work.ZeroDensity.Ingham
