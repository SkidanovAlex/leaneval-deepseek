import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_fe_expanded
import Submission.Commons.NumberTheory.Zeta.zeta1_ne_zero_re_neg_one_le_zero

open scoped Topology

namespace Commons.NumberTheory.Zeta

theorem logDeriv_riemannZeta_neg_one :
    logDeriv riemannZeta (-1) =
      ((Real.log (2 * Real.pi) - 1 + Real.eulerMascheroniConstant : ℝ) : ℂ)
        + ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((n : ℂ) ^ 2) := by
  have hζs : riemannZeta (-1 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_re_neg_one_le_zero (by norm_num) (by norm_num)
  have hζw : riemannZeta (1 - (-1 : ℂ)) ≠ 0 := by
    have h : (1 : ℂ) - (-1) = 2 := by norm_num
    rw [h]
    exact riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hΓ : ∀ n : ℕ, (1 : ℂ) - (-1) ≠ -(n : ℂ) := by
    intro n hn
    have h : (1 : ℂ) - (-1) = 2 := by norm_num
    rw [h] at hn
    have hre := congrArg Complex.re hn
    simp at hre
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hcos : Complex.cos (↑Real.pi * (1 - (-1 : ℂ)) / 2) ≠ 0 := by
    have h : (1 : ℂ) - (-1) = 2 := by norm_num
    rw [h, show (↑Real.pi : ℂ) * 2 / 2 = ↑Real.pi by ring, ← Complex.ofReal_cos, Real.cos_pi]
    norm_num
  have hfe := zeta_logDeriv_fe_expanded (s := (-1 : ℂ)) hζs hζw (by norm_num) (by norm_num) hΓ hcos
  rw [logDeriv_apply, hfe]
  rw [show (1 : ℂ) - (-1) = 2 from by norm_num]
  have hlog : Complex.log ((2 * Real.pi : ℝ) : ℂ) = ((Real.log (2 * Real.pi) : ℝ) : ℂ) :=
    (Complex.ofReal_log (x := 2 * Real.pi) (by positivity)).symm
  have hdig : Complex.digamma (2 : ℂ) =
      ((1 - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
    have h2 : (2 : ℂ) = 1 + 1 := by norm_num
    rw [h2, Complex.digamma_apply_add_one (1 : ℂ) (by
      intro m h
      have hre : (1 : ℝ) = -(m : ℝ) := by
        have := congrArg Complex.re h
        simpa using this
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith), Complex.digamma_one]
    push_cast
    ring
  have htan : Complex.tan ((↑Real.pi : ℂ) * 2 / 2) = 0 := by
    rw [show (↑Real.pi : ℂ) * 2 / 2 = ↑Real.pi by ring, ← Complex.ofReal_tan, Real.tan_pi]
    norm_num
  have hLsum : LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) 2 =
      ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((n : ℂ) ^ 2) := by
    rw [LSeries]
    refine tsum_congr (fun n => ?_)
    rw [LSeries.term_def]
    by_cases hn : n = 0
    · subst hn; simp
    · rw [if_neg hn]
      congr 1
      exact Complex.cpow_natCast (n : ℂ) 2
  have hL2 : deriv riemannZeta (2 : ℂ) / riemannZeta (2 : ℂ) =
      -∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((n : ℂ) ^ 2) := by
    have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (s := (2 : ℂ)) (by norm_num)
    rw [hLsum] at h
    linear_combination h
  rw [hlog, hdig, htan, hL2]
  push_cast
  ring

end Commons.NumberTheory.Zeta
