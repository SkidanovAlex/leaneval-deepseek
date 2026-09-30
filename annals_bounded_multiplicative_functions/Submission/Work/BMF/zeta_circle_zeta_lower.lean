import Mathlib
import Submission.Work.BMF.zeta_tsum_rpow_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped LSeries.notation
open ArithmeticFunction

namespace Work.BMF

/-- Norm bound for the L-series of the Möbius function: for `1 < s.re` it is dominated by the
real `p`-series `∑ n^{-re s}`.  Indeed `L ↗μ s = ∑_n μ(n)/n^s`, and the `n`-th summand has
norm `|μ n| / n^{re s} ≤ 1 / n^{re s} = n^{-re s}` because `|μ n| ≤ 1`. -/
theorem moebius_LSeries_norm_le {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries (↗moebius) s‖ ≤ ∑' (n : ℕ), (n : ℝ) ^ (-s.re) := by
  have hsumm : Summable (LSeries.term (↗moebius) s) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have h1 : ‖LSeries (↗moebius) s‖ ≤ ∑' n, ‖LSeries.term (↗moebius) s n‖ :=
    norm_tsum_le_tsum_norm hsumm.norm
  have hterm : ∀ n, ‖LSeries.term (↗moebius) s n‖ ≤ (n : ℝ) ^ (-s.re) := by
    intro n
    rw [LSeries.norm_term_eq, Real.rpow_neg (Nat.cast_nonneg n)]
    rcases eq_or_ne n 0 with rfl | hn
    · rw [ite_eq_left rfl]
      have h0 : (0 : ℝ) ^ s.re = 0 := Real.zero_rpow (by linarith : s.re ≠ 0)
      simp [h0]
    · rw [ite_eq_right hn, div_eq_mul_inv]
      have hμ : ‖((moebius n : ℤ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
      have hnonneg : 0 ≤ (((n : ℝ)) ^ s.re)⁻¹ :=
        inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      calc ‖((moebius n : ℤ) : ℂ)‖ * (((n : ℝ)) ^ s.re)⁻¹ ≤ 1 * (((n : ℝ)) ^ s.re)⁻¹ :=
            mul_le_mul_of_nonneg_right hμ hnonneg
        _ = (((n : ℝ)) ^ s.re)⁻¹ := one_mul _
  have h2 : ∑' n, ‖LSeries.term (↗moebius) s n‖ ≤ ∑' (n : ℕ), (n : ℝ) ^ (-s.re) :=
    Summable.tsum_le_tsum hterm hsumm.norm (Real.summable_nat_rpow.mpr (by linarith))
  exact le_trans h1 h2

/-- Lower bound for `‖ζ s‖` to the right of the critical line: for `1 < s.re`,
`‖ζ s‖ ≥ 1 / (1 + 1/(s.re - 1))`, i.e. `-log ‖ζ s‖ ≤ log (1 + 1/(s.re - 1))`.

The proof goes through the Dirichlet series of `1/ζ`:
`1/ζ(s) = ∑_n μ(n) n^{-s}` for `1 < s.re`, so
`1/‖ζ s‖ = ‖1/ζ(s)‖ ≤ ∑_n |μ(n)| n^{-re s} ≤ ∑_n n^{-re s} = ζ(re s) ≤ 1 + 1/(re s - 1)`,
the last bound being the elementary integral-test estimate for the real `p`-series. -/
theorem zeta_circle_zeta_lower {s : ℂ} (hs : 1 < s.re) :
    -Real.log ‖riemannZeta s‖ ≤ Real.log (1 + 1 / (s.re - 1)) := by
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  -- `1/ζ(s)` is the L-series of the Möbius function
  have hinv : LSeries (↗moebius) s = (riemannZeta s)⁻¹ := by
    have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
    rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at h
    exact eq_inv_of_mul_eq_one_right h
  have hnorm : ‖riemannZeta s‖⁻¹ ≤ 1 + 1 / (s.re - 1) := by
    calc ‖riemannZeta s‖⁻¹ = ‖(riemannZeta s)⁻¹‖ := (norm_inv _).symm
      _ = ‖LSeries (↗moebius) s‖ := by rw [hinv]
      _ ≤ ∑' (n : ℕ), (n : ℝ) ^ (-s.re) := moebius_LSeries_norm_le hs
      _ ≤ 1 + 1 / (s.re - 1) := zeta_tsum_rpow_le hs
  rw [← Real.log_inv]
  exact Real.log_le_log (inv_pos.mpr (norm_pos_iff.mpr hζ)) hnorm

end Work.BMF
