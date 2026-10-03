import Mathlib
import Submission.Work.FIArea6Hecke.R.norm_logDeriv_one_sub_mul_cpow_le

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

/-- The Euler factor `c · (p : ℂ)^{-s}` is small in the half plane `1 < re s`. -/
lemma norm_mul_cpow_neg_le_half {c : ℂ} {p : ℕ} {s : ℂ} (hp : 2 ≤ p) (hc : ‖c‖ ≤ 1)
    (hs : 1 < s.re) : ‖c * (p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hp1 : (1 : ℝ) < (p : ℝ) := by linarith
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s).re := by
    rw [← Complex.ofReal_natCast]
    exact Complex.norm_cpow_eq_rpow_re_of_pos hp0 (-s)
  have hre : (-s).re = -s.re := by simp
  have hb : (p : ℝ) ^ (-s).re ≤ 1 / 2 := by
    rw [hre]
    have hlt : (p : ℝ) ^ (-s.re) < (p : ℝ) ^ ((-1 : ℝ)) := by
      rw [Real.rpow_lt_rpow_left_iff hp1]
      linarith
    rw [Real.rpow_neg_one] at hlt
    have hinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div, div_le_div_iff₀ hp0 (by norm_num)]
      linarith
    linarith
  calc ‖c * (p : ℂ) ^ (-s)‖ = ‖c‖ * ‖(p : ℂ) ^ (-s)‖ := norm_mul _ _
    _ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ = ‖(p : ℂ) ^ (-s)‖ := one_mul _
    _ = (p : ℝ) ^ (-s).re := hnorm
    _ ≤ 1 / 2 := hb

theorem AxisFactorLogDerivNormLe {c : ℂ} {p : ℕ} {s : ℂ} (hp : 2 ≤ p)
    (hc : ‖c‖ ≤ 1) (hs : 1 < s.re) :
    ‖logDeriv (fun u : ℂ => (1 : ℂ) - c * (p : ℂ) ^ (-u)) s‖ ≤ (4 / 3) * Real.log (p : ℝ) := by
  exact norm_logDeriv_one_sub_mul_cpow_le hp (Or.inl (norm_mul_cpow_neg_le_half hp hc hs))

end Work.FIArea6Hecke.R
