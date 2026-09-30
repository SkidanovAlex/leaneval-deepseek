import Mathlib
import Submission.Work.BMF.liouville.prime_power_twist_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

/-- For `2 ≤ p` and `2 ≤ k`, the correction term `corr u (p^k)` is at most `p^{-k}` in modulus.
Since `p^k` is never prime (so the prime-indicator term vanishes) and `Λ (p^k) ≤ log (p^k)`,
`corr u (p^k) = (Λ (p^k)/log (p^k)) · (p^k)^{z}` with `z = -1 - i·u`, whose modulus is
`(Λ (p^k)/log (p^k)) · p^{-k} ≤ p^{-k}`. -/
theorem norm_corr_pow_le (u : ℝ) (p k : ℕ) (hp : 2 ≤ p) (hk : 2 ≤ k) :
    ‖corr u (p ^ k)‖ ≤ (((p : ℝ))⁻¹) ^ k := by
  have hpk_ge2 : 2 ≤ p ^ k := by
    calc 2 ≤ p := hp
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ k)
  have hlog_pos : 0 < Real.log (((p ^ k : ℕ) : ℝ)) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < p ^ k))
  -- `p ^ k` is never prime when `2 ≤ k`, so the prime-indicator term vanishes.
  have hcorr : corr u (p ^ k)
      = ((ArithmeticFunction.vonMangoldt (p ^ k) : ℝ) : ℂ)
          / ((Real.log (((p ^ k : ℕ) : ℝ))) : ℂ)
          * (((p ^ k : ℕ)) : ℂ) ^ twistZ u := by
    unfold corr
    rw [ite_eq_right (Nat.Prime.not_prime_pow hk), sub_zero]
  rw [hcorr, norm_mul]
  -- The von Mangoldt coefficient is bounded by `1`.
  have hcoef : ‖((ArithmeticFunction.vonMangoldt (p ^ k) : ℝ) : ℂ)
      / ((Real.log (((p ^ k : ℕ) : ℝ))) : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, abs_of_pos hlog_pos]
    exact (div_le_one hlog_pos).mpr ArithmeticFunction.vonMangoldt_le_log
  -- The complex power has modulus exactly `p^{-k}`.
  have hnorm : ‖((p ^ k : ℕ) : ℂ) ^ twistZ u‖ = (((p : ℝ))⁻¹) ^ k := by
    rw [← Complex.ofReal_natCast (p ^ k)]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (x := ((p ^ k : ℕ) : ℝ)) (by
      rw [Nat.cast_pow]; exact pow_pos (by exact_mod_cast (by omega : 0 < p)) k)]
    have hre : (twistZ u).re = -1 := by simp [twistZ]
    rw [hre, Real.rpow_neg_one, Nat.cast_pow, inv_pow]
  calc ‖((ArithmeticFunction.vonMangoldt (p ^ k) : ℝ) : ℂ)
          / ((Real.log (((p ^ k : ℕ) : ℝ))) : ℂ)‖
        * ‖((p ^ k : ℕ) : ℂ) ^ twistZ u‖
      ≤ 1 * ((((p : ℝ))⁻¹) ^ k) := by
        rw [hnorm]
        exact mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = (((p : ℝ))⁻¹) ^ k := one_mul _

end Work.BMF.liouville
