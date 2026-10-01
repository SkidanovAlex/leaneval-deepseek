import Mathlib
import Submission.Commons.Analysis.ExpLog.log_le_rpow_div

namespace Commons.Analysis.Real

/-- Any fixed power of `log x` is dominated by `x ^ ε` for `ε > 0`. -/
theorem log_pow_le_mul_rpow {ε : ℝ} (hε : 0 < ε) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → (Real.log x) ^ A ≤ C * x ^ ε := by
  rcases Nat.eq_zero_or_pos A with hA0 | hA
  · -- A = 0: take C = 1
    subst hA0
    refine ⟨1, one_pos, fun x hx => ?_⟩
    rw [pow_zero, one_mul]
    exact Real.one_le_rpow hx (le_of_lt hε)
  · -- A ≥ 1: take C = (A/ε)^A and compare logs
    have hApos : 0 < (A : ℝ) := by exact_mod_cast hA
    have hAne : (A : ℝ) ≠ 0 := hApos.ne'
    refine ⟨((A : ℝ) / ε) ^ A, pow_pos (div_pos hApos hε) A, fun x hx => ?_⟩
    have hxpos : 0 < x := lt_of_lt_of_le one_pos hx
    have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx
    have ha : 0 < ε / (A : ℝ) := div_pos hε hApos
    have hlog : Real.log x ≤ x ^ (ε / (A : ℝ)) / (ε / (A : ℝ)) :=
      Commons.Analysis.ExpLog.log_le_rpow_div hx ha
    calc (Real.log x) ^ A
        ≤ (x ^ (ε / (A : ℝ)) / (ε / (A : ℝ))) ^ A :=
          pow_le_pow_left₀ hlog_nonneg hlog A
      _ = ((A : ℝ) / ε) ^ A * (x ^ (ε / (A : ℝ))) ^ A := by
          rw [div_eq_mul_inv, inv_div, mul_pow, mul_comm]
      _ = ((A : ℝ) / ε) ^ A * (x ^ (ε / (A : ℝ))) ^ (A : ℝ) := by
          rw [Real.rpow_natCast]
      _ = ((A : ℝ) / ε) ^ A * x ^ ((ε / (A : ℝ)) * (A : ℝ)) := by
          rw [Real.rpow_mul (le_of_lt hxpos)]
      _ = ((A : ℝ) / ε) ^ A * x ^ ε := by
          rw [div_mul_cancel₀ ε hAne]

end Commons.Analysis.Real
