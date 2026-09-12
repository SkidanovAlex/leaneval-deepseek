import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Real

theorem exp_mul_le_of_exp_neg_mul_ge {S α c ε t : ℝ} (hS : 0 < S) (hα : 0 < α) (hc : 0 < c) (hε : 0 < ε) (h : c * ε ≤ Real.exp (-(t * S))) :
    Real.exp (t * S * α) ≤ (1 / c) ^ α * ε ^ (-α) := by
  have hcε : 0 < c * ε := mul_pos hc hε
  -- Take logarithms of the hypothesis.
  have hlog : Real.log (c * ε) ≤ -(t * S) := by
    simpa using Real.log_le_log hcε h
  rw [Real.log_mul hc.ne' hε.ne'] at hlog
  -- Rewrite the logarithms of the reciprocals.
  have hA : Real.log (1 / c) = -Real.log c := by rw [one_div, Real.log_inv]
  have hB : Real.log (1 / ε) = -Real.log ε := by rw [one_div, Real.log_inv]
  have htS : t * S ≤ Real.log (1 / c) + Real.log (1 / ε) := by
    rw [hA, hB]; linarith
  -- Powers as exponentials.
  have hpow1 : (1 / c) ^ α = Real.exp (α * Real.log (1 / c)) := by
    rw [Real.rpow_def_of_pos (one_div_pos.mpr hc), mul_comm]
  have hpow2 : ε ^ (-α) = Real.exp (α * Real.log (1 / ε)) := by
    rw [Real.rpow_def_of_pos hε]
    have : Real.log ε * (-α) = α * Real.log (1 / ε) := by
      rw [hB]; ring
    rw [this]
  have step1 : Real.exp (t * S * α) ≤ Real.exp (α * (Real.log (1 / c) + Real.log (1 / ε))) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left htS hα.le
    nlinarith [this]
  calc Real.exp (t * S * α)
      ≤ Real.exp (α * (Real.log (1 / c) + Real.log (1 / ε))) := step1
    _ = Real.exp (α * Real.log (1 / c) + α * Real.log (1 / ε)) := by rw [mul_add]
    _ = Real.exp (α * Real.log (1 / c)) * Real.exp (α * Real.log (1 / ε)) := by
          rw [Real.exp_add]
    _ = (1 / c) ^ α * ε ^ (-α) := by rw [← hpow1, ← hpow2]

end Commons.Analysis.Real