import Mathlib

namespace Work.TMComp.MAnalytic

/-- Exponential decay `exp (-(a * |k|))` is summable over `ℤ` for `a > 0`. -/
theorem summable_int_exp_neg_abs (B a : ℝ) (ha : 0 < a) :
    Summable (fun k : ℤ => B * Real.exp (-(a * |(k : ℝ)|))) := by
  have hpos : Summable (fun n : ℕ => Real.exp (-(a * (n : ℝ)))) := by
    have h := Real.summable_exp_nat_mul_iff.mpr (show (-a : ℝ) < 0 by linarith)
    convert h using 2 with n
    ring_nf
  rw [summable_int_iff_summable_nat_and_neg]
  exact ⟨by simpa using hpos.mul_left B, by simpa using hpos.mul_left B⟩

end Work.TMComp.MAnalytic
