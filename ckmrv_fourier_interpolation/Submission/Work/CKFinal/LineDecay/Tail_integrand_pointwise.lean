import Mathlib
import Submission.Work.CKFinal.LineDecay.rpow_le_mul_rpow_abs
import Submission.Work.CKFinal.LineDecay.exp_frac_le_exp_neg_abs

namespace Work.CKFinal.LineDecay

/-- **Pointwise majorant for the tail integrand.**

For `A : ℝ` and `y, t ≥ 1`,
`(1+t)^A e^{-πt}/(1 + e^{2π(y-t)}) ≤ (1+y)^A (1+|t-y|)^{|A|} e^{-π|t-y|} e^{-πy}`.

The exponential factor `e^{-πt}/(1 + e^{2π(y-t)})` is at most `e^{-π|t-y|} e^{-πy}`
(`exp_frac_le_exp_neg_abs`), while the power factor `(1+t)^A` is dominated by
`(1+y)^A (1+|t-y|)^{|A|}` because `1 + t ≤ (1+y)(1+|t-y|)` and
`1 + y ≤ (1+t)(1+|t-y|)` (`rpow_le_mul_rpow_abs`).  Multiplying the two bounds
gives the claim. -/
lemma Tail_integrand_pointwise (A y t : ℝ) (hy : 1 ≤ y) (ht : 1 ≤ t) : (1 + t) ^ A * (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t)))) ≤ (1 + y) ^ A * ((1 + |t - y|) ^ |A| * Real.exp (-(Real.pi * |t - y|))) * Real.exp (-(Real.pi * y)) := by
  have ha : 0 < 1 + t := by linarith
  have hb : 0 < 1 + y := by linarith
  have hc : 0 < 1 + |t - y| := by positivity
  -- Base inequality `1 + t ≤ (1 + y) * (1 + |t - y|)`.
  have habc : 1 + t ≤ (1 + y) * (1 + |t - y|) := by
    have h1 : t - y ≤ |t - y| := le_abs_self _
    have h2 : (0 : ℝ) ≤ |t - y| := abs_nonneg _
    nlinarith [hy, ht, h1, h2]
  -- Base inequality `1 + y ≤ (1 + t) * (1 + |t - y|)`.
  have hbac : 1 + y ≤ (1 + t) * (1 + |t - y|) := by
    have h1 : y - t ≤ |t - y| := by have := neg_le_abs (t - y); linarith
    have h2 : (0 : ℝ) ≤ |t - y| := abs_nonneg _
    nlinarith [hy, ht, h1, h2]
  have hrpow := rpow_le_mul_rpow_abs (1 + t) (1 + y) (1 + |t - y|) A ha hb hc habc hbac
  have hfrac := exp_frac_le_exp_neg_abs y t
  have hbnn : 0 ≤ (1 + y) ^ A * (1 + |t - y|) ^ |A| :=
    le_of_lt (mul_pos (Real.rpow_pos_of_pos hb A) (Real.rpow_pos_of_pos hc |A|))
  have hcnn : 0 ≤ Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t))) :=
    div_nonneg (le_of_lt (Real.exp_pos _)) (add_nonneg zero_le_one (le_of_lt (Real.exp_pos _)))
  calc (1 + t) ^ A * (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t))))
      ≤ ((1 + y) ^ A * (1 + |t - y|) ^ |A|) * (Real.exp (-(Real.pi * |t - y|)) * Real.exp (-(Real.pi * y))) :=
        mul_le_mul hrpow hfrac hcnn hbnn
    _ = (1 + y) ^ A * ((1 + |t - y|) ^ |A| * Real.exp (-(Real.pi * |t - y|))) * Real.exp (-(Real.pi * y)) := by
        ac_rfl

end Work.CKFinal.LineDecay
