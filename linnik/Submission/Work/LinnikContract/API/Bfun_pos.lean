import Mathlib
import Submission.Work.LinnikContract.Pre

namespace Work.LinnikContract.API

/-- HB's per-character constant `B(λ)` is strictly positive for `K > 0`, `λ > 0`.
The `else` branch of `Bfun` is the two-term expression of `Commons…Linnik.linnikB_nonneg`
(non-negative); strict positivity comes from the first term:
`1 - e^{-2Kλ} > 0` since `2Kλ > 0`, while the denominator `6K²λ > 0`.
(Equivalently: `t - 1 + e^{-t} > 0` for `t = 2Kλ > 0` for the second term.)
No `native_decide`. -/
theorem Bfun_pos {K lam : ℝ} (hK : 0 < K) (hlam : 0 < lam) : 0 < Work.LinnikContract.Bfun K lam := by
  have hlamne : lam ≠ 0 := ne_of_gt hlam
  rw [Work.LinnikContract.Bfun, if_neg hlamne]
  -- `2Kλ > 0`, so both denominators are strictly positive.
  have htpos : 0 < 2 * K * lam := by positivity
  have hden1 : 0 < 6 * K ^ 2 * lam := by positivity
  have hden2 : 0 < 2 * K ^ 2 * lam ^ 2 := by positivity
  -- First numerator: `1 - e^{-2Kλ} > 0` since `e^{-2Kλ} < 1` (`-2Kλ < 0`).
  have hexp_lt : Real.exp (-2 * K * lam) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hnum1 : 0 < 1 - Real.exp (-2 * K * lam) := by linarith
  have hf1 : 0 < (1 - Real.exp (-2 * K * lam)) / (6 * K ^ 2 * lam) := div_pos hnum1 hden1
  -- Second numerator: `2Kλ - 1 + e^{-2Kλ} ≥ 0` (from the elementary bound `1 - e^{-t} ≤ t`).
  have hb := Commons.NumberTheory.Linnik.exp_neg_bounds (2 * K * lam) (le_of_lt htpos)
  have hB0 : 0 ≤ 2 * K * lam - 1 + Real.exp (-2 * K * lam) := by
    have harg : -2 * K * lam = -(2 * K * lam) := by ring
    rw [harg]
    linarith [hb.2.1]
  have hf2 : 0 ≤ (2 * K * lam - 1 + Real.exp (-2 * K * lam)) / (2 * K ^ 2 * lam ^ 2) :=
    div_nonneg hB0 (le_of_lt hden2)
  linarith

end Work.LinnikContract.API
