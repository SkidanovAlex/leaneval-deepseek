import Mathlib
import Submission.Work.BW.ulcm_le_three_pow
import Submission.Work.BW.log_concavity_floor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- **Concavity bound for one Sylvester block.**  For `n ≥ 1` and any `i`, writing
`m = ⌊n / syl i⌋` (`syl` Sylvester's sequence from `Submission/Work/BW/ulcm_le_three_pow.lean`),
`m log n - m log (syl i) - n/syl i ≤ m log m - m` (all divisions of `ℝ`'s).

Route.  If `m = 0` both sides reduce: the left side is `-n/syl i ≤ 0` and `0 * Real.log 0 = 0`
(`Real.log_zero`) so the right side is `0`.  If `m ≥ 1`: `m ≤ n/syl i` (`Nat.cast_div_le`) and
`0 < n/syl i` (`n ≥ 1`, `syl i ≥ 2`), so with `x = (n/syl i)/m > 0` concavity
`Real.log_le_sub_one_of_pos` gives `log x ≤ x - 1`, i.e. `log (n/syl i) - log m ≤ (n/syl i)/m - 1`
(`Real.log_div`); multiplying by `m > 0` gives `m log(n/syl i) - m log m ≤ n/syl i - m`, and
`log (n/syl i) = log n - log (syl i)` (`Real.log_div`, `n ≠ 0`, `syl i ≠ 0`) finishes. -/
theorem floor_div_log_bound (n i : ℕ) (hn : 1 ≤ n) :
    ((n / syl i : ℕ) : ℝ) * Real.log (n : ℝ)
        - ((n / syl i : ℕ) : ℝ) * Real.log (syl i : ℝ) - (n : ℝ) / (syl i : ℝ)
      ≤ ((n / syl i : ℕ) : ℝ) * Real.log ((n / syl i : ℕ) : ℝ) - ((n / syl i : ℕ) : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hiR : (0 : ℝ) < (syl i : ℝ) := by
    have h := syl_two_le i
    exact_mod_cast (show 0 < syl i by omega)
  rcases Nat.eq_zero_or_pos (n / syl i) with h0 | hpos
  · -- `m = 0`: the left side is `-n/syl i ≤ 0` and the right side is `0`.
    rw [h0]
    simp only [Nat.cast_zero, Real.log_zero, mul_zero, zero_mul, sub_zero, zero_sub]
    exact neg_nonpos.mpr (div_nonneg (le_of_lt hnR) (le_of_lt hiR))
  · -- `m ≥ 1`: concavity of `log` at `m ≤ n/syl i`.
    have hmpos : (0 : ℝ) < ((n / syl i : ℕ) : ℝ) := by exact_mod_cast hpos
    have hcast : ((n / syl i : ℕ) : ℝ) ≤ (n : ℝ) / (syl i : ℝ) := Nat.cast_div_le
    have h := log_concavity_floor ((n / syl i : ℕ) : ℝ) ((n : ℝ) / (syl i : ℝ)) hmpos hcast
    have hlog : Real.log ((n : ℝ) / (syl i : ℝ))
        = Real.log (n : ℝ) - Real.log (syl i : ℝ) :=
      Real.log_div (ne_of_gt hnR) (ne_of_gt hiR)
    rw [hlog, mul_sub] at h
    linarith [h]

end Work.BW
