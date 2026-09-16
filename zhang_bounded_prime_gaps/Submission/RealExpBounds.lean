import Mathlib

/-!
# Small real exponential bounds

Elementary `exp` estimates used by the zeta-side analysis (uniform pole
asymptotic assembly).  Currently: `exp(S) − 1 ≤ 2S` for `0 ≤ S ≤ 1`, from
Mathlib's `Real.exp_bound` (degree-1 Taylor bound with remainder on `|x| ≤ 1`).
-/

/-- `exp(S) − 1 ≤ 2·S` for `0 ≤ S ≤ 1` (Taylor bound of `Real.exp_bound` at
degree 1). -/
lemma exp_sub_one_le_two_mul {S : ℝ} (hS0 : 0 ≤ S) (hS1 : S ≤ 1) :
    Real.exp S - 1 ≤ 2 * S := by
  have hb := Real.exp_bound (x := S) (by rw [abs_of_nonneg hS0]; exact hS1) (n := 1) (by norm_num)
  have hsum : (∑ m ∈ Finset.range 1, S ^ m / (m.factorial : ℝ)) = 1 := by simp
  rw [hsum] at hb
  have hb' : |Real.exp S - 1| ≤ 2 * S := by
    simpa [pow_one, abs_of_nonneg hS0, mul_comm] using hb
  have he : Real.exp S ≥ 1 := by
    have := Real.add_one_le_exp S
    nlinarith [this, hS0]
  have habs : |Real.exp S - 1| = Real.exp S - 1 := by
    rw [abs_of_nonneg]
    linarith
  rwa [habs] at hb'
