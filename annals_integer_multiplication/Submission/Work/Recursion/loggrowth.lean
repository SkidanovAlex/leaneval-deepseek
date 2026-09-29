import Mathlib

namespace Work.Recursion

open Filter Asymptotics

/-- `Real.logb 2` is little-o of `x ↦ x ^ (1/8)` at `+∞`. -/
lemma logb_two_isLittleO_rpow_eighth :
    (fun y : ℝ => Real.logb 2 y) =o[atTop] (fun y : ℝ => y ^ ((1 : ℝ) / 8)) := by
  have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 8 by norm_num)).const_mul_left
    ((Real.log 2)⁻¹)
  simpa [Real.logb, div_eq_inv_mul] using h

/-- For large `y`, `logb 2 y ≤ y ^ (1/8)`. -/
lemma eventually_logb_two_le_rpow_eighth :
    ∀ᶠ y : ℝ in atTop, Real.logb 2 y ≤ y ^ ((1 : ℝ) / 8) := by
  filter_upwards [(isLittleO_iff.mp logb_two_isLittleO_rpow_eighth) one_pos,
    eventually_ge_atTop (0 : ℝ)] with y hy hy0
  rw [Real.norm_eq_abs, one_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hy0 _)] at hy
  linarith [le_abs_self (Real.logb 2 y)]

/-- `Real.logb 2` tends to `+∞`. -/
lemma tendsto_logb_two_atTop : Tendsto (Real.logb (2 : ℝ)) atTop atTop :=
  Real.tendsto_logb_atTop (by norm_num)

/-- For every `c > 0`, `c * (log₂ y + 1) ≤ y ^ (1/4)` for all sufficiently large `y`. -/
lemma eventually_logb_mul_add_one_le_rpow (c : ℝ) (hc : 0 < c) :
    ∀ᶠ y : ℝ in atTop, c * (Real.logb 2 y + 1) ≤ y ^ ((1 : ℝ) / 4) := by
  have hD : ∀ᶠ y : ℝ in atTop, (2 * c + 2) ≤ y ^ ((1 : ℝ) / 8) :=
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 8 by norm_num)).eventually_ge_atTop (2 * c + 2)
  filter_upwards [eventually_logb_two_le_rpow_eighth, hD, eventually_ge_atTop (1 : ℝ)]
    with y h1 h2 hy1
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hr1 : (1 : ℝ) ≤ y ^ ((1 : ℝ) / 8) := Real.one_le_rpow hy1 (by norm_num)
  have hy4 : y ^ ((1 : ℝ) / 4) = (y ^ ((1 : ℝ) / 8)) ^ 2 := by
    rw [show ((1 : ℝ) / 4) = (1 / 8) * 2 by norm_num, Real.rpow_mul hy0]
    norm_num
  rw [hy4]
  nlinarith [h1, h2, hc, hr1]

/-- `log₂ log₂` grows slower than any positive power of `log₂`, and `log₂ → ∞`. -/
theorem loggrowth (c : ℝ) (hc : 0 < c) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    c ≤ Real.logb 2 (n : ℝ) ∧
    c * (Real.logb 2 (Real.logb 2 (n : ℝ)) + 1) ≤ (Real.logb 2 (n : ℝ)) ^ ((1 : ℝ) / 4) := by
  have hF : ∀ᶠ x : ℝ in atTop,
      c ≤ Real.logb 2 x ∧
        c * (Real.logb 2 (Real.logb 2 x) + 1) ≤ (Real.logb 2 x) ^ ((1 : ℝ) / 4) :=
    (tendsto_logb_two_atTop.eventually_ge_atTop c).and
      (tendsto_logb_two_atTop.eventually (eventually_logb_mul_add_one_le_rpow c hc))
  obtain ⟨N, hN⟩ :=
    eventually_atTop.mp ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually hF)
  exact ⟨N, fun n hn => hN n hn⟩

end Work.Recursion
