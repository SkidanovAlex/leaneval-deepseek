import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.ErrProfile
import Submission.Work.NumberTheory.Chen.APSwitchUpper.errH_transport
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_le_decay

namespace Work.ChenPlan.LinearSieve.JR2

/-- Elementary bound behind the shifted budget: for `2 ≤ s ≤ 3` we have `Real.exp (s - 2) ≤ s`
(equivalently `e^{s-2}/s ≤ 1`).  It follows from `log s ≥ 2 (s-1)/(s+1) ≥ s - 2`. -/
lemma exp_sub_two_le_s {s : ℝ} (h2 : 2 ≤ s) (h3 : s ≤ 3) : Real.exp (s - 2) ≤ s := by
  have hs : 0 < s := by linarith
  rw [← Real.le_log_iff_exp_le hs]
  have h1 : 2 * (s - 1) / (s + 1) ≤ Real.log s := by
    have := Real.le_log_one_add_of_nonneg (x := s - 1) (by linarith)
    simpa [show (1:ℝ) + (s-1) = s from by ring, show (s-1)+2 = s+1 from by ring] using this
  have h2' : s - 2 ≤ 2 * (s - 1) / (s + 1) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < s + 1)]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s) (by linarith : (0:ℝ) ≤ 3 - s)]
  linarith

/-- **The `δ`-shifted budget of the clamped case (B′).**  The clamped induction step applies the
Abel staircase at the level `Z ≥ D^{1/3}` with `δ := 3 - log D / log Z ∈ [0, 10^{-5}]`; the two
extra effects it produces (the top of the transported `errH` tail moves from `2` to
`s_Z - 1 = 2 - δ`, and the top boundary term gains the factor `s_Z/s = (3-δ)/s`) are absorbed by
the `0.08 %` slack of the unshifted budget (`budget_sharp.2.1`, whose LHS at `s = 1`, `ε = 1/100`
is `1.0201·(47/50) + 1.01·3·0.01 = 0.989194 < 0.99`).

Numerically: for `1 ≤ s ≤ 3`, `0 ≤ δ ≤ 10^{-5}` and `0 ≤ ε ≤ 1/100`,
`(1+ε)((3-δ)/s)εe^{-2} + (1+ε)²(1/s)((47/50)e^{-2} + δe^{-2}) + 2δe^{-2} ≤ (99/100)·errH s`,
the worst case being `(s, δ, ε) = (1, 10^{-5}, 1/100)`, where the LHS is
`e^{-2}(0.989194 + 3.01·10^{-5}) = 0.989224 < 0.99`.  Proof: `errH s = e^{-2}` for `s ≤ 2` and
`errH s = e^{-s}` for `2 ≤ s ≤ 3`; the LHS is increasing in `ε` and in `δ` and decreasing in `s`
on `[1,2]`; on `[2,3]` divide by `(99/100)e^{-s}` and use `(1/s)e^{s-2} ≤ e/3 < 1`. -/
theorem budget_shift (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1/100) :
    ∀ s δ : ℝ, 1 ≤ s → s ≤ 3 → 0 ≤ δ → δ ≤ 1/100000 →
      (1 + ε) * ((3 - δ) / s) * ε * Real.exp (-2)
        + (1 + ε)^2 * ((1 / s) * ((47/50) * Real.exp (-2) + δ * Real.exp (-2)))
        + 2 * δ * Real.exp (-2)
      ≤ (99/100) * Work.NumberTheory.Chen.APSwitchUpper.errH s := by
  intro s δ hs1 hs3 hδ0 hδ1
  -- The `δ`-shifted numerator `M = (1+ε)(3-δ)ε + (1+ε)²(47/50+δ)` is bounded by `0.98921`.
  have hkey : (1 + ε) * (3 - δ) * ε + (1 + ε)^2 * (47/50 + δ) ≤ 98921/100000 := by
    nlinarith [hε0, hε1, hδ0, hδ1]
  have hkey0 : 0 ≤ (1 + ε) * (3 - δ) * ε + (1 + ε)^2 * (47/50 + δ) := by
    nlinarith [hε0, hε1, hδ0, hδ1]
  -- Factor the common `e^{-2}` out of the left-hand side.
  have hLHS : (1 + ε) * ((3 - δ) / s) * ε * Real.exp (-2)
        + (1 + ε)^2 * ((1 / s) * ((47/50) * Real.exp (-2) + δ * Real.exp (-2)))
        + 2 * δ * Real.exp (-2)
      = Real.exp (-2) * ((1 + ε) * ((3 - δ) / s) * ε
        + (1 + ε)^2 * ((1 / s) * ((47/50) + δ)) + 2 * δ) := by ring
  -- The two `1/s`-terms collect into `M/s`.
  have hP : (1 + ε) * ((3 - δ) / s) * ε + (1 + ε)^2 * ((1 / s) * ((47/50) + δ))
      = ((1 + ε) * (3 - δ) * ε + (1 + ε)^2 * (47/50 + δ)) / s := by ring
  rcases le_or_gt s 2 with hs2 | hs2
  · -- Case `s ≤ 2`: `errH s = e^{-2}`, and `1/s ≤ 1` plus `M ≤ 0.98921` closes the budget.
    rw [Work.NumberTheory.Chen.APSwitchUpper.errH_of_le_two hs2, hLHS,
      show (99/100) * Real.exp (-2) = Real.exp (-2) * (99/100) from by ring]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos (-2)).le
    rw [hP]
    have hdiv : ((1 + ε) * (3 - δ) * ε + (1 + ε)^2 * (47/50 + δ)) / s
        ≤ (1 + ε) * (3 - δ) * ε + (1 + ε)^2 * (47/50 + δ) := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < s)]
      nlinarith [hkey0, mul_nonneg hkey0 (by linarith : (0:ℝ) ≤ s - 1)]
    linarith [hdiv, hkey, hδ1]
  · -- Case `2 < s ≤ 3`: `errH s = e^{-s}`; the shift `e^{s-2}` is absorbed by `e^{s-2} ≤ s`.
    rw [Work.NumberTheory.Chen.APSwitchUpper.errH_of_between hs2 hs3, hLHS]
    have hexp : Real.exp (-s) = Real.exp (-2) * Real.exp (2 - s) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hexp, show (99/100) * (Real.exp (-2) * Real.exp (2 - s))
        = Real.exp (-2) * ((99/100) * Real.exp (2 - s)) from by ring]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos (-2)).le
    have hKexp : ((1 + ε) * ((3 - δ) / s) * ε
          + (1 + ε)^2 * ((1 / s) * ((47/50) + δ)) + 2 * δ) * Real.exp (s - 2) ≤ 99/100 := by
      have hsplit : ((1 + ε) * ((3 - δ) / s) * ε
            + (1 + ε)^2 * ((1 / s) * ((47/50) + δ)) + 2 * δ) * Real.exp (s - 2)
          = ((1 + ε) * (3 - δ) * ε + (1 + ε)^2 * (47/50 + δ)) * (Real.exp (s - 2) / s)
            + 2 * δ * Real.exp (s - 2) := by
        rw [hP]; ring
      rw [hsplit]
      have hrat : Real.exp (s - 2) / s ≤ 1 := by
        rw [div_le_one (by linarith : (0:ℝ) < s)]
        exact exp_sub_two_le_s (le_of_lt hs2) hs3
      have term1 : ((1 + ε) * (3 - δ) * ε + (1 + ε)^2 * (47/50 + δ)) * (Real.exp (s - 2) / s)
          ≤ (1 + ε) * (3 - δ) * ε + (1 + ε)^2 * (47/50 + δ) := by
        nlinarith [mul_le_mul_of_nonneg_left hrat hkey0]
      have hes : Real.exp (s - 2) ≤ 3 := by
        have : Real.exp (s - 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
        linarith [Real.exp_one_lt_three.le]
      have term2 : 2 * δ * Real.exp (s - 2) ≤ 6/100000 := by
        nlinarith [hδ0, hδ1, hes]
      linarith [term1, term2, hkey]
    have hexpmul2 : Real.exp (2 - s) * Real.exp (s - 2) = 1 := by
      rw [← Real.exp_add, show (2:ℝ) - s + (s - 2) = 0 by ring, Real.exp_zero]
    have hb : ((99/100) * Real.exp (2 - s)) * Real.exp (s - 2) = 99/100 := by
      rw [mul_assoc, hexpmul2, mul_one]
    exact (mul_le_mul_iff_of_pos_right (Real.exp_pos (s - 2))).mp (by rw [hb]; exact hKexp)

end Work.ChenPlan.LinearSieve.JR2
