import Mathlib
import Submission.Commons.NumberTheory.Moebius.log_weighted_moebius_recip_bound
import Submission.Commons.NumberTheory.Moebius.moebius_recip_sum_exp_decay

namespace Work.LinnikAreas.Density4.Udecay

/-- A uniform bound for the partial sums `muRecipSum m = Σ_{n ≤ m} μ(n)/n`.
`recip_bound` (imported here) gives `|muRecip t| ≤ C·exp(-(c√log t)) ≤ C` for `t ≥ 1` with
`muRecip t = muRecipSum ⌊t⌋₊`; for `m = 0` the sum is empty. -/
theorem muRecipSum_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
      |Commons.NumberTheory.Moebius.muRecipSum m| ≤ C := by
  obtain ⟨c, C0, hc, hC0, hdecay⟩ :=
    Commons.NumberTheory.Moebius.moebius_recip_sum_exp_decay
  -- `muRecipSum_decay` gives `|muRecipSum n| ≤ max C0 1 · exp(-(c√log n))` for all `n ≥ 1`;
  -- since the exponential factor is `≤ 1`, the constant `max C0 1` is a uniform bound.
  have hCpos : 0 < max C0 1 := lt_of_lt_of_le zero_lt_one (le_max_right C0 1)
  refine ⟨max C0 1, hCpos, ?_⟩
  intro m
  have hCd := Commons.NumberTheory.Moebius.muRecipSum_decay hc hC0 hdecay
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · -- `m = 0`: the sum is empty.
    subst h0
    rw [show Commons.NumberTheory.Moebius.muRecipSum 0 = 0 by
      simp [Commons.NumberTheory.Moebius.muRecipSum], abs_zero]
    exact hCpos.le
  · have h := hCd m hpos
    have hexp : Real.exp (-(c * Real.sqrt (Real.log (m:ℝ)))) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have : 0 ≤ c * Real.sqrt (Real.log (m:ℝ)) :=
        mul_nonneg hc.le (Real.sqrt_nonneg _)
      linarith
    calc |Commons.NumberTheory.Moebius.muRecipSum m|
        ≤ max C0 1 * Real.exp (-(c * Real.sqrt (Real.log (m:ℝ)))) := h
      _ ≤ max C0 1 * 1 := mul_le_mul_of_nonneg_left hexp hCpos.le
      _ = max C0 1 := mul_one _

end Work.LinnikAreas.Density4.Udecay
