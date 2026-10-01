import Mathlib
import Submission.Work.LinnikAreas.Density4.selberg_U_aux

namespace Work.LinnikAreas.Density4.Udecay

open scoped BigOperators

/-- `A(t) = Σ_{n ≤ ⌊t⌋} μ(n)/n` decays like `exp(-c √(log t))`.

This is the real-variable form of `Commons.NumberTheory.Moebius.moebius_recip_sum_exp_decay`
(which gives the estimate for every real `x ≥ 2`); the only extra work is the unit
interval `1 ≤ t < 2`, where `⌊t⌋₊ = 1` and `muRecip t = 1`. -/
theorem recip_bound : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
    |Work.LinnikAreas.Density4.muRecip t| ≤ C * Real.exp (-(c * Real.sqrt (Real.log t))) := by
  obtain ⟨c, C0, hc, hC0, hdecay⟩ :=
    Commons.NumberTheory.Moebius.moebius_recip_sum_exp_decay
  refine ⟨c, max (max C0 1) (Real.exp (c * Real.sqrt (Real.log 2))), hc, ?_, ?_⟩
  · exact lt_max_of_lt_left (lt_of_lt_of_le hC0 (le_max_left C0 1))
  · intro t ht
    have hCge : Real.exp (c * Real.sqrt (Real.log 2))
        ≤ max (max C0 1) (Real.exp (c * Real.sqrt (Real.log 2))) := le_max_right _ _
    have hC0le : C0 ≤ max (max C0 1) (Real.exp (c * Real.sqrt (Real.log 2))) :=
      le_trans (le_max_left C0 1) (le_max_left _ _)
    rcases lt_or_ge t 2 with h2 | h2
    · -- The unit interval `1 ≤ t < 2`: `⌊t⌋₊ = 1` and `muRecip t = 1`.
      have hfl : ⌊t⌋₊ = 1 := by
        rw [Nat.floor_eq_iff (by linarith : (0:ℝ) ≤ t)]
        exact ⟨by push_cast; exact ht, by push_cast; linarith⟩
      have hmu : Work.LinnikAreas.Density4.muRecip t = 1 := by
        rw [Work.LinnikAreas.Density4.muRecip, hfl]
        simp [Commons.NumberTheory.Moebius.muRecipSum]
      rw [hmu, abs_one]
      have hlog2 : Real.log t ≤ Real.log 2 := Real.log_le_log (by linarith) (le_of_lt h2)
      have hs : Real.sqrt (Real.log t) ≤ Real.sqrt (Real.log 2) := Real.sqrt_le_sqrt hlog2
      have hcs : c * Real.sqrt (Real.log t) ≤ c * Real.sqrt (Real.log 2) :=
        mul_le_mul_of_nonneg_left hs hc.le
      calc (1:ℝ)
          ≤ Real.exp (c * Real.sqrt (Real.log 2)) *
              Real.exp (-(c * Real.sqrt (Real.log t))) := by
            rw [← Real.exp_zero, ← Real.exp_add]
            exact Real.exp_le_exp.mpr (by linarith)
        _ ≤ max (max C0 1) (Real.exp (c * Real.sqrt (Real.log 2))) *
              Real.exp (-(c * Real.sqrt (Real.log t))) :=
            mul_le_mul_of_nonneg_right hCge (Real.exp_pos _).le
    · -- `t ≥ 2`: the committed decay estimate applies verbatim.
      have hb := hdecay t h2
      exact le_trans hb (mul_le_mul_of_nonneg_right hC0le (Real.exp_pos _).le)

end Work.LinnikAreas.Density4.Udecay
