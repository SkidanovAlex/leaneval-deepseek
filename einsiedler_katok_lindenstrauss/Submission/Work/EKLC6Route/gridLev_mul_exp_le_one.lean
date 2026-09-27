import Mathlib
import Submission.Work.EKLC6Route.Defs

namespace Work.EKLC6Route

/-- The level `gridLev t i = ⌈betaExp t * i / log 2⌉` is exactly large enough that the
geometric decay `(1/2)^(gridLev t i)` compensates the expansion `exp (i * betaExp t)`.
Indeed `gridLev t i * log 2 ≥ i * betaExp t`, and exponentiating gives the claim. -/
theorem gridLev_mul_exp_le_one (t : Fin 3 → ℝ) (i : ℕ) :
    (1 / 2 : ℝ) ^ Work.EKLC6Route.gridLev t i * Real.exp ((i : ℝ) * Work.EKLC6Route.betaExp t) ≤ 1 := by
  set b := Work.EKLC6Route.betaExp t with hb
  set n := Work.EKLC6Route.gridLev t i with hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the defining estimate of the ceiling
  have hceil : b * (i : ℝ) / Real.log 2 ≤ (n : ℝ) := by
    rw [hn, hb]; exact Nat.le_ceil _
  have hkey : (i : ℝ) * b ≤ (n : ℝ) * Real.log 2 := by
    have h1 := mul_le_mul_of_nonneg_right hceil (le_of_lt hlog2)
    rw [div_mul_cancel₀ _ (ne_of_gt hlog2)] at h1
    rw [mul_comm b (i : ℝ)] at h1
    exact h1
  have hexp : (1 / 2 : ℝ) ^ n = Real.exp (-((n : ℝ) * Real.log 2)) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2), ← Real.exp_nat_mul]
    congr 1
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
    ring
  have hprod : (1 / 2 : ℝ) ^ n * Real.exp ((i : ℝ) * b)
      = Real.exp ((i : ℝ) * b - (n : ℝ) * Real.log 2) := by
    rw [hexp, ← Real.exp_add]
    congr 1
    ring
  rw [hprod]
  rw [Real.exp_le_one_iff]
  linarith

end Work.EKLC6Route
