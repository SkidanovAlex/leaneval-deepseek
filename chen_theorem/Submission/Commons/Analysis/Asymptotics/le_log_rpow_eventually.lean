import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Commons.Analysis.Asymptotics.eventually_log_ge

namespace Commons.Analysis.Asymptotics

open Filter

theorem le_log_rpow_eventually {b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c) :
    ∀ᶠ n : ℕ in Filter.atTop, c ≤ (Real.log (n:ℝ)) ^ b := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hlog : ∀ᶠ n : ℕ in Filter.atTop, c ^ (1/b) ≤ Real.log (n:ℝ) :=
    eventually_log_ge (c ^ (1/b))
  filter_upwards [hlog] with n hn
  have h1 : 0 ≤ c ^ (1/b) := Real.rpow_nonneg hc _
  have h2 : (c ^ (1/b)) ^ b = c := by
    rw [← Real.rpow_mul hc (1/b) b]
    have : (1/b) * b = 1 := by field_simp
    rw [this, Real.rpow_one]
  calc c = (c ^ (1/b)) ^ b := h2.symm
    _ ≤ (Real.log (n:ℝ)) ^ b := Real.rpow_le_rpow h1 hn hb.le

end Commons.Analysis.Asymptotics