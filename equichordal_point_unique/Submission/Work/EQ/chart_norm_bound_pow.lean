import Mathlib
import Submission.Work.EQ.EquiLocalDefs

namespace Work.EQ

/-- **A small `k`-th power bound forces `‖z‖ < 1`.**  If `κ ≠ 0`, `k > 0` and `‖κ * z ^ k‖ < ρ`
with `ρ ≤ ‖κ‖ / 2`, then `‖z‖ < 1`: indeed `‖z‖ ^ k < 1 / 2 < 1`. -/
theorem chart_norm_bound_pow {κ z : ℂ} {k : ℕ} {ρ : ℝ} (hκ : κ ≠ 0) (hk : 0 < k)
    (hρ : ‖κ * z ^ k‖ < ρ) (hbd : ρ ≤ ‖κ‖ / 2) : ‖z‖ < 1 := by
  have hκpos : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
  have h1 : ‖κ‖ * ‖z‖ ^ k < ‖κ‖ / 2 := by
    have h := hρ.trans_le hbd
    rwa [norm_mul, norm_pow] at h
  have h2 : ‖z‖ ^ k < 1 / 2 := by
    have h1' : ‖κ‖ * ‖z‖ ^ k < ‖κ‖ * (1 / 2) := by linarith
    exact (mul_lt_mul_iff_right₀ hκpos).mp h1'
  by_contra h
  have hge : 1 ≤ ‖z‖ := not_lt.mp h
  have hle : 1 ≤ ‖z‖ ^ k := one_le_pow₀ hge
  linarith

end Work.EQ
