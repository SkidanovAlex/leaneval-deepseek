import Mathlib

namespace Work.Pert.pert2v2

theorem drift_quotient_le {ρ : ℂ} {Φ : ℂ → ℂ} {z w : ℂ} {k : ℕ}
    (hρ : ‖ρ - 1‖ ≤ 1 / 32) (hΦ : Φ w = Φ z + (k : ℂ))
    (hdrift : ‖(w - z) - (k : ℂ) * ρ‖ ≤ 1 / 64) :
    ‖(Φ w - w / ρ) - (Φ z - z / ρ)‖ ≤ 1 := by
  -- `‖ρ - 1‖ ≤ 1/32` gives `‖ρ‖ ≥ 31/32`, in particular `ρ ≠ 0`.
  have hnorm : (31 : ℝ) / 32 ≤ ‖ρ‖ := by
    have h1 : |‖ρ‖ - ‖(1 : ℂ)‖| ≤ ‖ρ - 1‖ := abs_norm_sub_norm_le ρ 1
    rw [norm_one] at h1
    have h2 : -(‖ρ‖ - 1) ≤ 1 / 32 := by
      have := neg_le_abs (‖ρ‖ - 1)
      linarith
    linarith
  have hρ0 : ρ ≠ 0 := by
    intro h; rw [h] at hnorm; norm_num at hnorm
  -- the difference of the two "coordinates" is `-(u / ρ)` where `u = (w - z) - k * ρ`.
  have key : (Φ w - w / ρ) - (Φ z - z / ρ) = -(((w - z) - (k : ℂ) * ρ) / ρ) := by
    rw [hΦ]
    field_simp
    ring
  rw [key, norm_neg, norm_div]
  have hle : ‖(w - z) - (k : ℂ) * ρ‖ / ‖ρ‖ ≤ (1 / 64) / (31 / 32) :=
    div_le_div₀ (by norm_num) hdrift (by norm_num) hnorm
  have : (1 / 64 : ℝ) / (31 / 32) ≤ 1 := by norm_num
  linarith

end Work.Pert.pert2v2
