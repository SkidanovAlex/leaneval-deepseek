import Mathlib

namespace Work.FIArea6Road

theorem ZsfunTermNorm (a : ℕ → ℂ) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) (n : ℕ) :
    ‖a n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ ‖a n‖ * (n : ℝ) ^ (-σ) := by
  have hs : (-((σ : ℂ) + (t : ℂ) * Complex.I)).re ≠ 0 := by
    simp
    linarith
  have hre : (-((σ : ℂ) + (t : ℂ) * Complex.I)).re = -σ := by simp
  rw [norm_mul, Complex.norm_natCast_cpow_of_re_ne_zero n hs, hre]

end Work.FIArea6Road
