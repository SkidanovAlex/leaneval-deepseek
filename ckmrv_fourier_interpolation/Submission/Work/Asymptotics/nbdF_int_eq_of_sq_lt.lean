import Mathlib

namespace Work.Asymptotics

/-- If `x` lies in the open interval `(-1/16, 1 + 1/16)` and `(x + d)^2 < 7/16` for an
integer `d`, then `d ∈ {-1, 0}`.  Indeed `d ≥ 1` forces `x + d > 15/16`, and `d ≤ -2`
forces `x + d < -15/16`; in both cases `(x + d)^2 ≥ (15/16)^2 > 7/16`. -/
theorem nbdF_int_eq_of_sq_lt {x : ℝ} (h1 : -(1 / 16 : ℝ) < x) (h2 : x < 1 + 1 / 16)
    {d : ℤ} (hd : (x + (d : ℝ)) ^ 2 < 7 / 16) : d = 0 ∨ d = -1 := by
  by_cases h : d ≤ -2
  · -- `d ≤ -2` gives `x + d < -15/16`, hence `(x+d)^2 > 7/16`.
    exfalso
    have hd' : (d : ℝ) ≤ -2 := by exact_mod_cast h
    have hprod : (0 : ℝ) ≤ (x + (d : ℝ) + 15 / 16) * (x + (d : ℝ) - 15 / 16) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    have : (15 / 16 : ℝ) ^ 2 ≤ (x + (d : ℝ)) ^ 2 := by nlinarith [hprod]
    linarith
  · by_cases h' : 1 ≤ d
    · -- `d ≥ 1` gives `x + d > 15/16`, hence `(x+d)^2 > 7/16`.
      exfalso
      have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast h'
      have hprod : (0 : ℝ) ≤ (x + (d : ℝ) - 15 / 16) * (x + (d : ℝ) + 15 / 16) :=
        mul_nonneg (by linarith) (by linarith)
      have : (15 / 16 : ℝ) ^ 2 ≤ (x + (d : ℝ)) ^ 2 := by nlinarith [hprod]
      linarith
    · -- `-1 ≤ d ≤ 0`.
      omega

end Work.Asymptotics
