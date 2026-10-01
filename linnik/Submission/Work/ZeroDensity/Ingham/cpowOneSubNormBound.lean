import Mathlib

namespace Work.ZeroDensity.Ingham

/-- Bound on the norm of `Y ^ (1 - ρ)` in the right half-plane: with `1 ≤ Y ≤ T²`
and `1/2 ≤ Re ρ`, the modulus `‖Y^(1-ρ)‖ = Y^(1 - Re ρ)` is at most `T`. -/
lemma cpowOneSubNormBound (T Y : ℝ) (ρ : ℂ) (hT : 1 ≤ T) (hY : 1 ≤ Y) (hYT : Y ≤ T ^ 2)
    (hβ : 1 / 2 ≤ ρ.re) : ‖(Y : ℂ) ^ (1 - ρ)‖ ≤ T := by
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hYpos, Complex.sub_re, Complex.one_re]
  calc Y ^ (1 - ρ.re) ≤ Y ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hY (by linarith)
    _ ≤ (T ^ 2) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (le_of_lt hYpos) hYT (by norm_num)
    _ = T := by
        rw [← Real.rpow_natCast T 2, ← Real.rpow_mul (le_trans zero_le_one hT)]
        norm_num

end Work.ZeroDensity.Ingham
