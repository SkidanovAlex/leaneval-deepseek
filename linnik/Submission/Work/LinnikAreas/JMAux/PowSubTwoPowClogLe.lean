import Mathlib

namespace Work.LinnikAreas.JMAux

/-- Comparison of `((2)^(θ-2))^j` with `R^(-9/10)` under `R ≤ 2^j` and `θ ≤ 11/10`. -/
lemma PowSubTwoPowClogLe (R j : ℕ) {θ : ℝ} (hR : 1 ≤ R) (hRj : (R:ℝ) ≤ (2:ℝ)^j)
    (hθ : θ ≤ 11/10) : ((2:ℝ)^(θ - 2))^j ≤ (R:ℝ)^(-(9/10:ℝ)) := by
  have hRpos : (0:ℝ) < (R:ℝ) := by
    have : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    linarith
  have hθ' : θ - 2 ≤ -(9/10:ℝ) := by linarith
  have h1 : (2:ℝ)^(θ-2) ≤ (2:ℝ)^(-(9/10:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ'
  have h2 : ((2:ℝ)^(θ-2))^j ≤ ((2:ℝ)^(-(9/10:ℝ)))^j :=
    pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) h1 j
  have h3 : ((2:ℝ)^(-(9/10:ℝ)))^j = ((2:ℝ)^j)^(-(9/10:ℝ)) := by
    rw [← Real.rpow_natCast ((2:ℝ)^(-(9/10:ℝ))) j,
        ← Real.rpow_mul (show (0:ℝ) ≤ 2 by norm_num) (-(9/10)) (j:ℝ),
        ← Real.rpow_natCast (2:ℝ) j,
        ← Real.rpow_mul (show (0:ℝ) ≤ 2 by norm_num) (j:ℝ) (-(9/10)),
        mul_comm (-(9/10:ℝ)) (j:ℝ)]
  rw [h3] at h2
  exact le_trans h2 (Real.rpow_le_rpow_of_nonpos hRpos hRj (by norm_num))

end Work.LinnikAreas.JMAux
