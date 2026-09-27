import Mathlib
import Submission.Work.EQ.FanTri.facA_bounds

namespace Work.EQ.FanTri

open Work.EQ Complex

noncomputable section

/-- Algebraic identity behind the Lipschitz estimate for `facB a z = (sR a z)⁻¹`:
`facB a z - facB a w = (sR a w - sR a z) / (sR a z * sR a w)`. -/
lemma facB_sub_eq {a : ℝ} {z w : ℂ × ℂ} (hz : sR a z ≠ 0) (hw : sR a w ≠ 0) :
    facB a z - facB a w = (sR a w - sR a z) / (sR a z * sR a w) := by
  rw [facB, facB]
  field_simp

/-- Boundedness and Lipschitz estimate for `facB a z = (sR a z)⁻¹` on the ball
`‖z‖ ≤ sHat a / 16` (`sD a z = (sHat a : ℂ) - z.1`, `sR a z = (sD a z ^ 2 + z.2 ^ 2)^(1/2)`,
`sHat a = (1-a)/2`).  The already-proved `sD_sR_setup` gives `sR a z ^ 2 = sD a z ^ 2 + z.2 ^ 2`,
whence `‖sR a z - sHat a‖ ≤ (3/2)‖z‖` and in particular `‖sR a z‖ ≥ sHat a/2`.  The Lipschitz
estimate follows from `facB a z - facB a w = (sR a w - sR a z)/(sR a z * sR a w)`.  The
constants `2` and `100` are deliberately generous. -/
theorem facB_bounds {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {z w : ℂ × ℂ}
    (hz : ‖z‖ ≤ sHat a / 16) (hw : ‖w‖ ≤ sHat a / 16) :
    ‖facB a z‖ ≤ 2 / sHat a ∧ ‖facB a z - facB a w‖ ≤ 100 / sHat a ^ 3 * ‖z - w‖ := by
  have hs0 : 0 < sHat a := sHat_pos ha1
  obtain ⟨-, -, hRlowz, -, -, -⟩ := sR_pointwise ha0 ha1 hz
  obtain ⟨-, -, hRloww, -, -, -⟩ := sR_pointwise ha0 ha1 hw
  have hhalf : (0 : ℝ) < sHat a / 2 := by linarith
  have hRzpos : 0 < ‖sR a z‖ := lt_of_lt_of_le hhalf hRlowz
  have hRwpos : 0 < ‖sR a w‖ := lt_of_lt_of_le hhalf hRloww
  have hRzne : sR a z ≠ 0 := norm_pos_iff.mp hRzpos
  have hRwne : sR a w ≠ 0 := norm_pos_iff.mp hRwpos
  have hinvz : ‖sR a z‖⁻¹ ≤ 2 / sHat a := by
    calc ‖sR a z‖⁻¹ ≤ (sHat a / 2)⁻¹ := (inv_le_inv₀ hRzpos hhalf).mpr hRlowz
      _ = 2 / sHat a := by rw [inv_div]
  have hinvw : ‖sR a w‖⁻¹ ≤ 2 / sHat a := by
    calc ‖sR a w‖⁻¹ ≤ (sHat a / 2)⁻¹ := (inv_le_inv₀ hRwpos hhalf).mpr hRloww
      _ = 2 / sHat a := by rw [inv_div]
  constructor
  · rw [facB, norm_inv]; exact hinvz
  · have hfac : facB a z - facB a w = (sR a w - sR a z) / (sR a z * sR a w) :=
      facB_sub_eq hRzne hRwne
    have hlip : ‖sR a w - sR a z‖ ≤ 3 / 2 * ‖z - w‖ := by
      rw [norm_sub_rev]; exact sR_dist_le ha0 ha1 hz hw
    have hden : ‖sR a z‖⁻¹ * ‖sR a w‖⁻¹ ≤ (2 / sHat a) * (2 / sHat a) :=
      mul_le_mul hinvz hinvw (by positivity) (by positivity)
    calc ‖facB a z - facB a w‖
        = ‖sR a w - sR a z‖ * (‖sR a z‖⁻¹ * ‖sR a w‖⁻¹) := by
          rw [hfac, norm_div, norm_mul, div_eq_mul_inv, mul_inv]
      _ ≤ (3 / 2 * ‖z - w‖) * ((2 / sHat a) * (2 / sHat a)) :=
          mul_le_mul hlip hden (by positivity) (by positivity)
      _ ≤ 100 / sHat a ^ 3 * ‖z - w‖ := by
          have hs2 : (0 : ℝ) < sHat a ^ 2 := by positivity
          have hs3 : (0 : ℝ) < sHat a ^ 3 := by positivity
          have hkey : 6 / sHat a ^ 2 ≤ 100 / sHat a ^ 3 := by
            rw [div_le_div_iff₀ hs2 hs3]
            nlinarith [sHat_le_half ha0 ha1, hs0, sq_nonneg (sHat a)]
          calc (3 / 2 * ‖z - w‖) * ((2 / sHat a) * (2 / sHat a))
              = 6 / sHat a ^ 2 * ‖z - w‖ := by field_simp; ring
            _ ≤ 100 / sHat a ^ 3 * ‖z - w‖ :=
                mul_le_mul_of_nonneg_right hkey (norm_nonneg _)

end

end Work.EQ.FanTri
