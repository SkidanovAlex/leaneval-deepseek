import Mathlib

namespace Work.FIArea3.JointCount

theorem threshold_le (a θ : ℝ) (ha : 0 < a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    a * min ((2 * Real.pi * θ) ^ 3 / 6) (2 * Real.pi * θ + 1 + θ) / (32 * θ)
      ≤ min a (1.2 * θ * a) := by
  rcases eq_or_lt_of_le hθ0 with hθeq | hθ
  · subst hθeq
    simp
    exact ha.le
  · have hpi : Real.pi < 4 := Real.pi_lt_four
    have hM32 : min ((2 * Real.pi * θ) ^ 3 / 6) (2 * Real.pi * θ + 1 + θ) ≤ 32 * θ := by
      rcases le_total θ (2/5) with hle | hge
      · have hnonneg : 0 ≤ 2 * Real.pi * θ := by positivity
        have hle8 : 2 * Real.pi * θ ≤ 8 * θ := by nlinarith [hpi, hθ]
        have hp3 : (2 * Real.pi * θ)^3 ≤ (8*θ)^3 := pow_le_pow_left₀ hnonneg hle8 3
        have h8 : (8*θ)^3 = 512 * θ^3 := by ring
        rw [h8] at hp3
        have hAb : (2 * Real.pi * θ) ^ 3 / 6 ≤ (256/3 : ℝ) * θ^3 := by linarith [hp3]
        have hθsq : θ^2 ≤ (2/5:ℝ)^2 := pow_le_pow_left₀ hθ.le hle 2
        have h1 : (256/3 : ℝ) * θ^2 ≤ 1024/75 := by nlinarith [hθsq]
        have h2 : (256/3 : ℝ) * θ^2 * θ ≤ (1024/75) * θ := mul_le_mul_of_nonneg_right h1 hθ.le
        have h4 : (1024/75 : ℝ) * θ ≤ 32 * θ := by
          have : (1024/75:ℝ) ≤ 32 := by norm_num
          exact mul_le_mul_of_nonneg_right this hθ.le
        have e : (256/3:ℝ)*θ^3 = (256/3)*θ^2*θ := by ring
        have hb : (256/3 : ℝ) * θ^3 ≤ 32 * θ := by rw [e]; linarith [h2, h4]
        exact le_trans (min_le_left _ _) (le_trans hAb hb)
      · have hB9 : 2 * Real.pi * θ + 1 + θ ≤ 9 * θ + 1 := by nlinarith [hpi, hθ]
        have h932 : 9 * θ + 1 ≤ 32 * θ := by nlinarith
        exact le_trans (min_le_right _ _) (le_trans hB9 h932)
    have hM384 : min ((2 * Real.pi * θ) ^ 3 / 6) (2 * Real.pi * θ + 1 + θ) ≤ 38.4 * θ^2 := by
      rcases le_total θ (2/5) with hle | hge
      · have hnonneg : 0 ≤ 2 * Real.pi * θ := by positivity
        have hle8 : 2 * Real.pi * θ ≤ 8 * θ := by nlinarith [hpi, hθ]
        have hp3 : (2 * Real.pi * θ)^3 ≤ (8*θ)^3 := pow_le_pow_left₀ hnonneg hle8 3
        have h8 : (8*θ)^3 = 512 * θ^3 := by ring
        rw [h8] at hp3
        have hAb : (2 * Real.pi * θ) ^ 3 / 6 ≤ (256/3 : ℝ) * θ^3 := by linarith [hp3]
        have hb : (256/3 : ℝ)*θ^3 ≤ 38.4 * θ^2 := by
          have hmax : (256/3:ℝ)*θ^3 = (256/3)*θ^2*θ := by ring
          rw [hmax]
          have hne : (256/3:ℝ)*θ^2*θ ≤ (256/3)*θ^2*(2/5) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
          have hconst : (256/3:ℝ)*(2/5) ≤ 38.4 := by norm_num
          nlinarith [hne, hconst, sq_nonneg θ]
        exact le_trans (min_le_left _ _) (le_trans hAb hb)
      · have hB9 : 2 * Real.pi * θ + 1 + θ ≤ 9 * θ + 1 := by nlinarith [hpi, hθ]
        have h1 : 38.4 * θ^2 ≥ 38.4 * (2/5) * θ := by nlinarith [hge, hθ0]
        have h2 : 38.4 * (2/5) * θ ≥ 9 * θ + 1 := by nlinarith [hge]
        exact le_trans (min_le_right _ _) (le_trans hB9 (by linarith [h1, h2]))
    apply le_min
    · rw [div_le_iff₀ (by positivity : (0:ℝ) < 32 * θ)]
      exact mul_le_mul_of_nonneg_left hM32 ha.le
    · rw [div_le_iff₀ (by positivity : (0:ℝ) < 32 * θ)]
      calc a * min ((2 * Real.pi * θ) ^ 3 / 6) (2 * Real.pi * θ + 1 + θ)
          ≤ a * (38.4 * θ^2) := mul_le_mul_of_nonneg_left hM384 ha.le
        _ = (1.2 * θ * a) * (32 * θ) := by ring

end Work.FIArea3.JointCount
