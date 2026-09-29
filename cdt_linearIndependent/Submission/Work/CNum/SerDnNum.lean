import Mathlib
import Submission.Work.ANum.Ivl

namespace Work.CNum

/-- The coefficient sum `∑_{j=22}^{43} (2j - 43) = 484`. -/
lemma sum_coeff_484 : (∑ j ∈ Finset.Icc (22:ℕ) 43, (2 * (j : ℝ) - 43)) = 484 := by
  rw [show Finset.Icc (22:ℕ) 43 = Finset.Ico 22 44 from by decide]
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num

/-- Numerical bound on the `serDn` series remainder: for `0 ≤ ρ ≤ 10⁻⁶` and `0 ≤ R ≤ 79/100`,
`∑_{j=22}^{43} (2j-43) ρ R^j ≤ (1 - R^23) · 4096/2^30`. -/
theorem SerDnNum {R ρ : ℝ} (hR0 : 0 ≤ R) (hR : R ≤ 79 / 100) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 10 ^ 6) : (∑ j ∈ Finset.Icc (22:ℕ) 43, (2 * (j : ℝ) - 43) * ρ * R ^ j) ≤ (1 - R ^ 23) * (4096 / (Work.ANum.SC : ℝ)) := by
  have hR1 : R ≤ 1 := by linarith
  have hstep1 : (∑ j ∈ Finset.Icc (22:ℕ) 43, (2 * (j : ℝ) - 43) * ρ * R ^ j)
      ≤ (∑ j ∈ Finset.Icc (22:ℕ) 43, (2 * (j : ℝ) - 43) * ρ * R ^ 22) := by
    apply Finset.sum_le_sum
    intro j hj
    have hj1 : 22 ≤ j := (Finset.mem_Icc.mp hj).1
    have hcoef : (0:ℝ) ≤ 2 * (j : ℝ) - 43 := by
      have : (22:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj1
      linarith
    have hjR : R ^ j ≤ R ^ 22 := pow_le_pow_of_le_one hR0 hR1 hj1
    exact mul_le_mul_of_nonneg_left hjR (mul_nonneg hcoef hρ0)
  have hstep2 : (∑ j ∈ Finset.Icc (22:ℕ) 43, (2 * (j : ℝ) - 43) * ρ * R ^ 22) = 484 * ρ * R ^ 22 := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, sum_coeff_484]
  have hb1 : (∑ j ∈ Finset.Icc (22:ℕ) 43, (2 * (j : ℝ) - 43) * ρ * R ^ j) ≤ 484 * ρ * R ^ 22 :=
    le_trans hstep1 (le_of_eq hstep2)
  have hR22 : R ^ 22 ≤ (79/100:ℝ) ^ 22 := pow_le_pow_left₀ hR0 hR 22
  have hb2 : 484 * ρ * R ^ 22 ≤ 484 * (1/10^6) * (79/100:ℝ)^22 := by
    have h1 : ρ * R^22 ≤ (1/10^6) * (79/100:ℝ)^22 :=
      mul_le_mul hρ hR22 (pow_nonneg hR0 22) (by norm_num)
    calc 484 * ρ * R^22 = 484 * (ρ * R^22) := by ring
      _ ≤ 484 * ((1/10^6) * (79/100:ℝ)^22) := mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 484 * (1/10^6) * (79/100:ℝ)^22 := by ring
  have hb3 : 484 * (1/10^6) * (79/100:ℝ)^22 ≤ (1 - (79/100:ℝ)^23) * (4096 / (Work.ANum.SC : ℝ)) := by
    have hSC : ((Work.ANum.SC : ℤ) : ℝ) = 2^30 := by norm_num [Work.ANum.SC]
    rw [hSC]
    norm_num
  have hb4 : (1 - (79/100:ℝ)^23) * (4096 / (Work.ANum.SC : ℝ)) ≤ (1 - R ^ 23) * (4096 / (Work.ANum.SC : ℝ)) := by
    have hR23 : R^23 ≤ (79/100:ℝ)^23 := pow_le_pow_left₀ hR0 hR 23
    have hpos : (0:ℝ) ≤ 4096 / (Work.ANum.SC : ℝ) := by
      apply div_nonneg (by norm_num)
      have : (0:ℝ) < (Work.ANum.SC : ℝ) := by norm_num [Work.ANum.SC]
      linarith
    apply mul_le_mul_of_nonneg_right _ hpos
    linarith
  linarith [hb1, hb2, hb3, hb4]

end Work.CNum
