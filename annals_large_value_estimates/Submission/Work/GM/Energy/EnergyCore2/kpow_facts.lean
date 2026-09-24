import Mathlib

namespace Work.GM.Energy.EnergyCore2

/-- The locality-window parameter `K = Θ·N^{1/mm}` used in the assembly of GM Proposition 11.1
(`Θ ≥ 1`, `N ≥ 1`, `mm ≥ 1`) satisfies `K ≥ 1`, `K^mm = Θ^mm · N`, and, for every `j ≤ 12`,
`(K+1)^j ≤ 2^j · Θ^j · N^{j/mm}`. -/
theorem kpow_facts {Θ N : ℝ} {mm : ℕ} (hΘ : 1 ≤ Θ) (hN : 1 ≤ N) (hm : 1 ≤ mm) :
    1 ≤ Θ * N ^ (1 / (mm : ℝ)) ∧
      (Θ * N ^ (1 / (mm : ℝ))) ^ (mm : ℝ) = Θ ^ mm * N ∧
        ∀ j : ℕ, j ≤ 12 → (Θ * N ^ (1 / (mm : ℝ)) + 1) ^ j
          ≤ 2 ^ j * Θ ^ j * N ^ ((j : ℝ) / (mm : ℝ)) := by
  have hmmpos : 0 < (mm : ℝ) := by
    have h : (1 : ℝ) ≤ (mm : ℝ) := by exact_mod_cast hm
    linarith
  have hmmne : (mm : ℝ) ≠ 0 := ne_of_gt hmmpos
  have hr : 0 ≤ 1 / (mm : ℝ) := by positivity
  have hNr : 1 ≤ N ^ (1 / (mm : ℝ)) := Real.one_le_rpow hN hr
  have hN0 : (0 : ℝ) ≤ N := le_trans zero_le_one hN
  have h1 : 1 ≤ Θ * N ^ (1 / (mm : ℝ)) := one_le_mul_of_one_le_of_one_le hΘ hNr
  refine ⟨h1, ?_, ?_⟩
  · have hcancel : 1 / (mm : ℝ) * (mm : ℝ) = 1 := one_div_mul_cancel hmmne
    rw [Real.mul_rpow (le_trans zero_le_one hΘ) (Real.rpow_nonneg hN0 _)]
    rw [← Real.rpow_mul hN0 (1 / (mm : ℝ)) (mm : ℝ)]
    rw [hcancel, Real.rpow_one, Real.rpow_natCast]
  · intro j hj
    have hKle : Θ * N ^ (1 / (mm : ℝ)) + 1 ≤ 2 * (Θ * N ^ (1 / (mm : ℝ))) := by linarith
    have h1' : 0 ≤ Θ * N ^ (1 / (mm : ℝ)) + 1 := by linarith
    have hNj : (N ^ (1 / (mm : ℝ))) ^ j = N ^ ((j : ℝ) / (mm : ℝ)) := by
      rw [← Real.rpow_natCast (N ^ (1 / (mm : ℝ))) j]
      rw [← Real.rpow_mul hN0 (1 / (mm : ℝ)) (j : ℝ)]
      congr 1
      rw [div_eq_mul_one_div]; ring
    calc (Θ * N ^ (1 / (mm : ℝ)) + 1) ^ j
        ≤ (2 * (Θ * N ^ (1 / (mm : ℝ)))) ^ j := pow_le_pow_left₀ h1' hKle j
      _ = 2 ^ j * (Θ * N ^ (1 / (mm : ℝ))) ^ j := by rw [mul_pow]
      _ = 2 ^ j * (Θ ^ j * (N ^ (1 / (mm : ℝ))) ^ j) := by rw [mul_pow]
      _ = 2 ^ j * Θ ^ j * N ^ ((j : ℝ) / (mm : ℝ)) := by rw [hNj]; ring

end Work.GM.Energy.EnergyCore2
