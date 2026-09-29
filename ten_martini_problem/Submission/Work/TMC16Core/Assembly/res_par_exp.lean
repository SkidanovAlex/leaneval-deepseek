import Mathlib

namespace Work.TMC16Core.Assembly

/-- Exponential beats any polynomial: for every `δ > 0` and constant `C`, eventually
`8 * m * exp C < exp (m * δ)`. -/
theorem res_par_exp {δ C : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → 8 * (m : ℝ) * Real.exp C < Real.exp ((m : ℝ) * δ) := by
  have hδ1 : (1 : ℝ) < Real.exp δ := Real.one_lt_exp_iff.mpr hδ
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt 1 hδ1).const_mul (8 * Real.exp C)
  have hmem : Set.Iio (1 : ℝ) ∈ nhds ((8 * Real.exp C) * 0) := by
    simpa using Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)
  have hev : ∀ᶠ k : ℕ in Filter.atTop,
      (8 * Real.exp C) * ((k : ℝ) ^ 1 / (Real.exp δ) ^ k) < 1 :=
    ht.eventually hmem
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N, fun m hm => ?_⟩
  have hm1 := hN m hm
  rw [pow_one] at hm1
  rw [← mul_div_assoc] at hm1
  have hr : 0 < (Real.exp δ) ^ m := pow_pos (Real.exp_pos δ) m
  rw [div_lt_iff₀ hr, one_mul] at hm1
  rw [Real.exp_nat_mul]
  have hre : 8 * (m : ℝ) * Real.exp C = (8 * Real.exp C) * (m : ℝ) := by ring
  rw [hre]
  exact hm1

end Work.TMC16Core.Assembly
