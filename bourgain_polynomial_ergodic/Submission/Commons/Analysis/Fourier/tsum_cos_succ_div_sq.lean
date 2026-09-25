import Mathlib.NumberTheory.ZetaValues

/-!
# The Fourier series `∑_{k≥1} cos (k θ) / k²`

For `0 ≤ θ ≤ 2π` we have the classical Fourier expansion

  `∑_{k ≥ 1} cos (k θ) / k² = π²/6 - π θ/2 + θ²/4`,

which is the Fourier series of the second Bernoulli polynomial.  We obtain it from
Mathlib's `hasSum_one_div_nat_pow_mul_cos` (the Fourier expansion of the Bernoulli
polynomials) specialised to `k = 1`, reindexing the natural-number sum to drop the
vanishing `n = 0` term.
-/

namespace Commons.Analysis.Fourier

theorem tsum_cos_succ_div_sq {θ : ℝ} (h0 : 0 ≤ θ) (h2 : θ ≤ 2 * Real.pi) :
    (∑' k : ℕ, Real.cos (((k : ℝ) + 1) * θ) / ((k : ℝ) + 1) ^ 2)
      = Real.pi ^ 2 / 6 - Real.pi * θ / 2 + θ ^ 2 / 4 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  -- Substitute `x = θ / (2π)` so that the Mathlib theorem applies.
  set x : ℝ := θ / (2 * Real.pi) with hxdef
  have hxmem : x ∈ Set.Icc (0 : ℝ) 1 := by
    rw [Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · rw [hxdef]; positivity
    · rw [hxdef, div_le_one (by positivity)]; linarith
  -- Fourier expansion of the second Bernoulli polynomial.
  have h := hasSum_one_div_nat_pow_mul_cos (k := 1) (by norm_num) hxmem
  have hf : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * x)) :=
    h.summable
  -- Reindex the natural-number sum: the `n = 0` term vanishes, and the remaining
  -- terms `f (k+1)` are exactly our summands.
  rw [show (∑' k : ℕ, Real.cos (((k : ℝ) + 1) * θ) / ((k : ℝ) + 1) ^ 2)
        = ∑' n : ℕ, 1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * x) from ?_]
  · -- Evaluate the closed form at `k = 1`.
    rw [h.tsum_eq]
    have hbern : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * 1))).eval x
        = x ^ 2 - x + 1 / 6 := by
      norm_num only [Nat.reduceMul]
      simp only [Polynomial.bernoulli, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      norm_num [Polynomial.map_add]
      ring
    rw [hbern, hxdef]
    field_simp
    ring
  · rw [hf.tsum_eq_zero_add]
    have hz : (1 / (((0 : ℕ) : ℝ)) ^ 2 * Real.cos (2 * Real.pi * ((0 : ℕ) : ℝ) * x)) = 0 := by
      simp
    rw [hz, zero_add]
    apply tsum_congr
    intro k
    rw [Nat.cast_add, Nat.cast_one]
    have harg : 2 * Real.pi * ((k : ℝ) + 1) * x = ((k : ℝ) + 1) * θ := by
      rw [hxdef]; field_simp
    rw [harg]
    ring

end Commons.Analysis.Fourier