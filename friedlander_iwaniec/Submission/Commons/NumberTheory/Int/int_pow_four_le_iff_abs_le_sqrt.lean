import Mathlib.Analysis.Real.Sqrt

namespace Commons.NumberTheory.Int

theorem int_pow_four_le_iff_abs_le_sqrt (x : ℕ) (hx : 1 ≤ x) (b : ℤ) : b ^ 4 ≤ (x : ℤ) ↔ |(b : ℝ)| ≤ Real.sqrt (Real.sqrt (x : ℝ)) := by
  have hxR : (0 : ℝ) < (x : ℝ) := by
    have : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    linarith
  -- the fourth power of the iterated square root of `x`
  have hsq : (Real.sqrt (Real.sqrt (x : ℝ))) ^ 4 = (x : ℝ) := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt (le_of_lt hxR)]
  have hcast : ((b ^ 4 : ℤ) : ℝ) = (b : ℝ) ^ 4 := by push_cast; ring
  have hcastx : ((x : ℤ) : ℝ) = (x : ℝ) := by push_cast; ring
  have habs : |(b : ℝ)| ^ 4 = (b : ℝ) ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs]
    ring
  constructor
  · intro h
    have h1 : (b : ℝ) ^ 4 ≤ (x : ℝ) := by
      rw [← hcast, ← hcastx]
      exact Int.cast_le.mpr h
    have h2 : |(b : ℝ)| ^ 4 ≤ (x : ℝ) := by rwa [← habs] at h1
    have key : |(b : ℝ)| ^ 4 ≤ (Real.sqrt (Real.sqrt (x : ℝ))) ^ 4 ↔
        |(b : ℝ)| ≤ Real.sqrt (Real.sqrt (x : ℝ)) :=
      pow_le_pow_iff_left₀ (a := |(b : ℝ)|) (b := Real.sqrt (Real.sqrt (x : ℝ))) (n := 4)
        (abs_nonneg _) (Real.sqrt_nonneg _) (by norm_num)
    rw [hsq] at key
    exact key.mp h2
  · intro h
    have h2 : |(b : ℝ)| ^ 4 ≤ (Real.sqrt (Real.sqrt (x : ℝ))) ^ 4 :=
      pow_le_pow_left₀ (abs_nonneg _) h 4
    rw [hsq, habs] at h2
    have h1 : ((b ^ 4 : ℤ) : ℝ) ≤ ((x : ℤ) : ℝ) := by
      rw [hcast, hcastx]
      exact h2
    exact Int.cast_le.mp h1

end Commons.NumberTheory.Int