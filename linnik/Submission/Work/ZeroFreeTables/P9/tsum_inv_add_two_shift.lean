import Mathlib

namespace Work.ZeroFreeTables.P9

/-- For `k ≥ 1` and `1 < Re s` the series `∑_{n≥0} (1/(s+2n))^{k+1}` is summable, and splitting
off the `n = 0` term gives
`∑_{n≥0} (1/(s+2n))^{k+1} = (1/s)^{k+1} + ∑_{n≥0} (1/(s+2(n+1)))^{k+1}`.
(Standard: summability by comparison with `∑ 1/n^{k+1}`, then `Summable.tsum_eq_zero_add` plus
`2*(n+1) = 2*n + 2`.) -/
theorem tsum_inv_add_two_shift (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1)) ∧
      (∑' n : ℕ, (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1))
        = (1 / s) ^ (k + 1)
          + (∑' n : ℕ, (1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ (k + 1)) := by
  -- Comparison series `∑ 1/(n+1)^{k+1}`, summable as a shifted `p`-series with `p = k+1 > 1`.
  have hseries : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ (k + 1)) :=
    (summable_nat_add_iff (f := fun m : ℕ => 1 / (m : ℝ) ^ (k + 1)) 1).mpr
      ((Real.summable_one_div_nat_pow (p := k + 1)).mpr (by omega))
  -- Pointwise domination: `‖s + 2n‖ ≥ Re(s + 2n) = Re s + 2n ≥ n + 1`.
  have hbound : ∀ n : ℕ,
      ‖(1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1)‖ ≤ 1 / ((n + 1 : ℕ) : ℝ) ^ (k + 1) := by
    intro n
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hnorm : (n : ℝ) + 1 ≤ ‖s + ((2 * n : ℕ) : ℂ)‖ := by
      have hre : (s + ((2 * n : ℕ) : ℂ)).re = s.re + 2 * (n : ℝ) := by
        simp [Complex.add_re]
      calc (n : ℝ) + 1 ≤ s.re + 2 * (n : ℝ) := by linarith
        _ = (s + ((2 * n : ℕ) : ℂ)).re := hre.symm
        _ ≤ ‖s + ((2 * n : ℕ) : ℂ)‖ := Complex.re_le_norm _
    have hle : 1 / ‖s + ((2 * n : ℕ) : ℂ)‖ ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le hnpos hnorm
    calc ‖(1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1)‖
        = ‖1 / (s + ((2 * n : ℕ) : ℂ))‖ ^ (k + 1) := norm_pow _ _
      _ = (1 / ‖s + ((2 * n : ℕ) : ℂ)‖) ^ (k + 1) := by rw [norm_div, norm_one]
      _ ≤ (1 / ((n : ℝ) + 1)) ^ (k + 1) :=
            pow_le_pow_left₀ (by positivity) hle (k + 1)
      _ = 1 / ((n + 1 : ℕ) : ℝ) ^ (k + 1) := by
            rw [div_pow, one_pow, Nat.cast_add, Nat.cast_one]
  have hsum : Summable (fun n : ℕ => (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1)) :=
    Summable.of_norm_bounded hseries hbound
  refine ⟨hsum, ?_⟩
  -- Split off the `n = 0` term; the remaining summand is `f (n+1)` by definition.
  rw [hsum.tsum_eq_zero_add]
  congr 1
  simp

end Work.ZeroFreeTables.P9
