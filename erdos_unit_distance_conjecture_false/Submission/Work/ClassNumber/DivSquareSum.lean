import Mathlib

namespace Work.ClassNumber

/-- The truncated harmonic series of squares is bounded by `2`:
`∑_{d=1}^{m} 1/d² ≤ 2`, proved by comparison with the telescoping series
`∑_{d=1}^{m} 2/(d(d+1)) = 2(1 - 1/(m+1))`. -/
theorem sum_one_div_sq_le_two (m : ℕ) : ∑ d ∈ Finset.Icc 1 m, (1 : ℝ) / d ^ 2 ≤ 2 := by
  have tele : ∀ n : ℕ,
      ∑ d ∈ Finset.Icc 1 n, (1 : ℝ) / (d * (d + 1)) = 1 - 1 / (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
      have h1 : (↑n : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (↑n : ℝ) + 1 + 1 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
  calc ∑ d ∈ Finset.Icc 1 m, (1 : ℝ) / d ^ 2
      ≤ ∑ d ∈ Finset.Icc 1 m, (2 : ℝ) * (1 / (d * (d + 1))) := by
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨hd1, -⟩ := Finset.mem_Icc.mp hd
        have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
        have h1 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
        have h2 : (0 : ℝ) < (d : ℝ) * (d + 1) := by positivity
        rw [show (2 : ℝ) * (1 / ((d : ℝ) * (d + 1))) = 2 / ((d : ℝ) * (d + 1)) by ring,
          div_le_div_iff₀ h1 h2]
        have hd1r : (1 : ℝ) ≤ d := by exact_mod_cast hd1
        nlinarith [mul_nonneg (le_of_lt hdpos) (sub_nonneg.mpr hd1r)]
    _ = 2 * ∑ d ∈ Finset.Icc 1 m, (1 : ℝ) / (d * (d + 1)) := (Finset.mul_sum _ _ _).symm
    _ = 2 * (1 - 1 / (m + 1)) := by rw [tele m]
    _ ≤ 2 := by
        have h3 : (0 : ℝ) ≤ 1 / (m + 1 : ℝ) := by positivity
        linarith

/-- `∑_{d=1}^{m} ⌊m/d⌋² ≤ 2 m²`: cast to ℝ, bound `⌊m/d⌋ ≤ m/d` termwise,
factor out `m²`, and use `∑ 1/d² ≤ 2`. -/
theorem DivSquareSum (m : ℕ) : ∑ d ∈ Finset.Icc 1 m, (m / d) ^ 2 ≤ 2 * m ^ 2 := by
  have h : ((∑ d ∈ Finset.Icc 1 m, (m / d) ^ 2 : ℕ) : ℝ) ≤ ((2 * m ^ 2 : ℕ) : ℝ) := by
    push_cast
    calc ∑ d ∈ Finset.Icc 1 m, ((m / d : ℕ) : ℝ) ^ 2
        ≤ ∑ d ∈ Finset.Icc 1 m, ((m : ℝ) / d) ^ 2 := by
          apply Finset.sum_le_sum
          intro d _
          have hcast : ((m / d : ℕ) : ℝ) ≤ (m : ℝ) / d := Nat.cast_div_le
          have hpos : (0 : ℝ) ≤ ((m / d : ℕ) : ℝ) := by positivity
          exact pow_le_pow_left₀ hpos hcast 2
      _ = (m : ℝ) ^ 2 * ∑ d ∈ Finset.Icc 1 m, (1 : ℝ) / d ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          obtain ⟨hd1, -⟩ := Finset.mem_Icc.mp hd
          have hd0 : (d : ℝ) ≠ 0 := by
            have hd1' : d ≠ 0 := by omega
            exact_mod_cast hd1'
          field_simp
      _ ≤ (m : ℝ) ^ 2 * 2 := by
          exact mul_le_mul_of_nonneg_left (sum_one_div_sq_le_two m) (by positivity)
      _ = 2 * (m : ℝ) ^ 2 := by ring
  exact_mod_cast h

end Work.ClassNumber
