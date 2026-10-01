import Mathlib

namespace Work.LinnikAreas.Density4

/-- The harmonic block over `{a+1, …, b}` with `b ≤ 2*a+1` is at most `log 3`.
This is the elementary estimate `∑_{m=a+1}^{b} 1/m ≤ log(b/a) ≤ log 3`, the
first inequality following from `1/m ≤ log m - log (m-1)` (equivalently
`log(1 + 1/(m-1)) ≥ 1/m`) and telescoping. -/
theorem harmonic_block_bound (a b : ℕ) (ha : 1 ≤ a) (h2 : b ≤ 2 * a + 1) :
    ∑ m ∈ Finset.Icc (a + 1) b, (1 : ℝ) / (m : ℝ) ≤ Real.log 3 := by
  by_cases hab : a + 1 ≤ b
  · -- nonempty block: bound each term by the telescoping difference of logs
    have hpoint : ∀ m ∈ Finset.Icc (a + 1) b,
        (1 : ℝ) / (m : ℝ) ≤ Real.log (m : ℝ) - Real.log ((m - 1 : ℕ) : ℝ) := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      obtain ⟨hm1, hm2⟩ := hm
      have hm1a : 1 ≤ m := by omega
      have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show (0:ℕ) < m by omega)
      have hpos1 : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show (0:ℕ) < m - 1 by omega)
      have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub hm1a, Nat.cast_one]
      have hlog : Real.log ((m : ℝ) / ((m - 1 : ℕ) : ℝ))
          = Real.log (m : ℝ) - Real.log ((m - 1 : ℕ) : ℝ) :=
        Real.log_div hpos.ne' hpos1.ne'
      have hkey : (1 : ℝ) / (m : ℝ) = 1 - ((m : ℝ) / ((m - 1 : ℕ) : ℝ))⁻¹ := by
        rw [hcast]
        have hm10 : (m : ℝ) - 1 ≠ 0 := by
          have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show (1:ℕ) < m by omega)
          linarith
        field_simp
        ring
      rw [← hlog, hkey]
      exact Real.one_sub_inv_le_log_of_pos (by positivity)
    calc ∑ m ∈ Finset.Icc (a + 1) b, (1 : ℝ) / (m : ℝ)
        ≤ ∑ m ∈ Finset.Icc (a + 1) b,
            (Real.log (m : ℝ) - Real.log ((m - 1 : ℕ) : ℝ)) := Finset.sum_le_sum hpoint
      _ = Real.log (b : ℝ) - Real.log (a : ℝ) := by
          have := Finset.sum_Icc_sub (m := a + 1) (n := b) hab
            (fun i => Real.log (((i - 1 : ℕ) : ℝ)))
          simpa using this
      _ = Real.log ((b : ℝ) / (a : ℝ)) := by
          rw [Real.log_div (by exact_mod_cast (show b ≠ 0 by omega))
                (by exact_mod_cast (show a ≠ 0 by omega))]
      _ ≤ Real.log 3 := by
          have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show (0:ℕ) < b by omega)
          have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (show (0:ℕ) < a by omega)
          have hba : (b : ℝ) / (a : ℝ) ≤ 3 := by
            rw [div_le_iff₀ hapos]
            exact_mod_cast (show b ≤ 3 * a by omega)
          exact Real.log_le_log (div_pos hbpos hapos) hba
  · -- empty block: the sum vanishes and `log 3 > 0`
    rw [Finset.Icc_eq_empty_iff.mpr hab, Finset.sum_empty]
    exact Real.log_nonneg (by norm_num)

end Work.LinnikAreas.Density4
