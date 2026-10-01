import Mathlib

namespace Work.LinnikAreas.turanAux2

theorem invSqShiftSeriesLe (a : ℕ) (w : ℂ) (hw : (3 / 2 : ℝ) ≤ w.re) :
    Summable (fun n : ℕ => (1 : ℝ) / ‖w - (-(((a + 2 * n : ℕ) : ℂ)))‖ ^ 2) ∧
      (∀ n : ℕ, (1 : ℝ) / ‖w - (-(((a + 2 * n : ℕ) : ℂ)))‖ ^ 2
        ≤ (1 : ℝ) / ((3 / 2 : ℝ) + 2 * n) ^ 2) ∧
      (∑' n : ℕ, (1 : ℝ) / ‖w - (-(((a + 2 * n : ℕ) : ℂ)))‖ ^ 2)
        ≤ ∑' n : ℕ, (1 : ℝ) / ((3 / 2 : ℝ) + 2 * n) ^ 2 := by
  -- Pointwise bound: the modulus of `w - (-(a+2n))` dominates `3/2 + 2n`.
  have hpt : ∀ n : ℕ, (1 : ℝ) / ‖w - (-(((a + 2 * n : ℕ) : ℂ)))‖ ^ 2
        ≤ (1 : ℝ) / ((3 / 2 : ℝ) + 2 * n) ^ 2 := by
    intro n
    have hkey : ((3 / 2 : ℝ) + 2 * n) ≤ ‖w - (-(((a + 2 * n : ℕ) : ℂ)))‖ := by
      have hre : (w - (-(((a + 2 * n : ℕ) : ℂ)))).re
          = w.re + ((a : ℝ) + 2 * (n : ℝ)) := by
        simp [Complex.sub_re, Complex.neg_re, Complex.natCast_re,
          Nat.cast_add, Nat.cast_mul]
        ring
      have hle : ((3 / 2 : ℝ) + 2 * n) ≤ (w - (-(((a + 2 * n : ℕ) : ℂ)))).re := by
        rw [hre]
        have ha : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
        linarith
      calc ((3 / 2 : ℝ) + 2 * n) ≤ (w - (-(((a + 2 * n : ℕ) : ℂ)))).re := hle
        _ ≤ ‖w - (-(((a + 2 * n : ℕ) : ℂ)))‖ := Complex.re_le_norm _
    have h0 : (0 : ℝ) < (3 / 2 : ℝ) + 2 * n := by positivity
    have hsq : ((3 / 2 : ℝ) + 2 * n) ^ 2 ≤ ‖w - (-(((a + 2 * n : ℕ) : ℂ)))‖ ^ 2 :=
      pow_le_pow_left₀ (le_of_lt h0) hkey 2
    exact one_div_le_one_div_of_le (pow_pos h0 2) hsq
  -- Summability of the comparison series `∑ 1/(3/2+2n)^2`, dominated by `∑ 1/(n+1)^2`.
  have hgle : ∀ n : ℕ, (1 : ℝ) / ((3 / 2 : ℝ) + 2 * n) ^ 2
      ≤ (1 : ℝ) / ((n : ℝ) + 1) ^ 2 := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hle : (n : ℝ) + 1 ≤ (3 / 2 : ℝ) + 2 * n := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hsq : ((n : ℝ) + 1) ^ 2 ≤ ((3 / 2 : ℝ) + 2 * n) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hpos) hle 2
    exact one_div_le_one_div_of_le (pow_pos hpos 2) hsq
  have hh : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
    have hbase : Summable (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hshift :=
      (summable_nat_add_iff (f := fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ 2) 1).mpr hbase
    simpa using hshift
  have hg : Summable (fun n : ℕ => (1 : ℝ) / ((3 / 2 : ℝ) + 2 * n) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hgle hh
  have hf : Summable (fun n : ℕ => (1 : ℝ) / ‖w - (-(((a + 2 * n : ℕ) : ℂ)))‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hpt hg
  exact ⟨hf, hpt, Summable.tsum_le_tsum hpt hf hg⟩

end Work.LinnikAreas.turanAux2
