import Mathlib

namespace Work.FIArea7

/-- Pointwise bound: for `n ≥ 1`, `1/n ≤ 2 log((n+1)/n) = 2 (log(n+1) - log n)`.
This is the `2 log(1 + 1/n) ≥ 1/n` inequality obtained from `log x ≥ 1 - 1/x`
applied at `x = (n+1)/n`. -/
private lemma one_div_nat_le_two_log_succ_div (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℝ) / (n : ℝ) ≤ 2 * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hx : (0 : ℝ) < ((n : ℝ) + 1) / (n : ℝ) := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hx
  have hsimp : 1 - (((n : ℝ) + 1) / (n : ℝ))⁻¹ = 1 / ((n : ℝ) + 1) := by
    rw [inv_div]
    field_simp
    ring
  rw [hsimp] at h
  rw [Real.log_div (by positivity) (by positivity)] at h
  have h2 : (1 : ℝ) / (n : ℝ) ≤ 2 * (1 / ((n : ℝ) + 1)) := by
    rw [div_le_iff₀ hnpos]
    have hnn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have : 2 * (1 / ((n : ℝ) + 1)) * (n : ℝ) = 2 * (n : ℝ) / ((n : ℝ) + 1) := by ring
    rw [this, le_div_iff₀ hnn]
    linarith
  linarith

theorem sum_inv_Icc_le_two_log (B : ℕ) :
    (∑ b ∈ Finset.Icc 1 B, (1:ℝ) / (b : ℝ)) ≤ 2 * Real.log ((B : ℝ) + 2) := by
  rcases Nat.eq_zero_or_pos B with hB | hB
  · subst hB
    have h2 : (0:ℝ) ≤ 2 * Real.log ((0:ℝ) + 2) := by
      rw [zero_add]
      have hlog : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
    simpa using h2
  · -- Pointwise bound `1/b ≤ 2 (log (b+1) - log b)` for `b ≥ 1`.
    have hpt : ∀ b ∈ Finset.Icc 1 B,
        (1:ℝ)/(b:ℝ) ≤ 2 * (Real.log ((b:ℝ)+1) - Real.log (b:ℝ)) := by
      intro b hb
      exact one_div_nat_le_two_log_succ_div b (Finset.mem_Icc.mp hb).1
    -- The logarithmic terms telescope.
    have htel : ∑ b ∈ Finset.Icc 1 B, (Real.log ((b:ℝ)+1) - Real.log (b:ℝ))
        = Real.log ((B:ℝ)+1) - Real.log 1 := by
      rw [show (∑ b ∈ Finset.Icc 1 B, (Real.log ((b:ℝ)+1) - Real.log (b:ℝ)))
            = ∑ b ∈ Finset.Icc 1 B, (Real.log (((b+1:ℕ):ℝ)) - Real.log (((b:ℕ):ℝ))) from
          Finset.sum_congr rfl (fun b _ => by push_cast; ring)]
      rw [Finset.sum_Icc_sub hB (fun n : ℕ => Real.log (n:ℝ))]
      push_cast
      ring
    calc (∑ b ∈ Finset.Icc 1 B, (1:ℝ) / (b : ℝ))
        ≤ ∑ b ∈ Finset.Icc 1 B, 2 * (Real.log ((b:ℝ)+1) - Real.log (b:ℝ)) :=
          Finset.sum_le_sum hpt
      _ = 2 * (∑ b ∈ Finset.Icc 1 B, (Real.log ((b:ℝ)+1) - Real.log (b:ℝ))) := by
            rw [Finset.mul_sum]
      _ = 2 * (Real.log ((B:ℝ)+1) - Real.log 1) := by rw [htel]
      _ = 2 * Real.log ((B:ℝ)+1) := by simp
      _ ≤ 2 * Real.log ((B:ℝ)+2) := by
          have hlog : Real.log ((B:ℝ)+1) ≤ Real.log ((B:ℝ)+2) :=
            Real.log_le_log (by positivity) (by linarith)
          linarith

end Work.FIArea7
