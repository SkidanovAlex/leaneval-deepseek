import Mathlib

namespace Work.Parab.sumInv

/-- The `n`-th harmonic number, cast to `ℝ`, written as a sum of reciprocals of
`(i : ℝ) + 1` for `i < n`. -/
private lemma harmonic_cast (n : ℕ) :
    (harmonic n : ℝ) = ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) := by
  rw [harmonic, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [one_div, Rat.cast_inv, Nat.cast_add, Nat.cast_one]

/-- Harmonic-number bound: for `c, R > 0` and every `k`,
`∑_{m < k} 1 / max R (c * m) ≤ 1 / R + (1 / c) * (1 + log k)`.

The `m = 0` term is `1 / R`; for `m ≥ 1` each term is at most `1 / (c * m)`, and
`∑_{m < k} 1 / (m + 1) ≤ harmonic k ≤ 1 + log k`. -/
theorem sum_inv_max_le {c R : ℝ} (hc : 0 < c) (hR : 0 < R) (k : ℕ) :
    ∑ m ∈ Finset.range k, 1 / max R (c * (m : ℝ)) ≤ 1 / R + (1 / c) * (1 + Real.log k) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have h1 : (0 : ℝ) < 1 / R := one_div_pos.mpr hR
    have h2 : (0 : ℝ) < 1 / c := one_div_pos.mpr hc
    simp only [Finset.sum_range_zero, Nat.cast_zero, Real.log_zero]
    linarith
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have hf0 : 1 / max R (c * ((0 : ℕ) : ℝ)) = 1 / R := by
    have h : max R (c * ((0 : ℕ) : ℝ)) = R := by
      rw [Nat.cast_zero, mul_zero, max_eq_left hR.le]
    rw [h]
  rw [hf0]
  have hmain : ∑ m ∈ Finset.range j, 1 / max R (c * ((m + 1 : ℕ) : ℝ))
      ≤ (1 / c) * (1 + Real.log ((j + 1 : ℕ) : ℝ)) := by
    calc ∑ m ∈ Finset.range j, 1 / max R (c * ((m + 1 : ℕ) : ℝ))
        ≤ ∑ m ∈ Finset.range j, 1 / (c * ((m + 1 : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro m _
          have hpos : (0 : ℝ) < c * ((m + 1 : ℕ) : ℝ) := by positivity
          exact one_div_le_one_div_of_le hpos (le_max_right _ _)
        _ = (1 / c) * ∑ m ∈ Finset.range j, 1 / ((m : ℝ) + 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m _
          have hm1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
          rw [hm1]
          field_simp
        _ ≤ (1 / c) * (1 + Real.log ((j + 1 : ℕ) : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hh : ∑ m ∈ Finset.range j, 1 / ((m : ℝ) + 1) ≤ (harmonic (j + 1) : ℝ) := by
            rw [harmonic_cast]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.range_mono (Nat.le_succ j)
            · intro i _ _
              positivity
          calc ∑ m ∈ Finset.range j, 1 / ((m : ℝ) + 1) ≤ (harmonic (j + 1) : ℝ) := hh
            _ ≤ 1 + Real.log ((j + 1 : ℕ) : ℝ) := harmonic_le_one_add_log (j + 1)
  linarith

end Work.Parab.sumInv
