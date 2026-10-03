import Mathlib

namespace Work.FIArea2.Count

/-- Pointwise bound: for `H ≥ 1` and `n : ℕ`, the term `(1 + n/H)^(-3/2)` is bounded by
`H^(3/2) (n+1)^(-3/2)`. -/
private lemma nat_bound (H : ℝ) (hH : 1 ≤ H) (n : ℕ) :
    (1 + |(n : ℝ)| / H) ^ (-(3/2 : ℝ))
      ≤ H ^ (3/2 : ℝ) * ((n : ℝ) + 1) ^ (-(3/2 : ℝ)) := by
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  rw [abs_of_nonneg (Nat.cast_nonneg n)]
  have h1 : (1 : ℝ) / H ≤ 1 := by rw [div_le_one hH0]; exact hH
  have hle : ((n : ℝ) + 1) / H ≤ 1 + (n : ℝ) / H := by
    have : ((n : ℝ) + 1) / H = (n : ℝ) / H + 1 / H := by ring
    rw [this]; linarith
  have h3 : (1 + (n : ℝ) / H) ^ (-(3/2 : ℝ)) ≤ (((n : ℝ) + 1) / H) ^ (-(3/2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hle (by norm_num)
  have h4 : (((n : ℝ) + 1) / H) ^ (-(3/2 : ℝ))
      = H ^ (3/2 : ℝ) * ((n : ℝ) + 1) ^ (-(3/2 : ℝ)) := by
    rw [Real.div_rpow (by positivity) (le_of_lt hH0), Real.rpow_neg (le_of_lt hH0)]
    simp only [div_eq_mul_inv, inv_inv]
    ring
  exact h3.trans h4.le

theorem summable_int_rpow_majorant (H : ℝ) (hH : 1 ≤ H) :
    Summable (fun h : ℤ => (1 + |(h : ℝ)| / H) ^ (-(3/2 : ℝ))) := by
  -- Summability of the majorant `H^(3/2) * (n+1)^(-3/2)` on `ℕ`, a shifted `p`-series.
  have hnat : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(3/2 : ℝ))) := by
    have hbase : Summable (fun m : ℕ => ((m : ℝ)) ^ (-(3/2 : ℝ))) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    have hshift := (summable_nat_add_iff 1).mpr hbase
    simpa only [Nat.cast_add, Nat.cast_one] using hshift
  have hmaj : Summable (fun n : ℕ => H ^ (3/2 : ℝ) * ((n : ℝ) + 1) ^ (-(3/2 : ℝ))) :=
    hnat.mul_left _
  -- The `ℕ`-indexed piece is summable by comparison.
  have aux : Summable (fun n : ℕ => (1 + |(n : ℝ)| / H) ^ (-(3/2 : ℝ))) := by
    apply Summable.of_nonneg_of_le
      (f := fun n : ℕ => H ^ (3/2 : ℝ) * ((n : ℝ) + 1) ^ (-(3/2 : ℝ)))
    · intro n; positivity
    · intro n; exact nat_bound H hH n
    · exact hmaj
  -- Split the sum over `ℤ` into its nonnegative and negative parts.
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨?_, ?_⟩
  · simpa only [Int.cast_natCast] using aux
  · simpa only [Int.cast_neg, Int.cast_natCast, abs_neg] using aux

end Work.FIArea2.Count
