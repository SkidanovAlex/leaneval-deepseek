import Mathlib
import Submission.Work.Commons.Analysis.Series.sum_Icc_sqrt_div_self_le

namespace Work.LinnikAreas.Density4.BzBilin

/-- Range-restricted form of the weighted Abel error bound: only the values `h m` for
`m ∈ Icc 1 M` must be bounded by `H`, and only the increments `h (m+1) - h m` for `1 ≤ m < M`
must be bounded by `L / m`.  Then the Abel-summed combination
`Δ M · h M + ∑_{m < M} (h m − h (m+1)) · Δ m` is bounded by `C (H + 2L) √M`. -/
theorem abel_weighted_difference_bound_range (Δ h : ℕ → ℝ) (M : ℕ) (C H L : ℝ)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hΔ : ∀ m : ℕ, |Δ m| ≤ C * Real.sqrt (m : ℝ))
    (hh : ∀ m : ℕ, m ∈ Finset.Icc 1 M → |h m| ≤ H)
    (hd : ∀ m : ℕ, 1 ≤ m → m < M → |h (m + 1) - h m| ≤ L / (m : ℝ)) :
    |Δ M * h M + ∑ m ∈ Finset.Icc 1 (M - 1), (h m - h (m + 1)) * Δ m|
      ≤ C * (H + 2 * L) * Real.sqrt (M : ℝ) := by
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · -- `M = 0`: the sum is empty and `hΔ 0` forces `Δ 0 = 0`.
    subst hM0
    have hΔ0 : Δ 0 = 0 := by
      have h : |Δ 0| ≤ 0 := by simpa using hΔ 0
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    rw [hΔ0]
    simp [Real.sqrt_zero]
  · have hCL_nn : 0 ≤ C * L := mul_nonneg hC hL
    have hMmem : M ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨hMpos, le_refl M⟩
    -- Outgoing boundary term.
    have h1 : |Δ M * h M| ≤ C * Real.sqrt (M : ℝ) * H := by
      rw [abs_mul]
      exact mul_le_mul (hΔ M) (hh M hMmem) (abs_nonneg _)
        (mul_nonneg hC (Real.sqrt_nonneg _))
    -- The Abel correction sum.
    have hsum_bound :
        |∑ m ∈ Finset.Icc 1 (M - 1), (h m - h (m + 1)) * Δ m|
          ≤ C * L * (2 * Real.sqrt (M : ℝ)) := by
      calc |∑ m ∈ Finset.Icc 1 (M - 1), (h m - h (m + 1)) * Δ m|
          ≤ ∑ m ∈ Finset.Icc 1 (M - 1), |(h m - h (m + 1)) * Δ m| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Finset.Icc 1 (M - 1), C * L * (Real.sqrt (m : ℝ) / (m : ℝ)) := by
            apply Finset.sum_le_sum
            intro m hm
            rw [Finset.mem_Icc] at hm
            have hm1 : 1 ≤ m := hm.1
            have hmM : m < M := by omega
            have hLm : 0 ≤ L / (m : ℝ) := div_nonneg hL (Nat.cast_nonneg m)
            have hsub : |h m - h (m + 1)| ≤ L / (m : ℝ) := by
              rw [abs_sub_comm]; exact hd m hm1 hmM
            calc |(h m - h (m + 1)) * Δ m|
                = |h m - h (m + 1)| * |Δ m| := abs_mul _ _
              _ ≤ (L / (m : ℝ)) * (C * Real.sqrt (m : ℝ)) :=
                  mul_le_mul hsub (hΔ m) (abs_nonneg _) hLm
              _ = C * L * (Real.sqrt (m : ℝ) / (m : ℝ)) := by ring
        _ = C * L * (∑ m ∈ Finset.Icc 1 (M - 1), Real.sqrt (m : ℝ) / (m : ℝ)) := by
            rw [Finset.mul_sum]
        _ ≤ C * L * (2 * Real.sqrt (M : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ hCL_nn
            calc (∑ m ∈ Finset.Icc 1 (M - 1), Real.sqrt (m : ℝ) / (m : ℝ))
                ≤ 2 * Real.sqrt (((M - 1 : ℕ)) : ℝ) :=
                  Work.Commons.Analysis.Series.sum_Icc_sqrt_div_self_le (M - 1)
              _ ≤ 2 * Real.sqrt (M : ℝ) := by
                  apply mul_le_mul_of_nonneg_left _ (by norm_num)
                  exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le M 1)
    calc |Δ M * h M + ∑ m ∈ Finset.Icc 1 (M - 1), (h m - h (m + 1)) * Δ m|
        ≤ |Δ M * h M| + |∑ m ∈ Finset.Icc 1 (M - 1), (h m - h (m + 1)) * Δ m| :=
          abs_add_le _ _
      _ ≤ C * Real.sqrt (M : ℝ) * H + C * L * (2 * Real.sqrt (M : ℝ)) :=
          add_le_add h1 hsum_bound
      _ = C * (H + 2 * L) * Real.sqrt (M : ℝ) := by ring

end Work.LinnikAreas.Density4.BzBilin

