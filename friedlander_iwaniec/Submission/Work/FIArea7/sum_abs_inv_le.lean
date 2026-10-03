import Mathlib

namespace Work.FIArea7

open Finset

/-- Every nonzero integer `k` with `|k| ≤ R` contributes `1/|k|`; the extremal set is
`{-R, ..., -1, 1, ..., R}`, whose contribution is `2 * harmonic R ≤ 2 * (1 + log R)`. -/
theorem sum_abs_inv_le (R : ℕ) (T : Finset ℤ)
    (hT : ∀ k ∈ T, (k : ℝ) ≠ 0 ∧ |(k : ℝ)| ≤ (R : ℝ)) :
    ∑ k ∈ T, 1 / |(k : ℝ)| ≤ 2 * (1 + Real.log (R : ℝ)) := by
  -- The fibre of `Int.natAbs` over `n` lies in `{n, -n}`, hence contributes at most `2/n`.
  have hfiber : ∀ n ∈ T.image Int.natAbs,
      ∑ k ∈ T.filter (fun k => k.natAbs = n), 1 / |(k : ℝ)| ≤ 2 / (n : ℝ) := by
    intro n hn
    obtain ⟨k₀, hk₀T, hk₀n⟩ := Finset.mem_image.mp hn
    have hk₀ne : k₀ ≠ 0 := Int.cast_ne_zero.mp (hT k₀ hk₀T).1
    have hnpos : 0 < n := by rw [← hk₀n]; exact Int.natAbs_pos.mpr hk₀ne
    have hne : (n : ℤ) ≠ -(n : ℤ) := by omega
    have hsub : T.filter (fun k => k.natAbs = n) ⊆ ({(n : ℤ), -(n : ℤ)} : Finset ℤ) := by
      intro k hk
      simp only [Finset.mem_filter] at hk
      obtain ⟨_, hkn⟩ := hk
      rcases Int.natAbs_eq k with h | h
      · rw [h, hkn]; simp
      · rw [h, hkn]; simp
    calc ∑ k ∈ T.filter (fun k => k.natAbs = n), 1 / |(k : ℝ)|
        ≤ ∑ k ∈ ({(n : ℤ), -(n : ℤ)} : Finset ℤ), 1 / |(k : ℝ)|
            := Finset.sum_le_sum_of_subset_of_nonneg hsub
                 (fun k _ _ => div_nonneg zero_le_one (abs_nonneg _))
      _ = 2 / (n : ℝ) := by
          rw [Finset.sum_pair hne]
          have h1 : |(((n : ℤ)) : ℝ)| = (n : ℝ) := by
            push_cast; rw [abs_of_nonneg (Nat.cast_nonneg n)]
          rw [show ((-(n : ℤ) : ℤ) : ℝ) = -(n : ℝ) from by push_cast; ring]
          rw [abs_neg, h1, abs_of_nonneg (Nat.cast_nonneg n), ← add_div]
          norm_num
  calc ∑ k ∈ T, 1 / |(k : ℝ)|
      = ∑ n ∈ T.image Int.natAbs, ∑ k ∈ T.filter (fun k => k.natAbs = n), 1 / |(k : ℝ)|
          := (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi) _).symm
    _ ≤ ∑ n ∈ T.image Int.natAbs, 2 / (n : ℝ) := Finset.sum_le_sum hfiber
    _ ≤ ∑ n ∈ Finset.Icc 1 R, 2 / (n : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => by positivity)
        intro n hn
        obtain ⟨k, hkT, hkn⟩ := Finset.mem_image.mp hn
        obtain ⟨hne, hle⟩ := hT k hkT
        rw [← hkn, Finset.mem_Icc]
        refine ⟨?_, ?_⟩
        · have hk0 : k ≠ 0 := Int.cast_ne_zero.mp hne
          have := Int.natAbs_pos.mpr hk0
          omega
        · have h2 : (k.natAbs : ℝ) ≤ (R : ℝ) := by
            rw [Nat.cast_natAbs, Int.cast_abs]; exact hle
          exact_mod_cast h2
    _ = 2 * (harmonic R : ℝ) := by
        have h : (harmonic R : ℝ) = ∑ i ∈ Finset.Icc 1 R, (i : ℝ)⁻¹ := by
          rw [harmonic_eq_sum_Icc, Rat.cast_sum]; simp [Rat.cast_inv]
        rw [h, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        ring
    _ ≤ 2 * (1 + Real.log (R : ℝ)) := by
        have := harmonic_le_one_add_log R
        linarith

end Work.FIArea7
