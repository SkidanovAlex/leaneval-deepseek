import Mathlib

namespace Work.FIArea7

/-- The purely numerical core: for every `N : ℕ`,
`(2N+1)·√N ≤ 4·(√N)^3 + 8`. -/
private lemma num_bound (N : ℕ) :
    ((2 * N + 1 : ℕ) : ℝ) * Real.sqrt (N : ℝ) ≤ 4 * Real.sqrt ((N : ℝ)) ^ 3 + 8 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have hx : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hz1 : 1 ≤ Real.sqrt (N : ℝ) := Real.one_le_sqrt.mpr hx
    have hz2 : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
    have hcast : ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    nlinarith [sq_nonneg (Real.sqrt (N : ℝ)), hz1, hz2]

/-- `∑_{|r| ≤ Rz, r odd, r ≠ 0} √|r| ≪ Rz^{3/2}` — the loss of summing the *FI* §22 per-`r` bound
`√(q|r|)` over the `r`-range (`Work.FIPlan.gBox` has `|r|, |s| ≤ Rz` so `N ≍ Rz²`). -/
theorem sum_sqrt_Icc_le (Rz : ℤ) :
    (∑ r ∈ (Finset.Icc (-Rz) Rz).filter (fun r : ℤ => Odd r ∧ r ≠ 0),
        Real.sqrt (|(r : ℝ)|))
      ≤ 4 * Real.sqrt (((max Rz 0).toNat : ℝ)) ^ 3 + 8 := by
  by_cases hR : 0 ≤ Rz
  · have hmax : max Rz 0 = Rz := max_eq_left hR
    have hNcast : ((Rz.toNat : ℕ) : ℝ) = (Rz : ℝ) :=
      by exact_mod_cast (Int.toNat_of_nonneg hR : (Rz.toNat : ℤ) = Rz)
    have h3 : (Rz + 1 - (-Rz)).toNat = 2 * Rz.toNat + 1 := by
      have h : Rz + 1 - (-Rz) = 2 * Rz + 1 := by ring
      rw [h]; omega
    set S : Finset ℤ := (Finset.Icc (-Rz) Rz).filter (fun r : ℤ => Odd r ∧ r ≠ 0) with hS
    have hcard : (S.card : ℝ) ≤ ((2 * Rz.toNat + 1 : ℕ) : ℝ) := by
      have hle : S.card ≤ 2 * Rz.toNat + 1 := by
        calc S.card ≤ (Finset.Icc (-Rz) Rz).card :=
              Finset.card_le_card (Finset.filter_subset _ _)
          _ = (Rz + 1 - (-Rz)).toNat := Int.card_Icc (-Rz) Rz
          _ = 2 * Rz.toNat + 1 := h3
      exact_mod_cast hle
    have hterm : ∀ r ∈ S, Real.sqrt (|(r : ℝ)|) ≤ Real.sqrt ((Rz.toNat : ℕ) : ℝ) := by
      intro r hr
      have hr' := Finset.mem_filter.mp hr
      have hrI := Finset.mem_Icc.mp hr'.1
      have habs : |(r : ℝ)| ≤ (Rz : ℝ) := by
        rw [abs_le]
        exact ⟨by exact_mod_cast hrI.1, by exact_mod_cast hrI.2⟩
      rw [hNcast]
      exact Real.sqrt_le_sqrt habs
    calc ∑ r ∈ S, Real.sqrt (|(r : ℝ)|)
        ≤ ∑ r ∈ S, Real.sqrt ((Rz.toNat : ℕ) : ℝ) := Finset.sum_le_sum hterm
      _ = S.card • Real.sqrt ((Rz.toNat : ℕ) : ℝ) := Finset.sum_const _
      _ = (S.card : ℝ) * Real.sqrt ((Rz.toNat : ℕ) : ℝ) := by rw [nsmul_eq_mul]
      _ ≤ ((2 * Rz.toNat + 1 : ℕ) : ℝ) * Real.sqrt ((Rz.toNat : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hcard (Real.sqrt_nonneg _)
      _ ≤ 4 * Real.sqrt (((Rz.toNat : ℕ) : ℝ)) ^ 3 + 8 := num_bound Rz.toNat
      _ = 4 * Real.sqrt (((max Rz 0).toNat : ℝ)) ^ 3 + 8 := by rw [hmax]
  · have hempty : Finset.Icc (-Rz) Rz = (∅ : Finset ℤ) := by
      rw [Finset.Icc_eq_empty_iff]; omega
    have hmax : max Rz 0 = 0 := by rw [max_eq_right]; omega
    rw [hempty, Finset.filter_empty, Finset.sum_empty, hmax]
    norm_num

end Work.FIArea7
