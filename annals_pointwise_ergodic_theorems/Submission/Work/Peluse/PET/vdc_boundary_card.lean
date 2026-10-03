import Mathlib

namespace Work.Peluse.PET

/-- Counting bound for the boundary of a translate of an interval of integers:
the number of `y ∈ Icc 1 M` for which `y + a` leaves `Icc 1 M` is at most `|a|`. -/
theorem vdc_boundary_card (M : ℕ) (a : ℤ) :
    ((Finset.Icc (1 : ℤ) (M : ℤ)).filter
        (fun y => y + a ∉ Finset.Icc (1 : ℤ) (M : ℤ))).card ≤ a.natAbs := by
  by_cases ha : 0 ≤ a
  · -- `a ≥ 0`: the escaping `y` satisfy `M - a + 1 ≤ y ≤ M`.
    have hsub : (Finset.Icc (1:ℤ) (M:ℤ)).filter (fun y => y + a ∉ Finset.Icc (1:ℤ) (M:ℤ))
        ⊆ Finset.Icc (M - a + 1) (M:ℤ) := by
      intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨hy1, hy2⟩ := hy
      obtain ⟨hyge, hyle⟩ := Finset.mem_Icc.mp hy1
      refine Finset.mem_Icc.mpr ⟨?_, hyle⟩
      by_contra h
      rw [not_le] at h
      exact hy2 (Finset.mem_Icc.mpr ⟨by linarith, by linarith⟩)
    have h1 : ((Finset.Icc (1 : ℤ) (M : ℤ)).filter
          (fun y => y + a ∉ Finset.Icc (1 : ℤ) (M : ℤ))).card
        ≤ (Finset.Icc (M - a + 1) (M:ℤ)).card := Finset.card_le_card hsub
    rw [Int.card_Icc] at h1
    have h2 : ((M : ℤ) + 1 - (M - a + 1)).toNat = a.natAbs := by
      have h3 : (M : ℤ) + 1 - (M - a + 1) = a := by ring
      rw [h3]
      exact Int.ofNat_inj.mp (by rw [Int.toNat_of_nonneg ha, Int.natAbs_of_nonneg ha])
    rw [h2] at h1
    exact h1
  · -- `a < 0`: the escaping `y` satisfy `1 ≤ y ≤ -a`.
    have ha : a < 0 := not_le.mp ha
    have hsub : (Finset.Icc (1:ℤ) (M:ℤ)).filter (fun y => y + a ∉ Finset.Icc (1:ℤ) (M:ℤ))
        ⊆ Finset.Icc (1:ℤ) (-a) := by
      intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨hy1, hy2⟩ := hy
      obtain ⟨hyge, hyle⟩ := Finset.mem_Icc.mp hy1
      refine Finset.mem_Icc.mpr ⟨hyge, ?_⟩
      by_contra h
      rw [not_le] at h
      exact hy2 (Finset.mem_Icc.mpr ⟨by linarith, by linarith⟩)
    have h1 : ((Finset.Icc (1 : ℤ) (M : ℤ)).filter
          (fun y => y + a ∉ Finset.Icc (1 : ℤ) (M : ℤ))).card
        ≤ (Finset.Icc (1:ℤ) (-a)).card := Finset.card_le_card hsub
    rw [Int.card_Icc] at h1
    have h2 : ((-a : ℤ) + 1 - 1).toNat = a.natAbs := by
      have h3 : ((-a : ℤ) + 1 - 1) = -a := by ring
      rw [h3, ← Int.natAbs_neg a]
      exact Int.ofNat_inj.mp (by
        rw [Int.toNat_of_nonneg (by linarith), Int.natAbs_of_nonneg (by linarith)])
    rw [h2] at h1
    exact h1

end Work.Peluse.PET
