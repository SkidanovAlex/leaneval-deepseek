import Mathlib

namespace Work.FIArea7

theorem card_filter_mul_le (N t : ℕ) (ht : 1 ≤ t) :
    ((((Finset.Icc 1 N).filter (fun κ => κ * t ≤ N)).card : ℕ) : ℝ) ≤ (N : ℝ) / (t : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hsub : (Finset.Icc 1 N).filter (fun κ => κ * t ≤ N) ⊆ Finset.Icc 1 (N / t) := by
    intro κ hκ
    rw [Finset.mem_filter] at hκ
    obtain ⟨hκI, hκm⟩ := hκ
    rw [Finset.mem_Icc] at hκI ⊢
    exact ⟨hκI.1, (Nat.le_div_iff_mul_le ht0).mpr hκm⟩
  have hcard : ((Finset.Icc 1 N).filter (fun κ => κ * t ≤ N)).card ≤ N / t := by
    calc ((Finset.Icc 1 N).filter (fun κ => κ * t ≤ N)).card
        ≤ (Finset.Icc 1 (N / t)).card := Finset.card_le_card hsub
      _ = N / t := by simp
  calc ((((Finset.Icc 1 N).filter (fun κ => κ * t ≤ N)).card : ℕ) : ℝ)
      ≤ ((N / t : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ (N : ℝ) / (t : ℝ) := Nat.cast_div_le

end Work.FIArea7
