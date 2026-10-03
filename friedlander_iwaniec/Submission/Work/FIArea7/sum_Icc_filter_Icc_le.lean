import Mathlib

namespace Work.FIArea7

theorem sum_Icc_filter_Icc_le {M : Type*} [AddCommMonoid M] (N Y : ℕ) (hYN : Y ≤ N) (G : ℕ → M) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ≤ Y), G n)
      = ∑ n ∈ Finset.Icc 1 Y, G n := by
  have h : (Finset.Icc 1 N).filter (fun n => n ≤ Y) = Finset.Icc 1 Y := by
    apply Finset.ext
    intro n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [h]

end Work.FIArea7
