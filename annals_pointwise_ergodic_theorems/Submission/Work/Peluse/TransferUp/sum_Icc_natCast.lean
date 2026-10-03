import Mathlib

namespace Work.Peluse.TransferUp

/-- Reindexing a sum over the integer interval `[1, H]` as a sum over the natural
interval `[1, H]`: the two sums are equal under `n ↦ (n : ℤ)`. -/
theorem sum_Icc_natCast {H : ℕ} (g : ℤ → ℂ) :
    (∑ n ∈ Finset.Icc (1 : ℤ) (H : ℤ), g n) = ∑ n ∈ Finset.Icc 1 H, g (n : ℤ) := by
  refine (Finset.sum_bij' (fun n (_ : n ∈ Finset.Icc 1 H) => (n : ℤ))
    (fun m (_ : m ∈ Finset.Icc (1 : ℤ) (H : ℤ)) => m.toNat) ?_ ?_ ?_ ?_ ?_).symm
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro m hm
    simp only [Finset.mem_Icc] at hm ⊢
    exact ⟨(Int.le_toNat (by omega)).mpr hm.1, (Int.toNat_le).mpr hm.2⟩
  · intro n _
    simp
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    exact Int.toNat_of_nonneg (by omega)
  · intro n _
    rfl

end Work.Peluse.TransferUp
