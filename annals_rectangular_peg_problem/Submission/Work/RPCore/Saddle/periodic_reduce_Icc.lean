import Mathlib

namespace Work.RPCore.Saddle

theorem periodic_reduce_Icc {β : Type*} {f : ℝ → β} {c : ℝ} (hc : 0 < c)
    (hf : Function.Periodic f c) (a : ℝ) : ∃ a' ∈ Set.Icc 0 c, f a' = f a := by
  obtain ⟨a', ha', hfa'⟩ := hf.exists_mem_Ico hc a 0
  exact ⟨a', Set.Ico_subset_Icc_self (by simpa using ha'), hfa'.symm⟩

end Work.RPCore.Saddle
