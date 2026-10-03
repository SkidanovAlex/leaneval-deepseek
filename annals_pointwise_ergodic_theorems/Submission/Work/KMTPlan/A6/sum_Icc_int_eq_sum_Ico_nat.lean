import Mathlib

namespace Work.KMTPlan.A6

/-- Reindexing a sum over an integer interval `[K+1, M]` (K, M natural numbers)
as a sum over `n ∈ Ico K M` of the corresponding shifted term `g (n+1)`.
The map `n ↦ ((n+1 : ℕ) : ℤ)` is a bijection between `Finset.Ico K M` and
`Finset.Icc ((K : ℤ) + 1) (M : ℤ)`. -/
theorem sum_Icc_int_eq_sum_Ico_nat (g : ℤ → ℝ) (K M : ℕ) :
    ∑ p ∈ Finset.Icc ((K : ℤ) + 1) (M : ℤ), g p
      = ∑ n ∈ Finset.Ico K M, g (((n + 1 : ℕ) : ℤ)) := by
  symm
  refine Finset.sum_bij (fun n _ => ((n + 1 : ℕ) : ℤ)) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Ico] at hn
    simp only [Finset.mem_Icc]
    omega
  · intro n m hn hm h
    simp only [Finset.mem_Ico] at hn hm
    omega
  · intro p hp
    simp only [Finset.mem_Icc] at hp
    refine ⟨p.toNat - 1, ?_, ?_⟩
    · simp only [Finset.mem_Ico]
      omega
    · omega
  · intro n hn
    rfl

end Work.KMTPlan.A6
