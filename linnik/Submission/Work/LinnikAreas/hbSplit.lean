import Mathlib

namespace Work.LinnikAreas

/-- Splitting an `Icc` sum in two consecutive blocks: for `a ≤ s + 1` and `s ≤ m`,
`∑_{a ≤ i ≤ m} g i = ∑_{a ≤ i ≤ s} g i + ∑_{s+1 ≤ i ≤ m} g i`. -/
theorem hbSplit (g : ℕ → ℂ) {a m s : ℕ} (ha : a ≤ s + 1) (hs : s ≤ m) :
    ∑ i ∈ Finset.Icc a m, g i = (∑ i ∈ Finset.Icc a s, g i) + ∑ i ∈ Finset.Icc (s + 1) m, g i := by
  have h : Finset.Icc a m = Finset.Icc a s ∪ Finset.Icc (s + 1) m := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Icc a s) (Finset.Icc (s + 1) m) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_Icc] at hx hx'
    omega
  rw [h, Finset.sum_union hd]

end Work.LinnikAreas
