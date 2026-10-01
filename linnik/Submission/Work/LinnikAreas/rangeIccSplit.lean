import Mathlib

namespace Work.LinnikAreas

/-- Splitting the weighted cosine sum at `m = 0`: for `N ≥ 1`,
`∑_{m < N} (N - m) cos (mθ) = N + ∑_{1 ≤ m ≤ N-1} (N - m) cos (mθ)`. -/
theorem rangeIccSplit (θ : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∑ m ∈ Finset.range N, ((N : ℝ) - (m : ℝ)) * Real.cos ((m : ℝ) * θ)
      = (N : ℝ) + ∑ m ∈ Finset.Icc 1 (N - 1), ((N : ℝ) - (m : ℝ)) * Real.cos ((m : ℝ) * θ) := by
  have h : Finset.range N = insert 0 (Finset.Icc 1 (N - 1)) := by
    ext m
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    constructor
    · intro hm
      by_cases h0 : m = 0
      · exact Or.inl h0
      · exact Or.inr ⟨by omega, by omega⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact hN
      · omega
  rw [h, Finset.sum_insert (by simp)]
  simp

end Work.LinnikAreas
