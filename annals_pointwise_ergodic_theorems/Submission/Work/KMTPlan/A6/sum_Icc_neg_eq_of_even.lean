import Mathlib

namespace Work.KMTPlan.A6

/-- Summing an even function `g` over the negative interval
`[-M, -(K+1)]` equals summing it over `[K+1, M]`: the involution `p ↦ -p`
maps the second index set bijectively onto the first, and `g (-p) = g p`.
(When `M ≤ K` both index sets are empty and the identity is trivial.) -/
theorem sum_Icc_neg_eq_of_even (g : ℤ → ℝ) (heven : ∀ p, g (-p) = g p) (K M : ℕ) :
    ∑ p ∈ Finset.Icc (-(M : ℤ)) (-((K : ℤ) + 1)), g p
      = ∑ p ∈ Finset.Icc ((K : ℤ) + 1) (M : ℤ), g p := by
  have hset : Finset.Icc (-(M : ℤ)) (-((K : ℤ) + 1))
      = (Finset.Icc ((K : ℤ) + 1) (M : ℤ)).image (fun p : ℤ => -p) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨-x, ⟨by omega, by omega⟩, by simp⟩
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
      exact ⟨by omega, by omega⟩
  rw [hset, Finset.sum_image]
  · exact Finset.sum_congr rfl (fun p _ => heven p)
  · intro x _ y _ h
    exact neg_injective h

end Work.KMTPlan.A6
