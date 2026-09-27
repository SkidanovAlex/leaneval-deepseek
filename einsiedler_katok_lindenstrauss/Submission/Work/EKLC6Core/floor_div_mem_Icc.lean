import Mathlib

namespace Work.EKLC6Core

/-- If `N ≥ 2/η + 1` and `|a| ≤ 2` then `⌊a/η⌋` lies in `[-N, N]`; this is the index bound
for the floor grid of the entry-box cover. -/
theorem floor_div_mem_Icc {η : ℝ} (hη : 0 < η) (N : ℕ) (hN : (2 : ℝ) / η + 1 ≤ N)
    {a : ℝ} (ha : |a| ≤ 2) : ⌊a / η⌋ ∈ Finset.Icc (-(N : ℤ)) N := by
  rw [Finset.mem_Icc]
  -- `2/η + 1 ≤ N` gives `2/η < N`, hence `|a/η| < N` since `|a| ≤ 2`.
  have hN' : (2 : ℝ) / η < (N : ℝ) := by
    have h1 : (2 : ℝ) / η ≤ (N : ℝ) - 1 := by linarith
    linarith
  have habs : |a / η| ≤ 2 / η := by
    rw [abs_div, abs_of_pos hη]
    exact div_le_div_of_nonneg_right ha (le_of_lt hη)
  have hlt : |a / η| < (N : ℝ) := lt_of_le_of_lt habs hN'
  obtain ⟨hlow, hup⟩ := abs_lt.mp hlt
  constructor
  · rw [Int.le_floor]
    push_cast
    linarith
  · have h : ⌊a / η⌋ < (N : ℤ) := Int.floor_lt.mpr (by push_cast; exact hup)
    omega

end Work.EKLC6Core
