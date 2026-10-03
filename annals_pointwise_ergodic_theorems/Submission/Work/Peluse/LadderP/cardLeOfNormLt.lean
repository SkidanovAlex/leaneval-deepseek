import Mathlib

namespace Work.Peluse.LadderP

/-- A finite set of integers all lying in the open interval `(-r, r)` has at most `2r + 3` elements. -/
theorem cardLeOfNormLt {r : ℝ} (hr : 0 < r) (s : Finset ℤ) (h : ∀ x ∈ s, |(x : ℝ)| < r) :
    (s.card : ℝ) ≤ 2 * r + 3 := by
  -- Every element of `s` lies between `-⌊r⌋` and `⌊r⌋`.
  set a : ℤ := ⌊r⌋ with ha
  have ha0 : 0 ≤ a := by rw [ha]; exact Int.floor_nonneg.mpr (le_of_lt hr)
  have hsub : s ⊆ Finset.Icc (-a) a := by
    intro x hx
    rw [Finset.mem_Icc]
    obtain ⟨h1, h2⟩ := (abs_lt.mp (h x hx))
    constructor
    · have : (-x : ℤ) ≤ a := by
        rw [ha]
        exact Int.le_floor.mpr (by push_cast; linarith)
      omega
    · rw [ha]
      exact Int.le_floor.mpr (by linarith)
  have hcard : s.card ≤ (Finset.Icc (-a) a).card := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  -- The interval `[-a, a]` has `2a + 1` elements.
  have hnat : s.card ≤ (2*a+1).toNat := by
    have hh : a + 1 - -a = 2*a+1 := by ring
    rwa [hh] at hcard
  have h2a : (0:ℤ) ≤ 2*a+1 := by omega
  have hcast : (((2*a+1).toNat : ℕ) : ℝ) = 2*(a:ℝ)+1 := by
    have h1 : ((2*a+1).toNat : ℤ) = 2*a+1 := Int.toNat_of_nonneg h2a
    rw [← Int.cast_natCast]
    rw [h1]
    push_cast
    ring
  calc (s.card : ℝ) ≤ (((2*a+1).toNat : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = 2*(a:ℝ)+1 := hcast
    _ ≤ 2*r+3 := by
        have : (a:ℝ) ≤ r := by rw [ha]; exact Int.floor_le r
        linarith

end Work.Peluse.LadderP
