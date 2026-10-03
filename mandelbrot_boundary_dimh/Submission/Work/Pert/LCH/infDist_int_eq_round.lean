import Mathlib

namespace Work.Pert.LCH

/-- The distance from a real number to the set of integers is the distance to its nearest
integer, where ties (`x + 1/2 ∈ ℤ`) are rounded towards `+∞`, i.e. `⌊x + 1/2⌋`. -/
theorem infDist_int_eq_round (x : ℝ) :
    Metric.infDist x (Set.range (fun k : ℤ => (k : ℝ))) = |x - ((⌊x + 1 / 2⌋ : ℤ) : ℝ)| := by
  -- `⌊x + 1/2⌋` is Mathlib's `round`, the nearest integer with ties broken towards `+∞`.
  rw [← round_eq x]
  refine le_antisymm ?_ ?_
  · -- the value at the nearest integer is an admissible candidate
    exact Metric.infDist_le_dist_of_mem ⟨round x, rfl⟩
  · -- and no integer does better
    apply (Metric.le_infDist (s := Set.range (fun k : ℤ => (k : ℝ))) ⟨0, by simp⟩).mpr
    intro y hy
    obtain ⟨k, rfl⟩ := hy
    simpa [Real.dist_eq] using round_le x k

end Work.Pert.LCH
