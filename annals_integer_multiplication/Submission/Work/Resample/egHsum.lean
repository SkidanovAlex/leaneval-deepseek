import Mathlib
import Submission.Work.Resample.sliceB1defs

namespace Work.Resample

/-- Split the (summable) series `∑' h : ℤ, f h` into the finite window
`egHset m = {h | 0 < |h| ≤ m}` and the complementary tail, written as a single
series with an `if` that kills the window terms. -/
theorem egHsum {f : ℤ → ℂ} (m : ℕ) (hf : Summable f) :
    ∑' h : ℤ, f h = (∑ h ∈ Work.Resample.egHset m, f h)
      + ∑' h : ℤ, (if h ∈ Work.Resample.egHset m then 0 else f h) := by
  have hsub : (∑' h : ↑((↑(Work.Resample.egHset m) : Set ℤ)ᶜ), f h)
      = ∑' h : ℤ, (if h ∈ Work.Resample.egHset m then 0 else f h) := by
    rw [tsum_subtype]
    refine tsum_congr fun h => ?_
    by_cases hh : h ∈ (Work.Resample.egHset m : Set ℤ)
    · rw [Set.indicator_of_notMem (by simpa [Set.mem_compl_iff] using hh) f]
      exact (ite_eq_left hh).symm
    · rw [Set.indicator_of_mem (by simpa [Set.mem_compl_iff] using hh) f]
      exact (ite_eq_right hh).symm
  rw [eq_comm, ← hsub, hf.sum_add_tsum_compl (s := Work.Resample.egHset m)]

end Work.Resample
