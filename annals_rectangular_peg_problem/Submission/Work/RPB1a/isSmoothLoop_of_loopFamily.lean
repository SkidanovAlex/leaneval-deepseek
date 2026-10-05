import Mathlib
import Submission.Work.RPB1a.Defs

namespace Work.RPB1a

open Work.RPB1a

open scoped ContDiff

/-- Every slice of a loop family in the parameter range is a smooth loop.

This is just a matter of unbundling `IsLoopFamily` (the four fields of `IsSmoothLoop` are the
corresponding fields of `IsLoopFamily`, restricted to `s ∈ [0,1]`), together with the fact that
joint `C^∞` regularity restricts to `C^∞` regularity of each slice. -/
theorem isSmoothLoop_of_loopFamily {c : ℝ → ℝ → ℂ} (hc : IsLoopFamily c) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : IsSmoothLoop (c s) := by
  obtain ⟨hcd, hper, hinj, himm⟩ := hc
  have hslice : ContDiff ℝ ∞ (fun t : ℝ => (s, t)) := by fun_prop
  exact ⟨hcd.comp hslice, hper s, fun t t' h => hinj s hs t t' h, himm s hs⟩

end Work.RPB1a
