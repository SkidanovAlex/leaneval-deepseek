import Mathlib
import Submission.Work.LinnikAreas.PrincipalZeroCount
import Submission.Work.LinnikAreas.tail_le_of_ballCount
import Submission.Work.LinnikAreas.xiC_ballCount_order

namespace Work.LinnikAreas

/-- **The inverse-square tail of the zeros of `Ξ` is bounded.**

There is an absolute constant `C > 0` such that for every finite set `s` of complex numbers of
norm exceeding `2`, the multiplicity-weighted inverse-square sum of the vanishing orders of the
entire completion `Ξ = xiC` of the Riemann zeta function is at most `C`.  The bound rests on the
Jensen-type zero count `Commons.NumberTheory.Zeta.xiE_zeroCount` (a Riemann–von Mangoldt estimate
for `Ξ`) together with a dyadic decomposition of the tail. -/
theorem xiCZeroInvSqTailBound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Finset ℂ, (∀ u ∈ s, 2 < ‖u‖) →
      ∑ u ∈ s, (analyticOrderNatAt Work.LinnikAreas.xiC u : ℝ) / ‖u‖ ^ 2 ≤ C := by
  obtain ⟨c, hcpos, hcount⟩ := xiC_ballCount_order
  obtain ⟨C, hCpos, htail⟩ := tail_le_of_ballCount (le_of_lt hcpos)
  exact ⟨C, hCpos, fun s hs => htail (fun u => (analyticOrderNatAt xiC u : ℝ))
    (fun u => by positivity) hcount s hs⟩

end Work.LinnikAreas
