import Mathlib
import Submission.Work.Drive.oFatDefsS
import Submission.Work.Drive.crosscut_or_spreadQuad
import Submission.Work.Drive.shortMidClosure

/-!
# Closedness of the `E3′` obstruction set

`Work.Drive.OFatObstructionS r ρ δs = OFatObstruction r ρ ∪ ShortMid r δs` is closed: the first
part is closed (`Work.Drive.isClosed_OFatObstruction`) and the closure of the second lies in
`ShortMid r δs ∪ TCset r ⊆ OFatObstructionS r ρ δs` (`Work.Drive.shortMidClosure`).
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant Set

/-- **`OFatObstructionS r ρ δs` is closed** (`ρ > 0`, no inflections). -/
theorem isClosed_OFatObstructionS {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {ρ δs : ℝ} (hρ : 0 < ρ) :
    IsClosed (OFatObstructionS r ρ δs) := by
  have hA : closure (OFatObstruction r ρ) ⊆ OFatObstruction r ρ :=
    (isClosed_OFatObstruction hr hinfl hρ).closure_subset
  have hS : closure (ShortMid r δs) ⊆ OFatObstructionS r ρ δs := by
    intro q hq
    rcases shortMidClosure hr hinfl δs hq with h | h
    · exact ShortMid_subset_OFatObstructionS r ρ δs h
    · exact OFatObstruction_subset_OFatObstructionS r ρ δs (Or.inr h)
  have hsub : closure (OFatObstructionS r ρ δs) ⊆ OFatObstructionS r ρ δs := by
    rw [OFatObstructionS, closure_union]
    exact fun q hq => hq.elim (fun h => OFatObstruction_subset_OFatObstructionS r ρ δs (hA h))
      (fun h => hS h)
  rw [← le_antisymm hsub subset_closure]
  exact isClosed_closure

end Work.Drive
