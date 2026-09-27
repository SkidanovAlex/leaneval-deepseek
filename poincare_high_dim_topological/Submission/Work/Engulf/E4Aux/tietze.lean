import Mathlib
import Submission.Work.PL.Defs

namespace Work.Engulf.E4Aux

/-- A continuous map from a closed subset of `ℝᴺ` into `ℝⁿ` extends to a continuous map on all of
`ℝᴺ` (Tietze). -/
theorem tietze {N n : ℕ} {C : Set (PL.E N)} (hC : IsClosed C) {g : PL.E N → PL.E n}
    (hg : ContinuousOn g C) : ∃ G : PL.E N → PL.E n, Continuous G ∧ Set.EqOn G g C := by
  obtain ⟨F, hF⟩ :=
    ContinuousMap.exists_restrict_eq (Y := PL.E n) hC ⟨C.domRestrict g, hg.domRestrict⟩
  refine ⟨F, F.continuous, fun x hx => ?_⟩
  have := congrFun (congrArg DFunLike.coe hF) ⟨x, hx⟩
  simpa using this

end Work.Engulf.E4Aux
