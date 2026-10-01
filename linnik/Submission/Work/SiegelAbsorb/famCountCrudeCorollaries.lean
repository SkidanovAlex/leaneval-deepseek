import Mathlib
import Submission.Work.SiegelAbsorb.famCount_crude

/-!
# U3 (corollaries of `AREA6_ROUTE_LEAD.md`): the crude `LogFreeFamHeight`/`LogFreeFamHalf` at `9/2`

`SiegelAbsorb.famCount_crude` (U3) already has the exact shape of the two `LogFreeFam` statements
at `c₃ = 9/2`, `c₃' = 3/2`; this file records them.
-/

namespace Work.SiegelAbsorb

noncomputable section

/-- The crude log-free family count in the height direction: `LogFreeFamHeight (9/2) (3/2)`. -/
theorem logFreeFamHeight_crude : Work.ZeroDensity.LogFreeFamHeight (9 / 2) (3 / 2) := by
  obtain ⟨C, hC, h⟩ := famCount_crude
  exact ⟨C, hC, 2, fun q hq _ σ T hσ0 hσ1 hT => h q hq σ T hσ0 hσ1 hT⟩

/-- The crude log-free family count at height `1`: `LogFreeFamHalf (9/2)`. -/
theorem logFreeFamHalf_crude : Work.ZeroDensity.LogFreeFamHalf (9 / 2) := by
  obtain ⟨C, hC, h⟩ := famCount_crude
  refine ⟨C, hC, 2, ?_⟩
  intro q hq hqne σ hσ0 hσ1
  haveI := hqne
  have hb := h q hq σ 1 hσ0 hσ1 le_rfl
  rw [Real.one_rpow, mul_one] at hb
  exact hb

end

end Work.SiegelAbsorb
