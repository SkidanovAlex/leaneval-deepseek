import Mathlib
import Submission.Work.PTGeometric.WeakRegion.Manifold

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The defining function is negative away from the region's boundary

For a weak region setup `S : RegionSetupWeak k` and an interior point `x` of the region
`S.Region = {y | S.Φ y ≤ 0}`, the defining function is *strictly* negative: `S.Φ x.1 < 0`.

Immediate from the boundary characterisation `S.mem_boundary_iff`
(`x ∈ ∂S.Region ↔ x.1 ∈ ∂S.A ∨ S.Φ x.1 = 0`) and `x.2 : S.Φ x.1 ≤ 0`.

This is the input of **G4** of `LeadChapter/ASSEMBLY.md`: at a collar point of the level set the region
chart is the ambient identity (`Work.ThomBordism.sourceRegionMk_extChartAt_apply_of_phi_neg`, whose
hypothesis is exactly `S.Φ m.1 < 0`).

No `sorry`, no new axioms.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Manifold

namespace Work.PTGeometric.WeakRegion

noncomputable section

variable {k : ℕ}

/-- **The defining function is strictly negative at the region's interior points.** -/
theorem RegionSetupWeak.phi_neg_of_not_mem_boundary (S : RegionSetupWeak k) (x : S.Region)
    (hx : x ∉ (𝓡∂ (8 + k + 1)).boundary S.Region) : S.Φ x.1 < 0 := by
  refine lt_of_le_of_ne x.2 (fun hzero => hx ?_)
  exact (S.mem_boundary_iff x).mpr (Or.inr hzero)

end

#print axioms RegionSetupWeak.phi_neg_of_not_mem_boundary

end Work.PTGeometric.WeakRegion
