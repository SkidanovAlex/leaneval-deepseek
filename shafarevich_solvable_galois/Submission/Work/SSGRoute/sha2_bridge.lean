import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.AbsoluteKummer.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A helper for the `SSGRoute` cochain vocabulary

The four bridges between the `SSGRoute` predicates (`IsCocycle2`, `IsLocConst2`, `IsLocConstOn`,
`IsCoboundary2On`) and the continuous-cohomology groups `Work.AbsoluteKummer.Z2`/`B2` are proved
in the dedicated modules

* `Submission.Work.SSGRoute.bridge_isCocycle2_mem_Z2`,
* `Submission.Work.SSGRoute.bridge_isLocConst2_isLocallyConstant`,
* `Submission.Work.SSGRoute.bridge_isLocConstOn_top_of_isLocallyConstant`,
* `Submission.Work.SSGRoute.bridge_mem_B2_isCoboundary2On`

(the original statements collected here omitted the `IsTopologicalGroup`/`CompactSpace`
hypotheses and were false).  What remains here is the elementary compatibility of
`Work.AbsoluteKummer.IsLocallyConstant` with composition by a continuous map.
-/

namespace Work.SSGRoute

/-- Local constancy (in the `Work.AbsoluteKummer` sense) is preserved by composition with a
continuous map. -/
theorem isLocallyConstant_comp_continuous {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Y → Z} (hf : Work.AbsoluteKummer.IsLocallyConstant f) {φ : X → Y}
    (hφ : Continuous φ) : Work.AbsoluteKummer.IsLocallyConstant (f ∘ φ) := by
  intro x
  obtain ⟨V, hV, hxV, hVc⟩ := hf (φ x)
  exact ⟨φ ⁻¹' V, hV.preimage hφ, hxV, fun y hy => hVc (φ y) hy⟩

end Work.SSGRoute
