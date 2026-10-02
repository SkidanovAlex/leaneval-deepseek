import Mathlib
import Submission.Work.Cohomology.cohomologyPairVk
import Submission.Work.Cohomology.Crux.vkOvlDefs
import Submission.Work.Milnor.Collar
import Submission.Work.Milnor.VBundle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The set `(U ∩ V) ∪ collar` and the two chart models

The endgame target `Work.Cohomology.Endgame.ovlUnionCollar_vanishing` concerns the relative
cohomology of the pair `(Vk(-2), W)` where `W = (U ∩ V) ∪ collar(-2)` is the union of the overlap of
the two chart images of the disc bundle `Vk(-2)` and the collar `{1/2 < ν}`.

This file collects the definitions that the target and the lemmas about it share:

* `Work.Cohomology.Endgame.ovlW` — the set `W`;
* `Work.Cohomology.Endgame.ovlWU`, `ovlWV` — its traces on the two charts;
* `Work.Cohomology.Endgame.chartX` — the homeomorphism `ℝ⁴ × ℍ ≅ U` of the first chart;
* `Work.Cohomology.Endgame.ovlDiscX` — the closed disc `{0} × B̄(1/2) ⊆ ℝ⁴ × ℍ` whose complement
  in the chart is the trace of `W` on the first chart.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology.Endgame

noncomputable section

/-- **The set `W = (U ∩ V) ∪ collar(-2)`** of the target theorem. -/
abbrev ovlW : Set Work.Cohomology.vkPairX :=
  Work.Cohomology.Crux.vkU ∩ Work.Cohomology.Crux.vkV ∪ Work.Milnor.collar (-2)

/-- The trace of `W` on the first chart of `Vk(-2)`. -/
abbrev ovlWU : Set ↥(Work.Cohomology.Crux.vkU) :=
  (Subtype.val : ↥(Work.Cohomology.Crux.vkU) → Work.Cohomology.vkPairX) ⁻¹' ovlW

/-- The trace of `W` on the second chart of `Vk(-2)`. -/
abbrev ovlWV : Set ↥(Work.Cohomology.Crux.vkV) :=
  (Subtype.val : ↥(Work.Cohomology.Crux.vkV) → Work.Cohomology.vkPairX) ⁻¹' ovlW

/-- The chart homeomorphism `ℝ⁴ × ℍ ≅ U` of the first chart of `Vk(-2)`. -/
def chartX : Submission.Milnor.MSpace8 ≃ₜ ↥(Work.Cohomology.Crux.vkU) :=
  (Submission.Milnor.vData (-2)).isOpenEmbedding_ιX.isEmbedding.toHomeomorph

/-- The chart homeomorphism `ℝ⁴ × ℍ ≅ V` of the second chart of `Vk(-2)`. -/
def chartY : Submission.Milnor.MSpace8 ≃ₜ ↥(Work.Cohomology.Crux.vkV) :=
  (Submission.Milnor.vData (-2)).isOpenEmbedding_ιY.isEmbedding.toHomeomorph

/-- The closed disc `{0} × B̄(1/2) ⊆ ℝ⁴ × ℍ` at the origin of the first chart. -/
def ovlDisc : Set Submission.Milnor.MSpace8 :=
  {p | p.1 = 0 ∧ ‖p.2‖ ≤ 1/2}

end

end Work.Cohomology.Endgame
