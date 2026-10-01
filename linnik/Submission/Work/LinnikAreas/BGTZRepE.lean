import Mathlib
import Submission.Work.LinnikAreas.RepulsionCapDefs
import Submission.Work.LinnikAreas.BGTZ.ZFRInput_exists
import Submission.Work.LinnikAreas.BGTZ.ZFRInputL_of_ZFRInput
import Submission.Work.LinnikAreas.BGTZ.UniformConvexity
import Submission.Work.LinnikAreas.BGTZHyp
import Submission.Work.LinnikAreas.BGTZ.SieveWeights
import Submission.Work.LinnikAreas.BGTZ.E.RepulsionFromPiecesE
import Submission.Work.LinnikAreas.BGTZ.E.DetectorE_of_detJ
import Submission.Work.LinnikAreas.BGTZ.E.detJ_le_target

/-!
# The BGTZ Deuring--Heilbronn repulsion at all heights, without the `area6` import chain

This file proves `Work.LinnikAreas.BGTZRepulsionGenE` (`LinnikAreas/RepulsionCapDefs.lean`), the
statement

`∃ cZ > 0, BGTZ.ZFRInputL cZ ∧ BGTZ.RepulsionGenC (11/5) (11/10) (max (1000/cZ) 1000)`,

by the same five-line assembly as `Work.LinnikAreas.BGTZ.E.BGTZRepulsionGen_E`
(`BGTZ/E/BGTZRepulsionGen_E.lean`): the corrected detector `DetectorE_proved`, Graham's Selberg
weights `BGTZ.SieveWeights`, the convexity input `BGTZ.UniformConvexity`, the `ζ`-input
`BGTZ.hypZeta_of_commons` and the unconditional zero-free region `BGTZ.ZFRInputL_of_ZFRInput`.

The *only* difference from the chapter's packaging is that the statement is the local one, so that
the AREA 6 assembly (`LinnikAreas/area6CapChain.lean`) and the frozen target (`LinnikAreas/area6.lean`)
can import it: the chapter's `BGTZRepulsionGen` is defined in `LinnikAreas/area6Chain.lean`, which
imports `area6Final → area6Sound → area6`, so `area6.lean` cannot import it.
-/

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

/-- The uniform zero-free region in the `L`-function form, unconditionally (a copy of
`Work.LinnikAreas.ZFRInputL_exists`, which lives in `area6Chain`). -/
theorem ZFRInputL_existsE : ∃ cZ : ℝ, 0 < cZ ∧ Work.LinnikAreas.BGTZ.ZFRInputL cZ := by
  obtain ⟨cZ, hcZ, hz⟩ := Work.LinnikAreas.BGTZ.ZFRInput_exists
  exact Work.LinnikAreas.BGTZ.ZFRInputL_of_ZFRInput cZ hcZ hz

/-- The corrected BGTZ detector (a copy of `Work.LinnikAreas.BGTZ.E.DetectorE_proved`). -/
theorem DetectorE_provedE : Work.LinnikAreas.BGTZ.DetectorPropE :=
  Work.LinnikAreas.BGTZ.E.DetectorE_of_detJ Work.LinnikAreas.BGTZ.E.detJ_le_target

/-- **The BGTZ repulsion at all heights**, in the statement
`Work.LinnikAreas.BGTZRepulsionGenE`. -/
theorem BGTZRepulsionGenE_proved : Work.LinnikAreas.BGTZRepulsionGenE := by
  obtain ⟨cZ, hcZ, hzfr⟩ := ZFRInputL_existsE
  refine ⟨cZ, hcZ, hzfr, ?_⟩
  exact Work.LinnikAreas.BGTZ.E.RepulsionFromPiecesE cZ hcZ
    Work.LinnikAreas.BGTZ.UniformConvexity
    Work.LinnikAreas.BGTZ.hypZeta_of_commons
    (Work.LinnikAreas.BGTZ.SieveWeights : Work.LinnikAreas.BGTZ.SieveWeightsProp)
    DetectorE_provedE hzfr

end

end Work.LinnikAreas
