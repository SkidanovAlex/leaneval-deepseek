import Mathlib
import Submission.Work.InnermostDisk.Defs
import Submission.Work.CoreTopology.Winding
import Submission.Work.CoreTopology.standardCurve_one_one_simple
import Submission.Work.Drive.EpsForm.DatumCore
import Submission.Work.Drive.EpsForm.work_datumCore

namespace Work.Drive.EpsForm

open LeanEval.KnotTheory.PardonDistortion
open Set

/-- **The missing innermost-disc datum on the standard torus**, in the sharpest form:
a datum whose boundary curve is the standard `(1,1)`-curve.

`Submission/Work/Drive/EpsForm/NOTES_datum_ANALYSIS_session.md` (same directory) records the
analysis: clean datums are excluded by the *proved* `Work.CoreTopology.compressing_winding_dichotomy`
(a spanning disc with interior off the carrier is impossible for an essential `α`);
`Work.Drive.compressing_winding_dichotomyW` + `Work.Drive.vanishingWindingBoundsWeakDisc` show that
such a datum is *equivalent* to `¬ Work.Drive.CleansDiscsW Work.CoreTopology.standard`; datums whose
traces all stay strictly inside the model disc are excluded by the annulus argument; the surviving
shape is a dirty datum whose traces meet `∂𝔻`, and the configuration satisfying every winding
constraint is described there (`α = standardCurve 1 1`, the trace the Jordan curve
`γ_up = {torusMap(t,-t)}` over `[0,π]` together with
`γ_lo = {torusMap(π,φ)}`, `φ ∈ [-π,0]`, followed by `{torusMap(θ,0)}`, `θ ∈ [0,π]`).

The whole geometric content is isolated in `Work.Drive.EpsForm.DatumCore` (see
`Submission/Work/Drive/EpsForm/DatumCore.lean` and the design note
`NOTES_design_session2.md`): an injective continuous disc `e` spanning `standardCurve 1 1` together
with a single inessential simple closed curve covering `e '' (open 𝔻) ∩ Σ`.  The two facts about the
boundary curve itself (`standardCurve_one_one_simple`, `standardCurve_essential`) are proved, and
given `DatumCore` the datum is assembled below. -/
theorem exists_innermostDisc_standardCurve_of_datumCore (h : DatumCore) :
    ∃ S : Set R3, ∃ D : Work.InnermostDisk.InnermostDisc Work.CoreTopology.standard S,
      D.α = Work.CoreTopology.standardCurve 1 1 := by
  obtain ⟨e, hinj, hbd, κ, hsimp, hiness, hsub, hcov⟩ := h
  refine ⟨Set.univ, ?_⟩
  exact ⟨{ α := Work.CoreTopology.standardCurve 1 1
           simple := Work.CoreTopology.standardCurve_one_one_simple
           essential := Work.CoreTopology.standardCurve_essential 1 1 (by norm_num)
           mem := fun _ => trivial
           e := e
           inj := hinj
           boundary := hbd
           e_mem := fun _ => trivial
           ι := PUnit
           fintype := inferInstance
           curves := fun _ => κ
           curves_simple := fun _ => hsimp
           curves_inessential := fun _ => hiness
           curves_disjoint := fun _ _ h => absurd rfl h
           curves_subset := fun _ => hsub
           covers := fun z hz hc => ⟨PUnit.unit, hcov z hz hc⟩ }, rfl⟩

theorem exists_innermostDisc_standardCurve :
    ∃ S : Set LeanEval.KnotTheory.PardonDistortion.R3,
      ∃ D : Work.InnermostDisk.InnermostDisc Work.CoreTopology.standard S,
        D.α = Work.CoreTopology.standardCurve 1 1 :=
  exists_innermostDisc_standardCurve_of_datumCore work_datumCore

end Work.Drive.EpsForm
