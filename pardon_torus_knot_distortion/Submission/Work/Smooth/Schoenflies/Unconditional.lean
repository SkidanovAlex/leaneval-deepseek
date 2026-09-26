import Submission.Work.Smooth.Schoenflies.Main
import Submission.Work.Smooth.Schoenflies.caratheodory_extension_continuous

/-!
# The unconditional planar Jordan–Schoenflies theorem

This file supplies the one input of `Work.Smooth.Schoenflies.Main`
(`CaratheodoryExtensionInput`) with the proof of Carathéodory's extension theorem in
`caratheodory_extension_continuous.lean`, and records the resulting **unconditional** statements:

* `caratheodoryExtensionInput : CaratheodoryExtensionInput`;
* `planeHypothesis : Work.Smooth.SphereJordan.PlaneHypothesis`;
* `classicalInput : Work.Smooth.Jordan.ClassicalInput` — the planar Jordan–Schoenflies theorem in
  the shape consumed by the Pardon project (`cleans`, `cleansInDisc`);
* `schoenfliesInput`, `nonempty_planeSchoenflies` — the `C¹` forms;
* `jordanSchoenflies_of_smoothSimpleCurve` — the `SmoothPlaneCurve` form of the sibling chapter
  `Work.Smooth.JordanSeparation`.
-/

open Set Metric
open scoped Topology

namespace Work.Smooth.Schoenflies

noncomputable section

/-- **Carathéodory's extension theorem**, in the shape of the chapter's input. -/
theorem caratheodoryExtensionInput : CaratheodoryExtensionInput :=
  fun {Ω} hΩo hΩne hΩb hΩsc {γ} hγc hγp hγi hfr {f} hf hfinj hfsurj =>
    caratheodory_extension_continuous (Ω := Ω) hΩo hΩne hΩb hΩsc (γ := γ) hγc hγp hγi hfr
      (g := f) hf hfinj hfsurj

/-- **The planar Jordan–Schoenflies theorem**, unconditional:
`Work.Smooth.SphereJordan.PlaneHypothesis`. -/
theorem planeHypothesis : Work.Smooth.SphereJordan.PlaneHypothesis :=
  planeHypothesis_of_caratheodoryExtension caratheodoryExtensionInput

/-- **The classical input of the plane theory**, unconditional:
`Work.Smooth.Jordan.ClassicalInput` (equivalently `PlaneHypothesis`).  This is the theorem the
Pardon project consumes: every simple closed plane curve bounds an embedded disc whose image is the
closure of its bounded side. -/
theorem classicalInput : Work.Smooth.Jordan.ClassicalInput :=
  classicalInput_of_caratheodoryExtension caratheodoryExtensionInput

/-- `Work.Smooth.Jordan.SchoenfliesInput c` for every `C¹` simple closed plane curve. -/
theorem schoenfliesInput (c : Work.Smooth.Jordan.PlaneCurve) (hdiff : ContDiff ℝ 1 c.γ) :
    Work.Smooth.Jordan.SchoenfliesInput c :=
  schoenfliesInput_of_caratheodoryExtension caratheodoryExtensionInput c hdiff

/-- Every `C¹` simple closed plane curve spans an embedded disc (the Jordan–Schoenflies theorem). -/
theorem nonempty_planeSchoenflies (c : Work.Smooth.Jordan.PlaneCurve)
    (hdiff : ContDiff ℝ 1 c.γ) (hs : c.IsSimple) :
    Nonempty (Work.Smooth.Jordan.PlaneSchoenflies c) :=
  nonempty_planeSchoenflies_of_caratheodoryExtension caratheodoryExtensionInput c hdiff hs

/-- The `SmoothPlaneCurve` form of the same theorem, as used by the JordanSeparation chapter. -/
theorem nonempty_planeSchoenflies_of_smooth (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    (hs : c.toPlaneCurve.IsSimple) : Nonempty (Work.Smooth.Jordan.PlaneSchoenflies c.toPlaneCurve) :=
  nonempty_planeSchoenflies c.toPlaneCurve c.contDiff hs

end

end Work.Smooth.Schoenflies
