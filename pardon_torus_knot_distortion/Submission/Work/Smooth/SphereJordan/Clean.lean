import Submission.Work.Smooth.SphereJordan.RoundSphere
import Submission.Work.Smooth.SphereJordan.innermostCurveExists2

/-!
# The cut-and-paste (Pardon's second innermost argument) from its two ingredients

This file records the *reduction* of `Work.InnermostDisk.CleansDiscs` — the `cleans` field of the
sibling deliverable `Work.BoxShrink.FinalInput` — to the two ingredients of Pardon's argument, one
of which (`Work.Topology.Classical.InnermostCurveExists`) is **proved** in this chapter from the
planar Jordan–Schoenflies theorem:

* `Work.Topology.Classical.InnermostCurveExists P` (*innermost in the surface*): among the finitely
  many pairwise disjoint inessential intersection curves in an embedded disc one bounds a sub-disc
  whose interior misses `F` and which no other curve meets.  This is
  `Work.Smooth.SphereJordan.innermostCurveExists`, proved from `PlaneHypothesis` by pulling the
  curves back to the model disc, applying the planar two-disc theorem
  (`Work.Smooth.SphereJordan.planeTwoDiscs`) to each and reading off the nesting rank
  (`Work.Smooth.SphereJordan.familyDataOfTwoDiscs`).
* `Work.Topology.Classical.CutsAlongSubdisc P` (*the surgery*): given such an innermost sub-disc,
  eliminate exactly that intersection curve.  Classically this is Alexander's theorem (the union of
  the sub-disc and the disc of `F` it bounds is an embedded `2`-sphere, hence bounds a ball) together
  with isotopy extension.  It is **not** proved here: it is the one named hypothesis which remains,
  and it is stated in the delivered chapter with the exact hypotheses on which Pardon's argument
  consumes it.

The composition below is the whole of the reduction: it is the delivered
`pushThroughInnermost_of_innermostCurveExists_of_cutsAlongSubdisc` followed by the delivered
passage `PushThroughInnermost → CleanOneCurve → CleansDiscs` of Pardon's "proceeding in this way, we
may eliminate all the intersections".
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.SphereJordan

noncomputable section

/-- **Pardon's first innermost step ("innermost in the surface")**, in the form consumed by the
delivered chapter: every `SliceDisc` with at least one intersection curve has a curve bounding a
sub-disc whose interior misses the surface and which no other curve meets.  This is
`Work.Smooth.SphereJordan.innermostCurveExists2`, proved from the planar Jordan–Schoenflies theorem
by pulling the curves back to the model disc. -/
theorem innermostCurveExists (h : PlaneHypothesis) (P : Work.CoreTopology.ParamTorus) :
    Work.Topology.Classical.InnermostCurveExists P :=
  innermostCurveExists2 h P

/-- **Pardon's cut-and-paste from its two ingredients**, for an arbitrary parametrised torus. -/
theorem cleansDiscs_of_innermostCurveExists_of_cutsAlongSubdisc {P : Work.CoreTopology.ParamTorus}
    (h₂ : Work.Topology.Classical.InnermostCurveExists P)
    (h₃ : Work.Topology.Classical.CutsAlongSubdisc P) :
    Work.InnermostDisk.CleansDiscs P :=
  Work.Topology.SphereSlicing.cleansDiscs_of_cleanOneCurve
    (Work.Topology.Classical.cleanOneCurve_of_pushThroughInnermost
      (Work.Topology.Classical.pushThroughInnermost_of_innermostCurveExists_of_cutsAlongSubdisc
        h₂ h₃))

/-- **Pardon's cut-and-paste from the planar theorem and the gluing step**, for an arbitrary
parametrised torus: this is `CleansDiscs`, the `cleans` field of `Work.BoxShrink.FinalInput`. -/
theorem cleansDiscs_of_plane_of_cutsAlongSubdisc (h : PlaneHypothesis)
    {P : Work.CoreTopology.ParamTorus} (h₃ : Work.Topology.Classical.CutsAlongSubdisc P) :
    Work.InnermostDisk.CleansDiscs P :=
  cleansDiscs_of_innermostCurveExists_of_cutsAlongSubdisc (innermostCurveExists h P) h₃

/-- **The packaged classical input of `Work.Topology.Classical`**, from the planar
Jordan–Schoenflies theorem together with the gluing step at the standard torus of revolution: the
sphere side is now *proved*, and the cut-and-paste is reduced to `CutsAlongSubdisc standard`. -/
theorem classicalTopology_of_plane (h : PlaneHypothesis)
    (h₃ : Work.Topology.Classical.CutsAlongSubdisc Work.CoreTopology.standard) :
    Work.Topology.Classical.ClassicalTopology :=
  Work.Topology.Classical.classicalTopology_of_decomposed (jordanSchoenfliesSphere h)
    (innermostCurveExists h Work.CoreTopology.standard) h₃

/-- **Pardon's cut-and-paste for the tori of the challenge**
(`P = ParamTorus.mapHomeomorph ψ`, in particular `ψ.toHomeomorph` for the smooth ambient
diffeomorphisms `ψ : Submission.Diffeo` of the challenge): the field
`Work.BoxShrink.FinalInput.cleans`, from the planar Jordan–Schoenflies theorem and the gluing step
at the standard torus. -/
theorem cleansDiscs_mapHomeomorph (h : PlaneHypothesis)
    (h₃ : Work.Topology.Classical.CutsAlongSubdisc Work.CoreTopology.standard) (ψ : R3 ≃ₜ R3) :
    Work.InnermostDisk.CleansDiscs (Work.CoreTopology.ParamTorus.mapHomeomorph ψ) :=
  Work.Topology.SphereSlicing.cleansDiscs_of_cleanOneCurve
    (Work.Topology.Classical.cleanOneCurve_mapHomeomorph_of_classicalTopology ψ
      (classicalTopology_of_plane h h₃))

/-- **The `cleans` field of `Work.BoxShrink.FinalInput`** — Pardon's cut-and-paste step for the
surfaces of the challenge, i.e. `Work.BoxShrink.CleansDiscsAll` — from the planar
Jordan–Schoenflies theorem and the gluing hypothesis at the standard torus of revolution. -/
theorem cleansDiscsAll_of_plane_of_cuts (h : PlaneHypothesis)
    (h₃ : Work.Topology.Classical.CutsAlongSubdisc Work.CoreTopology.standard) :
    ∀ ψ : Submission.Diffeo, Work.InnermostDisk.CleansDiscs
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) :=
  fun ψ => cleansDiscs_mapHomeomorph h h₃ ψ.toHomeomorph

/-- The same, for the parametrised tori `ParamTorus.mapHomeomorph ψ` with the gluing hypothesis
stated for that torus directly. -/
theorem cleansDiscs_mapHomeomorph_of_cutsAlongSubdisc (h : PlaneHypothesis) (ψ : R3 ≃ₜ R3)
    (h₃ : Work.Topology.Classical.CutsAlongSubdisc
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ)) :
    Work.InnermostDisk.CleansDiscs (Work.CoreTopology.ParamTorus.mapHomeomorph ψ) :=
  cleansDiscs_of_plane_of_cutsAlongSubdisc h h₃

end

end Work.Smooth.SphereJordan
