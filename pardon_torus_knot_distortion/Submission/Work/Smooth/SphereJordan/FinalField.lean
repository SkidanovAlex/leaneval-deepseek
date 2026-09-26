import Submission.Work.Smooth.SphereJordan.PastingAssembly
import Submission.Work.Smooth.SphereJordan.plainAnnulus_of_planeHypothesis
import Submission.Work.BoxShrink.crux

/-!
# The `cleans` field of `Work.BoxShrink.FinalInput`

This small module names the conclusion of the chapter in the vocabulary of the workspace: the field
`cleans : Work.BoxShrink.CleansDiscsAll` of `Work.BoxShrink.FinalInput`, which is
`∀ ψ : Submission.Diffeo, Work.InnermostDisk.CleansDiscs (ParamTorus.mapHomeomorph ψ.toHomeomorph)`.

The reduction of that field to the classical inputs is `Work.BoxShrink.CleansDiscsAll`:

* `Work.Smooth.SphereJordan.PlainAnnulusSchoenflies` — the planar annulus theorem, in its plain
  set-level form (the parametrised form `Work.Smooth.SphereJordan.AnnulusSchoenflies` used inside
  the construction is *derived* from it by
  `Work.Smooth.SphereJordan.annulusSchoenflies_of_plain`);
* `Work.Smooth.SphereJordan.SurfaceDiscPushOff Work.CoreTopology.standard` — the push-off of a
  surface disc at the standard torus of revolution;
* either the position hypothesis `Work.Smooth.SphereJordan.CurvesInterior Work.CoreTopology.standard`
  (the constructive route) or Pardon's pinched surgery
  `Work.Smooth.SphereJordan.PinchedPushThrough Work.CoreTopology.standard` (Alexander's theorem and
  isotopy extension; no position hypothesis);

together with the *planar* Jordan–Schoenflies theorem `Work.Smooth.SphereJordan.PlaneHypothesis` for
the sphere side (items 1 and 2 of this chapter, which are **proved**: see
`Work.Smooth.SphereJordan.jordanSchoenfliesSphere`, `Work.Smooth.SphereJordan.innermostCurveExists`).

The named inputs are needed *at the standard torus only*: `Work.Topology.Classical.CutsAlongSubdisc
standard` is what the delivered reduction consumes, and everything is transported along the ambient
homeomorphism.

Nothing outside `Submission/Work/Smooth/SphereJordan/` is modified.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.SphereJordan

noncomputable section

/-- **The `cleans` field of `Work.BoxShrink.FinalInput`** — Pardon's cut-and-paste step for the
surfaces of the challenge — from the planar Jordan–Schoenflies theorem, the planar annulus theorem,
the push-off of a surface disc at the standard torus, and the position hypothesis on the slice
discs, all at the standard torus of revolution. -/
theorem cleansDiscsAll_field_of_standard_props (hA : AnnulusSchoenflies)
    (hB : SurfaceDiscPushOff Work.CoreTopology.standard)
    (hC : CurvesInterior Work.CoreTopology.standard)
    (hTame : ∀ D : Work.Topology.SphereSlicing.SliceDisc Work.CoreTopology.standard,
      LocallyFlat D.e)
    (h : PlaneHypothesis) :
    Work.BoxShrink.CleansDiscsAll :=
  cleansDiscsAll_of_standard_props hA hB hC hTame h

/-- **The `cleans` field of `Work.BoxShrink.FinalInput`** from the planar Jordan–Schoenflies theorem,
the planar annulus theorem, the push-off of a surface disc, and Pardon's surgery in the pinched
configuration — with no position hypothesis on the slice discs. -/
theorem cleansDiscsAll_field_of_standard_props_and_pinched (hA : AnnulusSchoenflies)
    (hB : SurfaceDiscPushOff Work.CoreTopology.standard)
    (hP : PinchedPushThrough Work.CoreTopology.standard)
    (hTame : ∀ D : Work.Topology.SphereSlicing.SliceDisc Work.CoreTopology.standard,
      LocallyFlat D.e)
    (h : PlaneHypothesis) :
    Work.BoxShrink.CleansDiscsAll :=
  cleansDiscsAll_of_standard_props_and_pinched hA hB hP hTame h

/-- **The `cleans` field of `Work.BoxShrink.FinalInput`** from the planar Jordan–Schoenflies
theorem, the **plain** annulus form of Schoenflies (`PlainAnnulusSchoenflies`, the honest classical
2-dimensional input), the push-off of a surface disc at the standard torus, and the position
hypothesis on the slice discs. -/
theorem cleansDiscsAll_field_of_standard_plain (hA : PlainAnnulusSchoenflies)
    (hB : SurfaceDiscPushOff Work.CoreTopology.standard)
    (hC : CurvesInterior Work.CoreTopology.standard)
    (hTame : ∀ D : Work.Topology.SphereSlicing.SliceDisc Work.CoreTopology.standard,
      LocallyFlat D.e)
    (h : PlaneHypothesis) :
    Work.BoxShrink.CleansDiscsAll :=
  cleansDiscsAll_of_standard_plain hA hB hC hTame h

/-- **The `cleans` field of `Work.BoxShrink.FinalInput`** from the planar Jordan–Schoenflies
theorem, the **plain** annulus form of Schoenflies, the push-off of a surface disc at the standard
torus, and Pardon's surgery in the pinched configuration — with no position hypothesis. -/
theorem cleansDiscsAll_field_of_standard_plain_and_pinched (hA : PlainAnnulusSchoenflies)
    (hB : SurfaceDiscPushOff Work.CoreTopology.standard)
    (hP : PinchedPushThrough Work.CoreTopology.standard)
    (hTame : ∀ D : Work.Topology.SphereSlicing.SliceDisc Work.CoreTopology.standard,
      LocallyFlat D.e)
    (h : PlaneHypothesis) :
    Work.BoxShrink.CleansDiscsAll :=
  cleansDiscsAll_of_standard_plain_and_pinched hA hB hP hTame h

/-- **The `cleans` field of `Work.BoxShrink.FinalInput`** from the *planar* Jordan–Schoenflies
theorem alone (which now also supplies the planar annulus theorem,
`Work.Smooth.SphereJordan.plainAnnulus_of_planeHypothesis`), the push-off of a surface disc, the
local flatness of the slice discs, and the position hypothesis. -/
theorem cleansDiscsAll_field_of_plane (h : PlaneHypothesis)
    (hB : SurfaceDiscPushOff Work.CoreTopology.standard)
    (hC : CurvesInterior Work.CoreTopology.standard)
    (hTame : ∀ D : Work.Topology.SphereSlicing.SliceDisc Work.CoreTopology.standard,
      LocallyFlat D.e) :
    Work.BoxShrink.CleansDiscsAll :=
  cleansDiscsAll_of_standard_plain (plainAnnulus_of_planeHypothesis h) hB hC hTame h

/-- **The `cleans` field of `Work.BoxShrink.FinalInput`** from the *planar* Jordan–Schoenflies
theorem (hence the planar annulus theorem), the push-off of a surface disc, the local flatness of
the slice discs, and Pardon's surgery in the pinched configuration. -/
theorem cleansDiscsAll_field_of_plane_and_pinched (h : PlaneHypothesis)
    (hB : SurfaceDiscPushOff Work.CoreTopology.standard)
    (hP : PinchedPushThrough Work.CoreTopology.standard)
    (hTame : ∀ D : Work.Topology.SphereSlicing.SliceDisc Work.CoreTopology.standard,
      LocallyFlat D.e) :
    Work.BoxShrink.CleansDiscsAll :=
  cleansDiscsAll_of_standard_plain_and_pinched (plainAnnulus_of_planeHypothesis h) hB hP hTame h

end

end Work.Smooth.SphereJordan
