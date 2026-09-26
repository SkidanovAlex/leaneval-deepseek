import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.Basic
import Submission.Work.Smooth.SphereJordan.mobiusAddInv
import Submission.Work.Smooth.SphereJordan.Transport
import Submission.Work.Smooth.SphereJordan.exists_planeCurve_of_avoids_infty
import Submission.Work.Smooth.SphereJordan.planeTwoDiscs
import Submission.Work.Smooth.SphereJordan.interior_range_empty_of_injOn_Icc
import Submission.Work.Smooth.SphereJordan.interior_range_empty_of_isSimpleClosedCurve
import Submission.Work.Smooth.SphereJordan.exists_notMem_iUnion_range
import Submission.Work.Smooth.SphereJordan.familyDataOfTwoDiscs
import Submission.Work.Smooth.SphereJordan.RiemannSphere
import Submission.Work.Smooth.SphereJordan.RoundSphere
import Submission.Work.Smooth.SphereJordan.Pullback
import Submission.Work.Smooth.SphereJordan.pullbackSphereCurve_pairwiseDisjoint
import Submission.Work.Smooth.SphereJordan.innerDiscSection
import Submission.Work.Smooth.SphereJordan.innerDiscSection2
import Submission.Work.Smooth.SphereJordan.innermostCurveExists2
import Submission.Work.Smooth.SphereJordan.Clean
import Submission.Work.Smooth.SphereJordan.BoundedSide
import Submission.Work.Smooth.SphereJordan.Pasting
import Submission.Work.Smooth.SphereJordan.Twist
import Submission.Work.Smooth.SphereJordan.injOn_circlePoint
import Submission.Work.Smooth.SphereJordan.injOn_arcPoint
import Submission.Work.Smooth.SphereJordan.continuous_piecewise_disc
import Submission.Work.Smooth.SphereJordan.exists_ball_avoiding
import Submission.Work.Smooth.SphereJordan.exists_ball_avoiding_homeomorph
import Submission.Work.Smooth.SphereJordan.lift_of_range_subset
import Submission.Work.Smooth.SphereJordan.PastingDerive
import Submission.Work.Smooth.SphereJordan.PastingAssembly
import Submission.Work.Smooth.SphereJordan.annulusSchoenflies_of_plain
import Submission.Work.Smooth.SphereJordan.not_naiveSurfaceDiscPushOff_standard
import Submission.Work.Smooth.SphereJordan.plainAnnulus_of_planeHypothesis
import Submission.Work.Smooth.SphereJordan.FinalField

/-!
# `Work.Smooth.SphereJordan` — the sphere-side and surface-side classical inputs of Pardon's theorem

Import this module for everything.  The headline results are

* `Work.Smooth.SphereJordan.jordanSchoenfliesSphere` :
  `Work.Topology.Classical.JordanSchoenfliesSphere` (Jordan–Schoenflies on the round sphere with the
  standard position of finitely many pairwise disjoint Jordan curves), from the **planar**
  Jordan–Schoenflies theorem `Work.Smooth.SphereJordan.PlaneHypothesis`;
* `Work.Smooth.SphereJordan.innermostCurveExists` :
  `Work.Topology.Classical.InnermostCurveExists P` (Pardon's "innermost in the surface" step), from
  the planar theorem;
* `Work.Smooth.SphereJordan.cutsAlongSubdisc_of_props_and_pinched` :
  `Work.Topology.Classical.CutsAlongSubdisc P` for **every** parametrised torus — Pardon's
  cut-and-paste — from the planar theorem together with the named inputs
  `Work.Smooth.SphereJordan.AnnulusSchoenflies` (the annulus form of Schoenflies, carrying the
  orientation sign `s ∈ {1, -1}` of the embedded disc — see §5/§6 of the README; the cut-and-paste
  absorbs the sign by composing with the disc twist of `Work.Smooth.SphereJordan.Twist`),
  `Work.Smooth.SphereJordan.SurfaceDiscPushOff` (the push-off of a surface disc; the eliminated
  curve is inessential in the surface and the disc it spans meets the surface in its interior only
  along it — both hypotheses are needed, see `NaiveSurfaceDiscPushOff` and the README §8.2) and `Work.Smooth.SphereJordan.PinchedPushThrough` (Pardon's
  surgery in the "pinched" configuration, resting on Alexander's theorem and isotopy extension).
  Along the way the *constructive* route `Work.Smooth.SphereJordan.cutsAlongSubdisc_of_props` proves
  the same statement from `AnnulusSchoenflies`, `SurfaceDiscPushOff` and the position hypothesis
  `Work.Smooth.SphereJordan.CurvesInterior` by the collar-discard/push-off/glue construction;
* `Work.Smooth.SphereJordan.cleansDiscsAll_of_props_and_pinched` (and
  `Work.Smooth.SphereJordan.cleansDiscsAll_of_props` via the constructive route) :
  `Work.InnermostDisk.CleansDiscs (ParamTorus.mapHomeomorph ψ)` for every `Submission.Diffeo` `ψ`
  — the `cleans` field of `Work.BoxShrink.FinalInput` — from the planar theorem and those inputs
  (via `Work.Smooth.SphereJordan.cleansDiscs_mapHomeomorph_of_props`,
  `Work.Smooth.SphereJordan.classicalTopology_of_props`).

* `Work.BoxShrink.CleansDiscsAll` — the field `cleans` of `Work.BoxShrink.FinalInput` — from the
  planar theorem, the two classical inputs and the pinched surgery, all at the **standard torus of
  revolution** only (`Work.Smooth.SphereJordan.cleansDiscsAll_field_of_standard_props`,
  `..._and_pinched`, module `FinalField`), and the versions that carry the tameness of the slice
  discs per disc (`Work.Smooth.SphereJordan.cleansDiscsAll_field_of_plane`,
  `..._of_plane_and_pinched`, module `FinalField`).

The **planar annulus theorem** — the only 2-dimensional input of the cut-and-paste — is *proved*
here from the planar Jordan–Schoenflies theorem:

* `Work.Smooth.SphereJordan.plainAnnulus_of_planeHypothesis : PlaneHypothesis → PlainAnnulusSchoenflies`
  (module `plainAnnulus_of_planeHypothesis`, the two-cuts construction, whose geometric core
  `Work.SphereJordan.annulusInjectionCore` lives in the sibling directory
  `Submission/Work/SphereJordan/`);
* `Work.Smooth.SphereJordan.annulusSchoenflies_of_plain : PlainAnnulusSchoenflies → AnnulusSchoenflies`
  (the parametrised form used inside the construction; module `annulusSchoenflies_of_plain`);
* `Work.Smooth.SphereJordan.annulus_of_planeHypothesis` (module of the same name) and
  `Work.Smooth.SphereJordan.annulusTheoremOfPlaneHypothesis` — the theorem in the
  closure/strict-clause form;

so the only remaining named inputs of the chapter are the three 3-dimensional/position statements
`SurfaceDiscPushOff standard`, `PinchedPushThrough standard` (or `CurvesInterior standard`) and the
per-disc tameness `LocallyFlat D.e` (see README §8 and §10).

`lake build Submission.Work.Smooth.SphereJordan.All` succeeds and the whole import closure of this
module is free of unproved holes and of `axiom`; `#print axioms` reports only `propext`, `Classical.choice`
and `Quot.sound` on every headline result.

See `Submission/Work/Smooth/SphereJordan/README.md` for the full account (§10 records the delivery
status of the directory, the archived scaffolding and the co-development with the sibling directory
`Submission/Work/SphereJordan/`).
-/
