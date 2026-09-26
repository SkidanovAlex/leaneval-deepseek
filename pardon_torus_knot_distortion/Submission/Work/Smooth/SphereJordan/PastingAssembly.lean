import Submission.Work.Smooth.SphereJordan.PastingDerive
import Submission.Work.Smooth.SphereJordan.Clean
import Submission.Work.Smooth.SphereJordan.annulusSchoenflies_of_plain

/-!
# The cut-and-paste, assembled: `CleansDiscs` for the tori of the challenge

This file records the consequences of `Work.Smooth.SphereJordan.cutsAlongSubdisc_of_props`: the
cut-and-paste `Work.Topology.Classical.CutsAlongSubdisc P`, hence Pardon's second innermost
argument `Work.InnermostDisk.CleansDiscs P` (the `cleans` field of `Work.BoxShrink.FinalInput`) and
the packaged classical input `Work.Topology.Classical.ClassicalTopology`, for the tori of the
challenge — from the *planar* Jordan–Schoenflies theorem (`PlaneHypothesis`, proved by the sibling
subproject `Submission/Work/Smooth/JordanSeparation`) together with the named inputs of
`Submission/Work/Smooth/SphereJordan/Pasting.lean`:

* `Work.Smooth.SphereJordan.PlainAnnulusSchoenflies` (the planar annulus theorem; the parametrised
  form `AnnulusSchoenflies` used inside the construction is derived from it by
  `annulusSchoenflies_of_plain`),
* `SurfaceDiscPushOff` (the push-off of a surface disc),
* `CurvesInterior` (the position hypothesis on the slice discs) or `PinchedPushThrough` (Pardon's
  surgery in the pinched configuration),
* and, in addition, the **local flatness** of the slice discs,
  `∀ D, LocallyFlat D.e` (the tameness that the push-off needs; it is *not* a consequence of the
  `SliceDisc` structure, which assumes only that the disc is embedded continuously, and it is
  documented in §8.2 of the README).  The tameness is needed only where the named inputs are
  needed, and the hypotheses are consumed at the standard torus of revolution only.

Nothing outside `Submission/Work/Smooth/SphereJordan/` is modified.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.SphereJordan

noncomputable section

/-- **Pardon's cut-and-paste for an arbitrary parametrised torus** from the named inputs, under the
local flatness of the slice discs. -/
theorem cutsAlongSubdisc_of_props_all (hA : AnnulusSchoenflies)
    (hB : ∀ Q : Work.CoreTopology.ParamTorus, SurfaceDiscPushOff Q)
    (hC : ∀ Q : Work.CoreTopology.ParamTorus, CurvesInterior Q)
    (hTame : ∀ (Q : Work.CoreTopology.ParamTorus)
      (D : Work.Topology.SphereSlicing.SliceDisc Q), LocallyFlat D.e)
    (P : Work.CoreTopology.ParamTorus) :
    Work.Topology.Classical.CutsAlongSubdisc P :=
  cutsAlongSubdisc_of_props hA hB hC hTame P

/-- **`CleansDiscs` for an arbitrary parametrised torus**: the `cleans` field of
`Work.BoxShrink.FinalInput` at a single torus. -/
theorem cleansDiscs_of_props (hA : AnnulusSchoenflies)
    (hB : ∀ Q : Work.CoreTopology.ParamTorus, SurfaceDiscPushOff Q)
    (hC : ∀ Q : Work.CoreTopology.ParamTorus, CurvesInterior Q)
    (hTame : ∀ (Q : Work.CoreTopology.ParamTorus)
      (D : Work.Topology.SphereSlicing.SliceDisc Q), LocallyFlat D.e)
    (h : PlaneHypothesis)
    (P : Work.CoreTopology.ParamTorus) (h₂ : Work.Topology.Classical.InnermostCurveExists P) :
    Work.InnermostDisk.CleansDiscs P :=
  cleansDiscs_of_innermostCurveExists_of_cutsAlongSubdisc h₂
    (cutsAlongSubdisc_of_props hA hB hC hTame P)

/-- **`CleansDiscs` for an arbitrary parametrised torus**, with Pardon's first innermost step also
discharged from the planar theorem. -/
theorem cleansDiscs_of_props' (hA : AnnulusSchoenflies)
    (hB : ∀ Q : Work.CoreTopology.ParamTorus, SurfaceDiscPushOff Q)
    (hC : ∀ Q : Work.CoreTopology.ParamTorus, CurvesInterior Q)
    (hTame : ∀ (Q : Work.CoreTopology.ParamTorus)
      (D : Work.Topology.SphereSlicing.SliceDisc Q), LocallyFlat D.e)
    (h : PlaneHypothesis) (P : Work.CoreTopology.ParamTorus) :
    Work.InnermostDisk.CleansDiscs P :=
  cleansDiscs_of_plane_of_cutsAlongSubdisc h (cutsAlongSubdisc_of_props hA hB hC hTame P)

/-- **The packaged classical input `ClassicalTopology`** of `Work.Topology.Classical`, from the
planar theorem together with the named inputs. -/
theorem classicalTopology_of_props (hA : AnnulusSchoenflies)
    (hB : ∀ Q : Work.CoreTopology.ParamTorus, SurfaceDiscPushOff Q)
    (hC : ∀ Q : Work.CoreTopology.ParamTorus, CurvesInterior Q)
    (hTame : ∀ (Q : Work.CoreTopology.ParamTorus)
      (D : Work.Topology.SphereSlicing.SliceDisc Q), LocallyFlat D.e)
    (h : PlaneHypothesis) :
    Work.Topology.Classical.ClassicalTopology :=
  classicalTopology_of_plane h
    (cutsAlongSubdisc_of_props hA hB hC hTame Work.CoreTopology.standard)

/-- **Pardon's cut-and-paste for the tori of the challenge**
(`P = ParamTorus.mapHomeomorph ψ` for a homeomorphism `ψ` of `ℝ³`) from the planar theorem and the
named inputs. -/
theorem cleansDiscs_mapHomeomorph_of_props (hA : AnnulusSchoenflies)
    (hB : ∀ Q : Work.CoreTopology.ParamTorus, SurfaceDiscPushOff Q)
    (hC : ∀ Q : Work.CoreTopology.ParamTorus, CurvesInterior Q)
    (hTame : ∀ (Q : Work.CoreTopology.ParamTorus)
      (D : Work.Topology.SphereSlicing.SliceDisc Q), LocallyFlat D.e)
    (h : PlaneHypothesis) (ψ : R3 ≃ₜ R3) :
    Work.InnermostDisk.CleansDiscs (Work.CoreTopology.ParamTorus.mapHomeomorph ψ) :=
  cleansDiscs_mapHomeomorph h
    (cutsAlongSubdisc_of_props hA hB hC hTame Work.CoreTopology.standard) ψ

/-- **The `cleans` field of `Work.BoxShrink.FinalInput`** — `Work.BoxShrink.CleansDiscsAll` — from
the planar Jordan–Schoenflies theorem and the named inputs. -/
theorem cleansDiscsAll_of_props (hA : AnnulusSchoenflies)
    (hB : ∀ Q : Work.CoreTopology.ParamTorus, SurfaceDiscPushOff Q)
    (hC : ∀ Q : Work.CoreTopology.ParamTorus, CurvesInterior Q)
    (hTame : ∀ (Q : Work.CoreTopology.ParamTorus)
      (D : Work.Topology.SphereSlicing.SliceDisc Q), LocallyFlat D.e)
    (h : PlaneHypothesis) :
    ∀ ψ : Submission.Diffeo, Work.InnermostDisk.CleansDiscs
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) :=
  cleansDiscsAll_of_plane_of_cuts h
    (cutsAlongSubdisc_of_props hA hB hC hTame Work.CoreTopology.standard)

/-- **`CutsAlongSubdisc` for every torus, without a position hypothesis**, from the planar annulus
theorem, the push-off of a surface disc and Pardon's surgery in the pinched configuration. -/
theorem cutsAlongSubdisc_of_props_and_pinched_all (hA : AnnulusSchoenflies)
    (hB : ∀ Q : Work.CoreTopology.ParamTorus, SurfaceDiscPushOff Q)
    (hP : ∀ Q : Work.CoreTopology.ParamTorus, PinchedPushThrough Q)
    (hTame : ∀ (Q : Work.CoreTopology.ParamTorus)
      (D : Work.Topology.SphereSlicing.SliceDisc Q), LocallyFlat D.e)
    (P : Work.CoreTopology.ParamTorus) :
    Work.Topology.Classical.CutsAlongSubdisc P :=
  cutsAlongSubdisc_of_props_and_pinched hA hB hP hTame P

/-- **`CleansDiscs` for an arbitrary parametrised torus** from the planar theorem, the two classical
inputs and the pinched surgery. -/
theorem cleansDiscs_of_props_and_pinched (hA : AnnulusSchoenflies)
    (hB : ∀ Q : Work.CoreTopology.ParamTorus, SurfaceDiscPushOff Q)
    (hP : ∀ Q : Work.CoreTopology.ParamTorus, PinchedPushThrough Q)
    (hTame : ∀ (Q : Work.CoreTopology.ParamTorus)
      (D : Work.Topology.SphereSlicing.SliceDisc Q), LocallyFlat D.e)
    (h : PlaneHypothesis) (P : Work.CoreTopology.ParamTorus) :
    Work.InnermostDisk.CleansDiscs P :=
  cleansDiscs_of_plane_of_cutsAlongSubdisc h
    (cutsAlongSubdisc_of_props_and_pinched hA hB hP hTame P)

/-- **`ClassicalTopology`** from the planar theorem, the two classical inputs and the pinched
surgery. -/
theorem classicalTopology_of_props_and_pinched (hA : AnnulusSchoenflies)
    (hB : ∀ Q : Work.CoreTopology.ParamTorus, SurfaceDiscPushOff Q)
    (hP : ∀ Q : Work.CoreTopology.ParamTorus, PinchedPushThrough Q)
    (hTame : ∀ (Q : Work.CoreTopology.ParamTorus)
      (D : Work.Topology.SphereSlicing.SliceDisc Q), LocallyFlat D.e)
    (h : PlaneHypothesis) :
    Work.Topology.Classical.ClassicalTopology :=
  classicalTopology_of_plane h
    (cutsAlongSubdisc_of_props_and_pinched hA hB hP hTame Work.CoreTopology.standard)

/-- **The `cleans` field of `Work.BoxShrink.FinalInput`** from the planar theorem, the two classical
inputs `AnnulusSchoenflies` and `SurfaceDiscPushOff`, and the pinched surgery — with no position
hypothesis on the slice discs. -/
theorem cleansDiscsAll_of_props_and_pinched (hA : AnnulusSchoenflies)
    (hB : ∀ Q : Work.CoreTopology.ParamTorus, SurfaceDiscPushOff Q)
    (hP : ∀ Q : Work.CoreTopology.ParamTorus, PinchedPushThrough Q)
    (hTame : ∀ (Q : Work.CoreTopology.ParamTorus)
      (D : Work.Topology.SphereSlicing.SliceDisc Q), LocallyFlat D.e)
    (h : PlaneHypothesis) :
    ∀ ψ : Submission.Diffeo, Work.InnermostDisk.CleansDiscs
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) :=
  cleansDiscsAll_of_plane_of_cuts h
    (cutsAlongSubdisc_of_props_and_pinched hA hB hP hTame Work.CoreTopology.standard)

/-! ## The hypotheses are needed at the standard torus only

The delivered reduction `Work.Topology.Classical.classicalTopology_of_decomposed` and Pardon's
induction consume the cut-and-paste at the **standard torus of revolution**
`Work.CoreTopology.standard` only (everything is then transported along the ambient homeomorphism),
so the named inputs need to be available at `standard` only.  The following weakenings of the
assembly record that. -/

/-- **The cut-and-paste at the standard torus** from the two classical inputs at `standard` and the
position hypothesis at `standard`. -/
theorem cutsAlongSubdisc_standard_of_props (hA : AnnulusSchoenflies)
    (hB : SurfaceDiscPushOff Work.CoreTopology.standard)
    (hC : CurvesInterior Work.CoreTopology.standard)
    (hTame : ∀ D : Work.Topology.SphereSlicing.SliceDisc Work.CoreTopology.standard,
      LocallyFlat D.e) :
    Work.Topology.Classical.CutsAlongSubdisc Work.CoreTopology.standard := by
  intro D j f hf_inj hf_bd hf_off hf_sub hf_disj
  exact cutsAlongSubdisc_inside hA hB D (hTame D) j f hf_inj hf_bd hf_off hf_sub hf_disj
    (hC D j f hf_inj hf_bd hf_sub)

/-- **The cut-and-paste at the standard torus** from the two classical inputs at `standard` and the
pinched surgery at `standard` (no position hypothesis). -/
theorem cutsAlongSubdisc_standard_of_props_and_pinched (hA : AnnulusSchoenflies)
    (hB : SurfaceDiscPushOff Work.CoreTopology.standard)
    (hP : PinchedPushThrough Work.CoreTopology.standard)
    (hTame : ∀ D : Work.Topology.SphereSlicing.SliceDisc Work.CoreTopology.standard,
      LocallyFlat D.e) :
    Work.Topology.Classical.CutsAlongSubdisc Work.CoreTopology.standard :=
  cutsAlongSubdisc_of_props_or_pinched hA hB hP hTame

/-- **`Work.BoxShrink.CleansDiscsAll`** — the `cleans` field of `Work.BoxShrink.FinalInput` — from
the planar Jordan–Schoenflies theorem together with the two classical inputs and the position
hypothesis, **all at the standard torus of revolution only**. -/
theorem cleansDiscsAll_of_standard_props (hA : AnnulusSchoenflies)
    (hB : SurfaceDiscPushOff Work.CoreTopology.standard)
    (hC : CurvesInterior Work.CoreTopology.standard)
    (hTame : ∀ D : Work.Topology.SphereSlicing.SliceDisc Work.CoreTopology.standard,
      LocallyFlat D.e)
    (h : PlaneHypothesis) :
    ∀ ψ : Submission.Diffeo, Work.InnermostDisk.CleansDiscs
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) :=
  cleansDiscsAll_of_plane_of_cuts h (cutsAlongSubdisc_standard_of_props hA hB hC hTame)

/-- **`Work.BoxShrink.CleansDiscsAll`** from the planar theorem together with the two classical
inputs and the pinched surgery, **all at the standard torus of revolution only**. -/
theorem cleansDiscsAll_of_standard_props_and_pinched (hA : AnnulusSchoenflies)
    (hB : SurfaceDiscPushOff Work.CoreTopology.standard)
    (hP : PinchedPushThrough Work.CoreTopology.standard)
    (hTame : ∀ D : Work.Topology.SphereSlicing.SliceDisc Work.CoreTopology.standard,
      LocallyFlat D.e)
    (h : PlaneHypothesis) :
    ∀ ψ : Submission.Diffeo, Work.InnermostDisk.CleansDiscs
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) :=
  cleansDiscsAll_of_plane_of_cuts h (cutsAlongSubdisc_standard_of_props_and_pinched hA hB hP hTame)

/-! ## The 2-dimensional input in its plain (set-level) form

The parametrised form `AnnulusSchoenflies` is *equivalent* to the plain form
`PlainAnnulusSchoenflies` (`Work.Smooth.SphereJordan.annulusSchoenflies_of_plain`), so the whole
chapter can be stated with the plain form — the honest classical annulus theorem — as its
2-dimensional input. -/

/-- **The cut-and-paste at the standard torus** from the *plain* annulus theorem, the cap and the
pinched surgery. -/
theorem cutsAlongSubdisc_standard_of_plain (hA : PlainAnnulusSchoenflies)
    (hB : SurfaceDiscPushOff Work.CoreTopology.standard)
    (hP : PinchedPushThrough Work.CoreTopology.standard)
    (hTame : ∀ D : Work.Topology.SphereSlicing.SliceDisc Work.CoreTopology.standard,
      LocallyFlat D.e) :
    Work.Topology.Classical.CutsAlongSubdisc Work.CoreTopology.standard :=
  cutsAlongSubdisc_standard_of_props_and_pinched (annulusSchoenflies_of_plain hA) hB hP hTame

/-- **`Work.BoxShrink.CleansDiscsAll`** — the `cleans` field of `Work.BoxShrink.FinalInput` — from
the planar Jordan–Schoenflies theorem, the **plain** annulus theorem, the cap and the position
hypothesis, all at the standard torus of revolution. -/
theorem cleansDiscsAll_of_standard_plain (hA : PlainAnnulusSchoenflies)
    (hB : SurfaceDiscPushOff Work.CoreTopology.standard)
    (hC : CurvesInterior Work.CoreTopology.standard)
    (hTame : ∀ D : Work.Topology.SphereSlicing.SliceDisc Work.CoreTopology.standard,
      LocallyFlat D.e)
    (h : PlaneHypothesis) :
    ∀ ψ : Submission.Diffeo, Work.InnermostDisk.CleansDiscs
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) :=
  cleansDiscsAll_of_standard_props (annulusSchoenflies_of_plain hA) hB hC hTame h

/-- **`Work.BoxShrink.CleansDiscsAll`** from the planar theorem, the **plain** annulus theorem, the
cap and the pinched surgery, with no position hypothesis. -/
theorem cleansDiscsAll_of_standard_plain_and_pinched (hA : PlainAnnulusSchoenflies)
    (hB : SurfaceDiscPushOff Work.CoreTopology.standard)
    (hP : PinchedPushThrough Work.CoreTopology.standard)
    (hTame : ∀ D : Work.Topology.SphereSlicing.SliceDisc Work.CoreTopology.standard,
      LocallyFlat D.e)
    (h : PlaneHypothesis) :
    ∀ ψ : Submission.Diffeo, Work.InnermostDisk.CleansDiscs
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) :=
  cleansDiscsAll_of_standard_props_and_pinched (annulusSchoenflies_of_plain hA) hB hP hTame h

end

end Work.Smooth.SphereJordan
