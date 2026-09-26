import Mathlib
import Submission.Work.Drive.Mono.Residual
import Submission.Work.Drive.Mono.Split
import Submission.Work.Drive.Mono.DataExists_holds
import Submission.Work.EpsW.countsWd
import Submission.Work.Topology.SphereSlicing.frontier_PBox
import Submission.Work.Drive.EpsForm.sliceWallRoute
import Submission.Work.EpsW.exists_family_of_isCompact_of_isLocallyEuclidean
import Submission.Work.EpsW.arcsWallFamily_holds
import Submission.Work.Drive.Mono.LevelSetLocallyEuclidean_holds
import Submission.Work.Drive.Mono.Trace_eq_levelSet_near_wallPoint_holds
import Submission.Work.Drive.Mono.Trace_eq_planeNear_facePoint_holds
import Submission.Work.InnermostDisk.sphereSlicing_of_isEmbeddedSphere_of_traceCurves
import Submission.Work.Drive.EpsForm.encard_inter_sphereSet_lt_min
import Submission.Work.Drive.EpsFormSphere.encard_frontier_tiltedSweptBall_lt_min
import Submission.Work.Drive.Mono.encard_le_two_mul_of_cover
import Submission.Work.Drive.Mono.inbox_frontier_subset
import Submission.Work.Drive.Mono.TraceLocalModels
import Submission.Work.Drive.Mono.aboveGenericAt_of_junctionGen
import Submission.Work.Drive.Mono.aboveGenericAt_of_junctionGenC
import Submission.Work.Drive.Mono.TraceLocalModelsJunction
import Submission.Work.Drive.Mono.trace_localModels_of_junctionGenC
import Submission.Work.Drive.Mono.SlabCaps
import Submission.Work.Drive.Mono.frontier_PBox_sdiff_slab_eq_caps
import Submission.Work.Drive.Mono.isEmbeddedSphere_frontier_slabCaps
import Submission.Work.Drive.Mono.sphereSlicing_union_of_curveFamily
import Submission.Work.Drive.Mono.encard_frontier_lt_min_at_top
import Submission.Work.Drive.Mono.isEmbeddedSphere_frontier_levelChunk
import Submission.Work.Drive.Mono.encard_frontier_chunk_lt_min
import Submission.Work.Drive.Mono.encard_frontier_lt_min_of_face_wall
import Submission.Work.Topology.SphereSlicing.isEmbeddedSphere_BoxSphere
import Submission.Work.Drive.Mono.tiltedLevel_disjoint_spheres
import Submission.Work.Drive.Mono.LevelFrontierGen
import Submission.Work.Drive.Mono.LocalEuclideanTrace_of_traceCurves

/-!
# The residual of the tilted sweep: reduction lemmas

**The graze case (session H381-s8).**  The junction bundle `JunctionGenC` used by the residuals
`TraceDataInputsS`/`TraceDataInputsB` below has two *differential* clauses which are unsatisfiable at
a configuration where the surface is tangent to the box sphere (a *graze*) — machine-checked by
`Work.Drive.Mono.not_grazePoint_of_junctionGenC` and `Work.Drive.Mono.not_traceDataInputsS_of_grazePoint`
in `Mono/TiltedTraceDataWExistsE.lean` — while the deliverable quantifies over the box level, hence
over the graze configurations.  The graze case is analysed in
`Submission/Work/Drive/Mono/NOTES_H381_s8_graze.md`, and the deliverable's reduction there is re-run
with the corrected bundle `Work.Drive.Mono.JunctionGenE` and the data conditions
`Work.Drive.Mono.GrazeConditions` in the *downstream* modules

* `Submission/Work/Drive/Mono/WallInert.lean` (the transversality-free local models of the trace at a
  graze point, and the "wall-inert" lemmas),
* `Submission/Work/Drive/Mono/JunctionGenE.lean` (the corrected bundle and the graze obligation),
* `Submission/Work/Drive/Mono/GrazeConditions.lean` (the two graze conditions, and the proof that they
  discharge the graze obligation),
* `Submission/Work/Drive/Mono/trace_localModels_of_junctionGenE.lean` and
  `Submission/Work/Drive/Mono/aboveGenericAt_of_junctionGenE.lean` (the local models and clause 2 for
  the corrected bundle),
* `Submission/Work/Drive/Mono/TiltedTraceDataWExistsE.lean` (the corrected residual
  `Work.Drive.Mono.TraceDataInputsE` and `Work.Drive.Mono.TiltedTraceDataWExists_of_inputsE`),
* `Submission/Work/Drive/Mono/BridgeDataPackage.lean` (the bridges to the fleet's
  `Work.Drive.Mono.DataPackage`; in particular
  `Work.Drive.Mono.TiltedTraceDataWExists_of_goodSweepData_graze` shows that the fleet's two live
  fields plus `GrazeConditions` close the deliverable).

This module carries, under the deliverable `Work.Drive.Mono.TiltedTraceDataWExists` (the existence of
tilt data satisfying `TiltData` together with the trace data `TiltedTraceDataW` at every crux
configuration), the *fixed-datum* consequences of the trace data which the assembly
`Work.Drive.Mono.tiltedSweepMono_of_traceDataWExists` uses only in the universally quantified form:

* `windingSpan_bot_or_top_of_traceCurvesAt` — Pardon's dichotomy (field `(D)`) at a *fixed* level whose
  trace is a family of pairwise disjoint simple inessential curves (clause 1);
* `windingSpan_end_ne_bot_of_tiltedTraceDataW` — the infimum assembly at *fixed* data: `TiltData` plus
  the trace data plus `W = ⊤` at the start of the window give `W ≠ ⊥` at the end;
* `windingSpan_ne_bot_of_tiltedTraceDataW` — hence `W ≠ ⊥` at *every* level of the window.  This is a
  *necessary condition* on any datum witnessing the residual: in particular the data of the upstream
  genericity theorem cannot witness it (`not_tiltedTraceDataW_of_slab_contains_box`, the machine-checked
  form of the diagnosis in the statement of the deliverable: a slab that swallows the box makes the
  region empty at the end of the window, so the trace data fail there);
* `traceCurvesAt_of_slab_disjoint_carrier`, `aboveGenericAt_of_slab_disjoint_carrier` and their package
  `tiltedTraceDataW_of_slab_disjoint_carrier`: the trace data at a datum whose slab misses the surface
  altogether — the case in which both clauses are elementary (`exc = ∅`), which is how the residual is
  discharged whenever such a datum exists;
* `carrier_inter_subset_iUnion_range_slicing`: a slicing of a sphere covers the surface's intersection
  with it, by the *constant* loops (no transversality).

## State of the reduction (session H381-L1107; full account in `NOTES_hcross.md`)

The obstruction of the `∀ u` form at a *bad* cutting level (`u = z (σ 2) - c (σ 2)` for a knot point
`z` on the box sphere, where `Work.Drive.Mono.one_le_encard_boxSphere_openSlab` forces a box-sphere
point of the knot into the open slab for *every* datum) has been localised exactly:

* the visit counting of `Work.Drive.Mono.levelCount_lt_min_all` consumes `hboxsph` **only** through the
  fact that every `visit` of the knot to the box-and-open-slab contains a crossing of the cutting plane
  (this is `Work.Drive.Mono.HCross`, `Submission/Work/Drive/Mono/Hcross.lean`; `hboxsph` implies it, and
  it is equivalent to "no visit is strictly one-sided");
* with `HCross` in place of `hboxsph` the whole level count goes through at *every* level of the
  window (delegated: `Work.Mono.visit_facts_le_hcross`, `Work.Mono.levelCount_lt_min_all_hcross` in
  `Submission/Work/Mono/`), so the residual of the deliverable is exactly: produce data with `TiltData`
  whose visits all cross the cutting plane, together with the junction genericity, the face regularity,
  the graze conditions and clause 4;
* `cutG = φ + ⟪v - e_{σ 2}, · - c⟫` *exactly*, with `φ := (·)(σ 2) - c (σ 2) - u` independent of the
  tilt: a one-sided visit can be removed only by the *sign* of the tilt term at the bad box-sphere
  points, while the size condition `h > ‖v - e_{σ 2}‖ R` forces `|cutG| < h` there.  Hence `HCross` at
  a bad cutting level is a finite sign condition on the tilt direction and the knot's exit heights, and
  it is *not* a consequence of the crux's hypotheses;
* `Work.Drive.Mono.exists_essentialLoop_sdiff_slab_of_traceData` (below) is the matching *necessary*
  condition on the data: the slab of any datum of the residual must leave an essential loop of the box
  outside it (whence clause 4 is free there, `noJumpBelowAt_of_span_ne_bot`).
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

noncomputable section

variable {P : Work.CoreTopology.ParamTorus} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
  {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam lam0 lam1 : ℝ} {exc : Finset ℝ}

/-! ## The constant loop and the covering property of a slicing -/

/-- The **constant closed curve** at a point of the surface. -/
def constClosedCurveMono (z : R3) (hz : z ∈ P.carrier) : Work.CoreTopology.ClosedCurve P where
  γ := fun _ => z
  cont := continuous_const
  periodic := fun _ => rfl
  mem := fun _ => hz

/-- **A slicing of a sphere covers the surface's intersection with it.**  Apply the `covers` field of
the slicing to the constant loop at a point of the intersection; no transversality is needed. -/
theorem carrier_inter_subset_iUnion_range_slicing {S : Set R3}
    (h : Work.InnermostDisk.SphereSlicing P S) :
    P.carrier ∩ S ⊆ ⋃ i, Set.range (h.c i).γ := by
  intro z hz
  obtain ⟨hzc, hzS⟩ := hz
  obtain ⟨i, hi⟩ := h.covers (constClosedCurveMono (P := P) z hzc) (fun _ => hzS)
  exact Set.mem_iUnion.mpr ⟨i, hi ⟨0, rfl⟩⟩

/-- **Clause 1 from a slicing of the level's frontier and the absence of essential loops in it.**

This is the *leanest* form of Pardon's second input at a level of the sweep, and the form in which
the residual is honestly attacked: the hypothesis is a `Work.InnermostDisk.SphereSlicing` of the
level's frontier — the classical PL description of the trace, finite by construction — together with
the statement that the frontier carries no essential loop (which the level count supplies).  Note
that **no local model of the trace is needed** (the slicing *is* the family of curves) and that
`IsEmbeddedSphere` is *not* assumed (the frontier of the level's removed set need not be a single
sphere: above the `ell`-range of the box it is a disjoint union of two of them, and at a corner of
the wall with the box boundary even the union-of-spheres statement is false — the honest datum is
the slicing, and `sphereSlicing_union` below combines the slicings of the pieces). -/
theorem traceCurvesAt_of_slicing {S : Set R3}
    (Sl : Work.InnermostDisk.SphereSlicing P S)
    (hine : ¬ P.ContainsEssentialLoop S)
    (hSeq : S = frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) :
    TraceCurvesAt P s c σ u v h ℓ lam := by
  classical
  refine ⟨Fintype.card Sl.ι, fun i => Sl.c ((Fintype.equivFin Sl.ι).symm i), ?_, ?_, ?_, ?_⟩
  · intro i; exact Sl.simple _
  · intro i hi
    exact hine ⟨Sl.c ((Fintype.equivFin Sl.ι).symm i), hi, fun t => Sl.mem _ t⟩
  · intro i j hij
    exact Sl.disjoint (fun hh => hij (by simpa using congrArg (Fintype.equivFin Sl.ι) hh))
  · apply Set.Subset.antisymm
    · rintro z hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      obtain ⟨t, ht⟩ := hi
      exact ⟨(Sl.c ((Fintype.equivFin Sl.ι).symm i)).range_subset_carrier ⟨t, ht⟩,
        by rw [← hSeq]; exact ht ▸ Sl.mem _ t⟩
    · intro z hz
      obtain ⟨hzc, hzfr⟩ := hz
      have hzS : z ∈ S := by rw [hSeq]; exact hzfr
      have h2 := carrier_inter_subset_iUnion_range_slicing (P := P) Sl ⟨hzc, hzS⟩
      simp only [Set.mem_iUnion] at h2 ⊢
      obtain ⟨i, hi⟩ := h2
      exact ⟨Fintype.equivFin Sl.ι i, by simpa using hi⟩

/-- **Clause 1 at the bottom level of the window.**

If the level `lam` is at most `ell` on the box, then the region `{ℓ < lam}` misses the box (and the
slab), so the removed set of the level is the whole box and the level's frontier is the box sphere
`{boxNorm c σ · = s}`.  The clause follows: the slicing `hslice` of the box sphere *is* a slicing of
the frontier, and the crux's box-sphere count makes the box-sphere trace inessential
(`Work.EpsW.sphereTrace_inessential_of_countsWd`).  **No genericity of the sweep height is used**,
and in particular this discharges clause 1 at the *first* level of every window (`lam0`), the level
at which the sweep starts with the whole box region. -/
theorem traceCurvesAt_at_window_bottom
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hslice : Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
      {y : R3 | Submission.boxNorm c σ y = s})
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
    {u : ℝ} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    (hlam : ∀ y ∈ Submission.PBox s c σ, lam ≤ ℓ y) :
    TraceCurvesAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam := by
  have hrem : tiltedLevelRemoved s c σ u v h ℓ lam = Submission.PBox s c σ := by
    ext y
    rw [tiltedLevelRemoved]
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · exact fun h => h.1
    · intro hy
      exact ⟨hy, fun hc' => absurd (hlam y hy) (not_le.mpr hc'.2)⟩
  have hfr : frontier (tiltedLevelRemoved s c σ u v h ℓ lam) =
      {y : R3 | Submission.boxNorm c σ y = s} := by
    rw [hrem, Work.Topology.SphereSlicing.frontier_PBox hs c σ]
    rfl
  have hne : Nonempty (Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
      {y : R3 | Submission.boxNorm c σ y = s}) := hslice
  obtain ⟨Sl⟩ := hne
  refine traceCurvesAt_of_slicing (S := {y : R3 | Submission.boxNorm c σ y = s}) Sl ?_ hfr.symm
  exact Work.EpsW.sphereTrace_inessential_of_countsWd p q hp hq hc ψ K hd himg hsmall hs c σ
    hslice hcl hcount

/-- **Clause 1 from the trace curves bounding discs *in the surface*.**

By `Work.InnermostDisk.boundsDiscInSurface_iff_not_isEssential` the two forms of inessentiality of a
closed curve of the surface are *equivalent* (`¬ IsEssential P α ↔ BoundsDiscInSurface P α`), so this
is a restatement of clause 1 in the vocabulary in which the **geometry** delivers it: the pieces of
the level's removed set inside the box and the slab are (generically) discs of the surface, and the
trace curves are their boundaries.  Contrast with the counting route
(`not_containsEssentialLoop_frontier_of_counts`), which is the only route available for *arbitrary*
data and which needs a `SphereSlicing` of the frontier and the level count. -/
theorem traceCurvesAt_of_boundsDiscs {P : Work.CoreTopology.ParamTorus} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    (n : ℕ) (cs : Fin n → Work.CoreTopology.ClosedCurve P)
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (cs i))
    (hdisc : ∀ i, Work.InnermostDisk.BoundsDiscInSurface P (cs i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ))
    (hcov : (⋃ i, Set.range (cs i).γ) =
      P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) :
    TraceCurvesAt P s c σ u v h ℓ lam :=
  ⟨n, cs, hsimple,
    fun i => Work.InnermostDisk.not_isEssential_of_boundsDiscInSurface P (hdisc i), hdisj, hcov⟩

/-! ## Pardon's dichotomy at a fixed datum -/

/-- **Pardon's dichotomy at a fixed datum, from clause 1 alone.**  If the trace of the level `lam` is
the union of the ranges of finitely many pairwise disjoint simple *inessential* closed curves of the
surface, then the winding span of the level's open region is `⊥` or `⊤`.

This is the body of the `(D)` field of the assembly `Work.Drive.Mono.tiltedSweepMono_of_traceData`,
with the data fixed. -/
theorem windingSpan_bot_or_top_of_traceCurvesAt (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hcurves : TraceCurvesAt P s c σ u v h ℓ lam) :
    Work.SurgeryInvariance.WindingSpan P
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam) = ⊥ ∨
      Work.SurgeryInvariance.WindingSpan P
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam) = ⊤ := by
  obtain ⟨n, cs, hsimple, hiness, hdisj, hunion⟩ := hcurves
  set Rle : Set R3 := Submission.PBox s c σ \
      (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y ≤ lam})
    with hRledef
  set Rlt : Set R3 := Submission.PBox s c σ \
      (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y < lam})
    with hRltdef
  have hfr : frontier Rle = frontier Rlt :=
    Work.Drive.EpsFormSphere.frontier_tiltedSweptBall_eq σ u ℓ hv hℓv hℓne
  have htrace : (⋃ i, Set.range (cs i).γ) = P.carrier ∩ frontier Rle := by
    rw [hunion]
    show P.carrier ∩ frontier Rlt = P.carrier ∩ frontier Rle
    rw [← hfr]
  have hTclosed : IsClosed (⋃ i, Set.range (cs i).γ) :=
    (isCompact_iUnion (fun i =>
      Work.BoxShrink.PinchOff.isCompact_range_closedCurve (cs i))).isClosed
  set X : Set R3 := Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam with hXdef
  have hXeq : X = P.carrier ∩ Rle := rfl
  set Y : Set R3 := P.carrier \ ((⋃ i, Set.range (cs i).γ) ∪ closure X) with hYdef
  refine Work.BoxShrink.PinchOff.windingSpan_bot_or_top_of_inessential_boundary
    (P := P) (X := X) (Y := Y) (n := n) (γ := cs) hsimple hiness hdisj ?_ ?_ ?_ ?_
  · exact Work.Drive.EpsFormSphere.isOpenInCarrier_openTiltedSweepRegion
  · rw [hYdef, Set.sdiff_eq]
    refine Work.SurgeryInvariance.isOpenInCarrier_carrier_inter (P := _) ?_
    exact (hTclosed.union isClosed_closure).isOpen_compl
  · rw [Set.disjoint_left]
    intro z hzX hzY
    exact hzY.2 (Or.inr (subset_closure hzX))
  · ext z
    constructor
    · rintro ⟨hzc, hzT⟩
      by_cases hzX : z ∈ X
      · exact Or.inl hzX
      · refine Or.inr ⟨hzc, ?_⟩
        intro hmem
        rcases hmem with hzT' | hzcl
        · exact hzT hzT'
        · have hzfr : z ∉ frontier Rle := by
            intro hfr'
            exact hzT (by rw [htrace]; exact ⟨hzc, hfr'⟩)
          have hzRle : z ∉ Rle := fun hzRle => hzX (by rw [hXeq]; exact ⟨hzc, hzRle⟩)
          have hsub : closure X ⊆ closure Rle :=
            closure_mono (by rw [hXeq]; exact Set.inter_subset_right)
          have hclR : z ∈ closure Rle := hsub hzcl
          rw [closure_eq_self_union_frontier] at hclR
          rcases hclR with hcl | hfr'
          · exact hzRle hcl
          · exact hzfr hfr'
    · rintro (hzX | hzY)
      · refine ⟨?_, ?_⟩
        · rw [hXeq] at hzX
          exact hzX.1
        · intro hzT'
          have hzfr : z ∈ frontier Rle := by rw [htrace] at hzT'; exact hzT'.2
          rw [hXeq] at hzX
          have hleopen : IsOpen Rle := by
            rw [hRledef]
            exact (Work.Topology.SphereSlicing.isOpen_PBox s c σ).sdiff
              ((Work.Drive.EpsForm.isClosed_tiltedSlabClosed (inner ℝ v c + u) v h).inter
                (isClosed_Iic.preimage ℓ.continuous))
          have h2 : z ∈ closure Rle \ Rle := hleopen.frontier_eq ▸ hzfr
          exact h2.2 hzX.2
      · exact ⟨hzY.1, fun hzT' => hzY.2 (Or.inl hzT')⟩

/-! ## The infimum assembly at a fixed datum -/

/-- **The infimum assembly at a fixed datum**: `TiltData` together with the windowed trace data at the
data and `W = ⊤` at the start of the window give `W ≠ ⊥` at the end of the window.

This is the fixed-datum content of the consumer
`Work.Drive.Final.cruxCoreWd_of_tiltedSweepMono` (`windingSpan_end_ne_bot_of_fields` fed by the
dichotomy `(D)` of clause 1 and the no-drop `(L)`, which is clause 4 at the exceptional levels and the
proved `Work.Drive.Mono.noJumpBelow_of_traceCurves` at the others). -/
theorem windingSpan_end_ne_bot_of_tiltedTraceDataW
    (hv1 : ‖v‖ = 1) (hℓne : ℓ ≠ 0) (hℓv : ℓ v = 0)
    (hW : TiltedTraceDataW P s c σ u v h ℓ exc lam0 lam1)
    (hstart : Work.SurgeryInvariance.WindingSpan P
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam0) = ⊤) :
    Work.SurgeryInvariance.WindingSpan P
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam1) ≠ ⊥ := by
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv1
    exact one_ne_zero hv1.symm
  refine Work.Drive.Final.windingSpan_end_ne_bot_of_fields (lam0 := lam0) (lam1 := lam1)
    (exc := exc) P s c σ u v h ℓ hstart ?_ ?_
  · intro lam hlam hne
    exact windingSpan_bot_or_top_of_traceCurvesAt (P := P) hvne hℓv hℓne (hW.1 lam hlam hne)
  · intro lam hlam hbot
    by_cases he : lam ∈ (exc : Set ℝ)
    · exact hW.2.2 lam hlam he hbot
    · exact Work.Drive.Mono.noJumpBelow_of_traceCurves (P := P) hvne hℓv hℓne
        (hW.1 lam hlam he) (hW.2.1 lam hlam he) hbot

/-- **The necessary condition on any datum satisfying the trace data**: if the region has full span at
the start of the window then it has non-vanishing span at *every* level of the window.

In particular the data of the upstream genericity theorem — whose slab swallows the box, so that the
region is empty at the end of the window — cannot satisfy `TiltedTraceDataW`: see
`not_tiltedTraceDataW_of_slab_contains_box`. -/
theorem windingSpan_ne_bot_of_tiltedTraceDataW
    (hv1 : ‖v‖ = 1) (hℓne : ℓ ≠ 0) (hℓv : ℓ v = 0)
    (hW : TiltedTraceDataW P s c σ u v h ℓ exc lam0 lam1)
    (hstart : Work.SurgeryInvariance.WindingSpan P
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam0) = ⊤) :
    ∀ lam ∈ Set.Icc lam0 lam1,
      Work.SurgeryInvariance.WindingSpan P
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam) ≠ ⊥ := by
  intro lam hlam hbot
  have hmono := Work.SurgeryInvariance.WindingSpan_mono (P := P)
    (X := Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam1)
    (Y := Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam)
    (Work.Drive.Final.sweep_anti hlam.2)
  rw [hbot] at hmono
  exact windingSpan_end_ne_bot_of_tiltedTraceDataW (P := P) hv1 hℓne hℓv hW hstart
    (le_bot_iff.mp hmono)

/-! ## A necessary condition: the slab must trench the box -/

/-- **A necessary condition on any datum witnessing the trace data: the box minus the closed slab must
contain an essential loop of the surface.**

`TiltData` together with `TiltedTraceDataW` forces the span of the level region to be non-vanishing at
*every* level of the window (`windingSpan_ne_bot_of_tiltedTraceDataW`), and at the top of the window
the level region is the box region with the closed tilted slab removed
(`Work.Drive.EpsFormSphere.openTiltedSweepRegion_eq_sdiff`).  Hence the slab of any datum of the
residual genuinely *trenches* the box: some essential loop of the box avoids the closed tilted slab.

Consequences: (i) it excludes the degenerate data of the upstream genericity theorem, whose slab
swallows the box (`not_tiltedTraceDataW_of_slab_contains_box`); (ii) at a crux configuration it says
that the tilt must be chosen so that an essential loop of the box lies at a positive gap from the
cutting plane — exactly the loop that `Work.Drive.Final.cruxCoreWd_of_noEquator_regular` produces in
the no-equator case, which is why clause 4 is free there (`noJumpBelowAt_of_span_ne_bot`). -/
theorem exists_essentialLoop_sdiff_slab_of_traceData
    {ψ : Submission.Diffeo} {R : ℝ}
    (hv1 : ‖v‖ = 1) (hℓne : ℓ ≠ 0) (hℓv : ℓ v = 0)
    (hT : TiltData ψ s c σ u v h R ℓ exc lam0 lam1)
    (hW : TiltedTraceDataW P s c σ u v h ℓ exc lam0 lam1)
    (hstart : Work.SurgeryInvariance.WindingSpan P
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam0) = ⊤) :
    P.ContainsEssentialLoop (Work.BoxShrink.Core.boxRegion P s c σ \
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) := by
  have hlt : lam0 < lam1 := hT.2.2.2.2.2.2.2.2.2.1
  have hhigh : ∀ y ∈ Submission.PBox s c σ, ℓ y < lam1 := hT.2.2.2.2.2.2.2.2.1
  have hne := windingSpan_ne_bot_of_tiltedTraceDataW (P := P) (s := s) (c := c) (σ := σ)
    (u := u) (v := v) (h := h) (ℓ := ℓ) (exc := exc) (lam0 := lam0) (lam1 := lam1)
    hv1 hℓne hℓv hW hstart lam1 ⟨le_of_lt hlt, le_rfl⟩
  rw [Work.Drive.EpsFormSphere.openTiltedSweepRegion_eq_sdiff (P := P) (s := s) (c := c)
    (σ := σ) (u := u) (v := v) (h := h) (ℓ := ℓ) (lam := lam1) hhigh] at hne
  exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hne

/-! ## The data of the upstream genericity theorem cannot witness the trace data -/

/-- **A slab that swallows the box makes the region empty at the top of the window.** -/
theorem openTiltedSweepRegion_eq_empty_of_slab_contains_box
    (hslab : ∀ y ∈ Submission.PBox s c σ, |inner ℝ v y - (inner ℝ v c + u)| ≤ h)
    (hhigh : ∀ y ∈ Submission.PBox s c σ, ℓ y < lam) :
    Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam = ∅ := by
  ext y
  constructor
  · intro hy
    rw [Work.Drive.Mono.mem_openTiltedSweepRegion_iff] at hy
    exact hy.2.2 ⟨hslab y hy.2.1, le_of_lt (hhigh y hy.2.1)⟩
  · intro hy
    exact absurd hy (Set.notMem_empty y)

/-- **The data of the upstream genericity theorem cannot satisfy the trace data.**

If the slab swallows the box then the region of the sweep at every level above the `ℓ`-range of the box
is empty, so its span is `⊥`; but `TData` together with `TiltedTraceDataW` forces the span of the region
at the end of the window to be non-vanishing (`windingSpan_ne_bot_of_tiltedTraceDataW`, whose start
hypothesis is Pardon's `⊤` at the box region, supplied by `HasEssBox` and the box-sphere count).

This is the machine-checked form of the diagnosis recorded in the statement of the deliverable: the
half-width `h = ε·R + R + |u| + 1` of `Work.Drive.EpsForm.tiltedSweepGenericity_holds_sized` (with
`‖v - shiftVσ σ 1‖ ≤ ε`) contains the box strictly — `|⟪v,y⟫ - a| ≤ ‖y - c‖ + |u| ≤ R + |u| < h` for
every `y ∈ PBox s c σ` — hence those data cannot witness `Work.Drive.Mono.TiltedTraceDataWExists`, and
the *thin*-slab data of the deliverable's route are unavoidable. -/
theorem not_tiltedTraceDataW_of_slab_contains_box
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {r : ℝ} (hr : 0 < r) {c : R3} {σ : Equiv.Perm (Fin 3)}
    (hbox : Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ)
    {s : ℝ} (hrs : r < s) (hs : s < (1 + Submission.eps) * r)
    (hslice : Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
        {y : R3 | Submission.boxNorm c σ y = s})
    {u : ℝ} (hu : |u| < Submission.eps * r)
    (hS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
    (hU : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)))
    {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 : ℝ}
    (hT : TiltData ψ s c σ u v h R ℓ exc lam0 lam1)
    (hslab : ∀ y ∈ Submission.PBox s c σ, |inner ℝ v y - (inner ℝ v c + u)| ≤ h) :
    ¬ TiltedTraceDataW (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ exc lam0 lam1 := by
  intro hW
  obtain ⟨_hgen, hv1, hℓne, hℓv, _hsize, _hh, _hRbox, hlow, hhigh, _hl, _hexc⟩ := hT
  set P := Work.Drive.EpsSphere.torusOf ψ with hP
  have hs0 : 0 < s := lt_trans hr hrs
  -- the span at the box region is not `⊥`
  have hnoS : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) :=
    Work.EpsW.sphereTrace_inessential_of_countsWd p q hp hq hc ψ K hd himg hsmall hs0 c σ hslice
      hcl hS
  have hne : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊥ :=
    (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr
      (Work.BoxShrink.Core.containsEssentialLoop_boxRegion_of_hasEssBox (le_of_lt hrs) hbox)
  have hstart : Work.SurgeryInvariance.WindingSpan P
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam0) = ⊤ := by
    rw [Work.Drive.EpsFormSphere.openTiltedSweepRegion_eq_boxRegion hlow]
    exact Work.Drive.EpsForm.windingSpan_boxRegion_eq_top_of_sphereTrace_inessential hs0 hslice
      hnoS hne
  have hnebot : ∀ lam ∈ Set.Icc lam0 lam1,
      Work.SurgeryInvariance.WindingSpan P
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam) ≠ ⊥ :=
    windingSpan_ne_bot_of_tiltedTraceDataW (P := P) hv1 hℓne hℓv hW hstart
  have hmem : lam1 ∈ Set.Icc lam0 lam1 := ⟨le_of_lt _hl, le_refl lam1⟩
  have hempty := openTiltedSweepRegion_eq_empty_of_slab_contains_box (P := P) hslab hhigh
  have hbot : Work.SurgeryInvariance.WindingSpan P
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam1) = ⊥ := by
    rw [hempty]
    by_contra hcon
    obtain ⟨γ, _hess, hγ⟩ := (Work.SurgeryInvariance.windingSpan_ne_bot_iff P ∅).mp hcon
    exact Set.notMem_empty (γ 0) (hγ 0)
  exact hnebot lam1 hmem hbot

/-! ## The trace data at a datum whose slab misses the surface -/

/-- **Clause 1 at a datum whose slab misses the surface.**  If no point of the surface lies in the
closed tilted slab, then the level's removed set has the same frontier on the surface as the box, so
the trace of every level is the surface's intersection with the box sphere — which a slicing of the box
sphere covers, and whose curves are inessential as soon as the box sphere carries no essential loop.

The two directions of the frontier identity use the surface points only (the frontier of the removed
set contains the slab faces and the level wall *inside the box*, which miss the surface under the
hypothesis). -/
theorem traceCurvesAt_of_slab_disjoint_carrier (hs : 0 < s)
    (Sl : Work.InnermostDisk.SphereSlicing P (Work.BoxShrink.Core.sphereSet c σ s))
    (hnoS : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s))
    (hslab : ∀ y ∈ P.carrier, |inner ℝ v y - (inner ℝ v c + u)| ≤ h → False) :
    TraceCurvesAt P s c σ u v h ℓ lam := by
  classical
  have hcont : Continuous fun y : R3 => |inner ℝ v y - (inner ℝ v c + u)| := by fun_prop
  have hfrPBox : frontier (Submission.PBox s c σ) = Work.BoxShrink.Core.sphereSet c σ s := by
    rw [Work.Topology.SphereSlicing.frontier_PBox hs c σ,
      Work.BoxShrink.Core.sphereSet_eq_BoxSphere]
  -- the frontier of the removed set, on the surface, is the frontier of the box
  have hfr : ∀ z ∈ P.carrier,
      (z ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) ↔
        z ∈ frontier (Submission.PBox s c σ)) := by
    intro z hzc
    have hgt : h < |inner ℝ v z - (inner ℝ v c + u)| := not_le.mp (hslab z hzc)
    constructor
    · intro hz
      rw [← closure_sdiff_interior] at hz
      have hzcl : z ∈ closure (Submission.PBox s c σ) :=
        closure_mono (fun y hy => hy.1) hz.1
      rw [closure_eq_self_union_frontier] at hzcl
      rcases hzcl with hzbox | hzfr
      · exfalso
        have hTopen : IsOpen (Submission.PBox s c σ ∩
            {y : R3 | h < |inner ℝ v y - (inner ℝ v c + u)|}) :=
          (Work.Topology.SphereSlicing.isOpen_PBox s c σ).inter
            (isOpen_lt continuous_const hcont)
        have hTsub : Submission.PBox s c σ ∩
            {y : R3 | h < |inner ℝ v y - (inner ℝ v c + u)|} ⊆
            tiltedLevelRemoved s c σ u v h ℓ lam := by
          rintro y ⟨hyb, hy⟩
          refine ⟨hyb, ?_⟩
          rintro ⟨hcon, -⟩
          simp only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_setOf_eq] at hcon
          exact absurd hcon (not_le.mpr hy)
        exact hz.2 (interior_maximal hTsub hTopen ⟨hzbox, hgt⟩)
      · exact hzfr
    · intro hzfr
      have hzclP : z ∈ closure (Submission.PBox s c σ) := frontier_subset_closure hzfr
      have hznotbox : z ∉ Submission.PBox s c σ := by
        intro hzb
        rw [(Work.Topology.SphereSlicing.isOpen_PBox s c σ).frontier_eq] at hzfr
        exact hzfr.2 hzb
      rw [← closure_sdiff_interior]
      refine ⟨?_, ?_⟩
      · rw [mem_closure_iff]
        intro V hVopen hzV
        have hWopen : IsOpen (V ∩ {y : R3 | h < |inner ℝ v y - (inner ℝ v c + u)|}) :=
          hVopen.inter (isOpen_lt continuous_const hcont)
        obtain ⟨y, hyV, hybox⟩ := mem_closure_iff.mp hzclP _ hWopen ⟨hzV, hgt⟩
        refine ⟨y, hyV.1, hybox, ?_⟩
        rintro ⟨hcon, -⟩
        simp only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_setOf_eq] at hcon
        exact absurd hcon (not_le.mpr hyV.2)
      · intro hint
        exact hznotbox (interior_subset hint).1
  -- the trace is the surface's intersection with the box sphere, covered by the slicing
  have hfront : P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) =
      P.carrier ∩ Work.BoxShrink.Core.sphereSet c σ s := by
    ext z
    constructor
    · rintro ⟨hzc, hz⟩
      exact ⟨hzc, hfrPBox ▸ (hfr z hzc).mp hz⟩
    · rintro ⟨hzc, hz⟩
      exact ⟨hzc, (hfr z hzc).mpr (hfrPBox ▸ hz)⟩
  let e : Sl.ι ≃ Fin (Fintype.card Sl.ι) := Fintype.equivFin Sl.ι
  refine ⟨Fintype.card Sl.ι, fun i => Sl.c (e.symm i), ?_, ?_, ?_, ?_⟩
  · intro i; exact Sl.simple (e.symm i)
  · intro i hess; exact hnoS ⟨Sl.c (e.symm i), hess, Sl.mem (e.symm i)⟩
  · intro i j hij
    have hne : e.symm i ≠ e.symm j := fun hcon => hij (by simpa using congrArg e hcon)
    exact Sl.disjoint hne
  · rw [hfront]
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      obtain ⟨t, ht⟩ := hi
      rw [← ht]
      exact ⟨(Sl.c (e.symm i)).mem t, Sl.mem (e.symm i) t⟩
    · intro z hz
      obtain ⟨hzc, hzS⟩ := hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (carrier_inter_subset_iUnion_range_slicing Sl ⟨hzc, hzS⟩)
      refine Set.mem_iUnion.mpr ⟨e j, ?_⟩
      simpa using hj

/-- **Clause 2 at a datum whose slab misses the surface** is vacuous: a point of the surface in the
closed tilted slab does not exist. -/
theorem aboveGenericAt_of_slab_disjoint_carrier
    (hslab : ∀ y ∈ P.carrier, |inner ℝ v y - (inner ℝ v c + u)| ≤ h → False) :
    AboveGenericAt P s c σ u v h ℓ lam := by
  intro z hzc _hcl hslabmem _hl
  exact absurd (hslab z hzc hslabmem) not_false

/-- **The trace data at a datum whose slab misses the surface**, with the empty exceptional set: both
clauses hold at *every* level of the window and clause 4 has no level to apply to. -/
theorem tiltedTraceDataW_of_slab_disjoint_carrier (hs : 0 < s)
    (Sl : Work.InnermostDisk.SphereSlicing P (Work.BoxShrink.Core.sphereSet c σ s))
    (hnoS : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s))
    (hslab : ∀ y ∈ P.carrier, |inner ℝ v y - (inner ℝ v c + u)| ≤ h → False) :
    TiltedTraceDataW P s c σ u v h ℓ (∅ : Finset ℝ) lam0 lam1 :=
  ⟨fun _lam _ _ => traceCurvesAt_of_slab_disjoint_carrier (P := P) hs Sl hnoS hslab,
   fun _lam _ _ => aboveGenericAt_of_slab_disjoint_carrier (P := P) hslab,
   fun _lam _ hmem => absurd hmem (by simp)⟩

/-! ## (P1): clause 1 from the local structure and the count -/

/-- **(P1)(a)+(b): clause 1 from the local structure alone.**

If the trace of the level — the surface's part of the frontier of the level's removed set — is compact
and locally Euclidean of dimension one, then it is the union of the ranges of finitely many pairwise
disjoint simple closed curves (`Work.EpsW.exists_family_of_isCompact_of_isLocallyEuclidean`); and if no
essential loop of the surface lies in the frontier of the level's removed set (the inessentiality
input, obtained from the count in `traceCurvesAt_of_isLocallyEuclidean_of_counts`), each of those
curves is inessential, which is clause 1.

This is the assembly step `(P1)` of the design: it isolates the two geometric inputs which remain —
the local models at every point of the trace (the "crossing conditions") and the count. -/
theorem traceCurvesAt_of_isLocallyEuclidean
    (hcomp : IsCompact (P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))
    (hloc : Work.Smooth.OneManifold.IsLocallyEuclidean
      (P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))
    (hnoess : ¬ P.ContainsEssentialLoop (frontier (tiltedLevelRemoved s c σ u v h ℓ lam))) :
    TraceCurvesAt P s c σ u v h ℓ lam := by
  set Z : Set R3 := P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) with hZdef
  obtain ⟨n, γ, hsimple, hdisj, hZ⟩ :=
    Work.EpsW.exists_family_of_isCompact_of_isLocallyEuclidean (P := P) (Z := Z)
      (by rw [hZdef]; exact Set.inter_subset_left) (by rw [hZdef]; exact hcomp)
      (by rw [hZdef]; exact hloc)
  have htrace : (⋃ i, Set.range (γ i).γ) = P.carrier ∩ frontier
      (tiltedLevelRemoved s c σ u v h ℓ lam) := by
    rw [← hZ, hZdef]
  refine ⟨n, γ, hsimple, ?_, hdisj, htrace⟩
  intro i hess
  refine hnoess ⟨γ i, hess, fun t => ?_⟩
  have hmem : (γ i).γ t ∈ Z := by
    rw [hZ]
    exact Set.mem_iUnion.mpr ⟨i, ⟨t, rfl⟩⟩
  rw [hZdef] at hmem
  exact hmem.2

/-- **(P1)(c): the inessentiality input from the count.**  If the frontier of the level's removed set
is sliced in general position by the surface and the knot meets it in fewer than `min p q` points
(Pardon's Lemma 2 in the weak-cleaning vocabulary
`Work.EpsW.trace_inessential_of_slicing_of_countsWd`), then no essential loop of the surface lies in
that frontier. -/
theorem not_containsEssentialLoop_frontier_of_counts
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    (Sl : Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
        (frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))
    (hcount : Set.encard (Set.range K.curve ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞)) :
    ¬ (Work.Drive.EpsSphere.torusOf ψ).ContainsEssentialLoop
        (frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) :=
  Work.EpsW.trace_inessential_of_slicing_of_countsWd p q hp hq hc ψ K himg Sl hcl hcount

/-- **(P1) at one level, with the crossing conditions and the count as explicit hypotheses.** -/
theorem traceCurvesAt_of_isLocallyEuclidean_of_counts
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    (hcomp : IsCompact ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))
    (hloc : Work.Smooth.OneManifold.IsLocallyEuclidean
      ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))
    (Sl : Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
        (frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))
    (hcount : Set.encard (Set.range K.curve ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞)) :
    TraceCurvesAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam :=
  traceCurvesAt_of_isLocallyEuclidean hcomp hloc
    (not_containsEssentialLoop_frontier_of_counts
      p q hp hq hc ψ K himg hcl Sl hcount)

/-- **The windowed trace data from the geometric hypotheses of the design.**  If at every
non-exceptional level of the window the trace of the level is compact and locally Euclidean and the
frontier of the level's removed set carries no essential loop, if clause 2 (`AboveGenericAt`) holds
there, and if clause 4 (`NoJumpBelowAt`) holds at the exceptional levels, then
`TiltedTraceDataW` holds — i.e. the whole content of the residual is the choice of the data together
with those four geometric conditions. -/
theorem tiltedTraceDataW_of_geometric_hypotheses
    (hc1 : ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
      IsCompact (P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) ∧
      ¬ P.ContainsEssentialLoop (frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))
    (hc2 : ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
      AboveGenericAt P s c σ u v h ℓ lam)
    (hc4 : ∀ lam ∈ Set.Icc lam0 lam1, lam ∈ (exc : Set ℝ) →
      NoJumpBelowAt P s c σ u v h ℓ lam) :
    TiltedTraceDataW P s c σ u v h ℓ exc lam0 lam1 :=
  ⟨fun lam hlam hne => traceCurvesAt_of_isLocallyEuclidean (hc1 lam hlam hne).1
      (hc1 lam hlam hne).2.1 (hc1 lam hlam hne).2.2,
   hc2, hc4⟩




/-! ## Slicings of a disjoint union of spheres -/

/-- A rank function on the disjoint union of the two index types, used to assemble a slicing of a
disjoint union of spheres: the ranks of the first part dominate those of the second, so that the
nesting conditions of the two parts do not interact. -/
def sphereRank {S₁ S₂ : Set R3} (Sl₁ : Work.InnermostDisk.SphereSlicing P S₁)
    (Sl₂ : Work.InnermostDisk.SphereSlicing P S₂) (i : Sl₁.ι ⊕ Sl₂.ι) : ℕ :=
  match i with
  | Sum.inl a => 2 * Sl₁.rank a + 1
  | Sum.inr b => 2 * Sl₂.rank b

@[simp] theorem sphereRank_inl {S₁ S₂ : Set R3}
    (Sl₁ : Work.InnermostDisk.SphereSlicing P S₁) (Sl₂ : Work.InnermostDisk.SphereSlicing P S₂)
    (a : Sl₁.ι) : sphereRank Sl₁ Sl₂ (Sum.inl a) = 2 * Sl₁.rank a + 1 := rfl

@[simp] theorem sphereRank_inr {S₁ S₂ : Set R3}
    (Sl₁ : Work.InnermostDisk.SphereSlicing P S₁) (Sl₂ : Work.InnermostDisk.SphereSlicing P S₂)
    (b : Sl₂.ι) : sphereRank Sl₁ Sl₂ (Sum.inr b) = 2 * Sl₂.rank b := rfl

/-- **A slicing of a disjoint union of two separated spheres, from slicings of the pieces.**

`Work.InnermostDisk.sphereSlicing_of_isEmbeddedSphere_of_traceCurves` produces a slicing of a *single*
embedded sphere; the level frontier of the tilted sweep is only a disjoint union of such spheres (above
the `ℓ`-range of the box, the box minus the slab has two components, each a half-box with a spherical
frontier).  This lemma assembles a slicing of the union from slicings of the two parts: the components
of the two slicings are put side by side, and because the two parts are closed and disjoint, the range
of a closed curve contained in the union lies in one of them.

This is the "disjoint-union-of-spheres version" of the slicing input which the design of the tilted
sweep records as missing. -/
def sphereSlicing_union {S₁ S₂ : Set R3}
    (Sl₁ : Work.InnermostDisk.SphereSlicing P S₁) (Sl₂ : Work.InnermostDisk.SphereSlicing P S₂)
    (hc₁ : IsClosed S₁) (hc₂ : IsClosed S₂) (hdisj : Disjoint S₁ S₂) :
    Work.InnermostDisk.SphereSlicing P (S₁ ∪ S₂) where
  ι := Sl₁.ι ⊕ Sl₂.ι
  fintype := inferInstance
  c := fun i => match i with
    | Sum.inl a => Sl₁.c a
    | Sum.inr b => Sl₂.c b
  simple := by
    rintro (a | b)
    · exact Sl₁.simple a
    · exact Sl₂.simple b
  disjoint := by
    intro i j hij
    rcases i with a | b <;> rcases j with a' | b'
    · exact Sl₁.disjoint (fun h => hij (by rw [h]))
    · exact hdisj.mono (fun w ⟨t, ht⟩ => ht ▸ Sl₁.mem a t) (fun w ⟨t, ht⟩ => ht ▸ Sl₂.mem b' t)
    · exact hdisj.symm.mono (fun w ⟨t, ht⟩ => ht ▸ Sl₂.mem b t)
        (fun w ⟨t, ht⟩ => ht ▸ Sl₁.mem a' t)
    · exact Sl₂.disjoint (fun h => hij (by rw [h]))
  mem := by
    rintro (a | b) t
    · exact Or.inl (Sl₁.mem a t)
    · exact Or.inr (Sl₂.mem b t)
  covers := by
    intro γ hγ
    have hpre : IsPreconnected (Set.range γ.γ) := isPreconnected_range γ.cont
    have hsub : Set.range γ.γ ⊆ S₁ ∪ S₂ := fun z ⟨t, ht⟩ => ht ▸ hγ t
    have hinter : Set.range γ.γ ∩ (S₁ ∩ S₂) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨-, hz⟩
      exact (Set.disjoint_left.mp hdisj) hz.1 hz.2
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hpre S₁ S₂ hc₁ hc₂ hsub hinter) with
      h | h
    · obtain ⟨a, ha⟩ := Sl₁.covers γ (fun t => h ⟨t, rfl⟩)
      exact ⟨Sum.inl a, ha⟩
    · obtain ⟨b, hb⟩ := Sl₂.covers γ (fun t => h ⟨t, rfl⟩)
      exact ⟨Sum.inr b, hb⟩
  disc := fun i => match i with
    | Sum.inl a => Sl₁.disc a
    | Sum.inr b => Sl₂.disc b
  disc_inj := by
    rintro (a | b)
    · exact Sl₁.disc_inj a
    · exact Sl₂.disc_inj b
  disc_boundary := by
    rintro (a | b) θ
    · exact Sl₁.disc_boundary a θ
    · exact Sl₂.disc_boundary b θ
  disc_mem := by
    rintro (a | b) z
    · exact Or.inl (Sl₁.disc_mem a z)
    · exact Or.inr (Sl₂.disc_mem b z)
  rank := sphereRank Sl₁ Sl₂
  inside := by
    intro i j hij
    rcases i with a | b <;> rcases j with a' | b'
    · have h : Sl₁.rank a' < Sl₁.rank a := Sl₁.inside a a' hij
      simp only [sphereRank_inl]
      omega
    · exfalso
      obtain ⟨z, -, hzr⟩ := hij
      obtain ⟨s, hs⟩ := hzr
      exact (Set.disjoint_left.mp hdisj) (Sl₁.disc_mem a z) (hs ▸ Sl₂.mem b' s)
    · exfalso
      obtain ⟨z, -, hzr⟩ := hij
      obtain ⟨s, hs⟩ := hzr
      exact (Set.disjoint_left.mp hdisj) (hs ▸ Sl₁.mem a' s) (Sl₂.disc_mem b z)
    · have h : Sl₂.rank b' < Sl₂.rank b := Sl₂.inside b b' hij
      simp only [sphereRank_inr]
      omega
  inside_subset := by
    intro i j hij
    rcases i with a | b <;> rcases j with a' | b'
    · exact Sl₁.inside_subset a a' hij
    · exfalso
      obtain ⟨z, -, hzr⟩ := hij
      obtain ⟨s, hs⟩ := hzr
      exact (Set.disjoint_left.mp hdisj) (Sl₁.disc_mem a z) (hs ▸ Sl₂.mem b' s)
    · exfalso
      obtain ⟨z, -, hzr⟩ := hij
      obtain ⟨s, hs⟩ := hzr
      exact (Set.disjoint_left.mp hdisj) (hs ▸ Sl₁.mem a' s) (Sl₂.disc_mem b z)
    · exact Sl₂.inside_subset b b' hij
  covers_interior := by
    rintro (a | b) z hz hc
    · obtain ⟨j, hj⟩ := Sl₁.covers_interior a z hz hc
      exact ⟨Sum.inl j, hj⟩
    · obtain ⟨j, hj⟩ := Sl₂.covers_interior b z hz hc
      exact ⟨Sum.inr j, hj⟩

/-- **A slicing of a disjoint union of two separated spheres** (the `Nonempty` form used by
`Work.BoxShrink.SlicedSphere`). -/
theorem sphereSlicing_union_nonempty {S₁ S₂ : Set R3}
    (Sl₁ : Work.InnermostDisk.SphereSlicing P S₁) (Sl₂ : Work.InnermostDisk.SphereSlicing P S₂)
    (hc₁ : IsClosed S₁) (hc₂ : IsClosed S₂) (hdisj : Disjoint S₁ S₂) :
    Nonempty (Work.InnermostDisk.SphereSlicing P (S₁ ∪ S₂)) :=
  ⟨sphereSlicing_union Sl₁ Sl₂ hc₁ hc₂ hdisj⟩


/-! ## The sweep is eventually constant -/

/-- **Above the `ℓ`-range of the box the removed set of the level is the box minus the slab**, hence
independent of the level: `{ℓ < lam} ⊇ PBox s c σ` as soon as `ℓ < lam` holds on the box. -/
theorem tiltedLevelRemoved_eq_sdiff_of_lt (hhigh : ∀ y ∈ Submission.PBox s c σ, ℓ y < lam) :
    tiltedLevelRemoved s c σ u v h ℓ lam = Submission.PBox s c σ \
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h := by
  ext y
  constructor
  · rintro ⟨hyb, hrem⟩
    exact ⟨hyb, fun hslab => hrem ⟨hslab, hhigh y hyb⟩⟩
  · rintro ⟨hyb, hnot⟩
    exact ⟨hyb, fun hcon => hnot hcon.1⟩

/-- **Clause 1 transfers to every level above the `ℓ`-range of the box.**  The removed set is then
`PBox \ slabClosed`, which does not depend on the level, so the trace does not either: one check at any
single level above the range gives clause 1 at all of them. -/
theorem traceCurvesAt_of_lt_transfer {lam' : ℝ}
    (hhigh : ∀ y ∈ Submission.PBox s c σ, ℓ y < lam')
    (hhigh' : ∀ y ∈ Submission.PBox s c σ, ℓ y < lam)
    (hcurves : TraceCurvesAt P s c σ u v h ℓ lam) : TraceCurvesAt P s c σ u v h ℓ lam' := by
  obtain ⟨n, cs, hsimple, hiness, hdisj, hunion⟩ := hcurves
  exact ⟨n, cs, hsimple, hiness, hdisj, by
    rw [hunion, tiltedLevelRemoved_eq_sdiff_of_lt hhigh',
      tiltedLevelRemoved_eq_sdiff_of_lt hhigh]⟩




/-! ## The two caps of the box cut by the slab, and clause 1 above the `ℓ`-range

Above the `ℓ`-range of the box the removed set of a level is `PBox \ slabClosed`, which does not
depend on the level (`tiltedLevelRemoved_eq_sdiff_of_lt`), and its frontier is the union of the
frontiers of the two **caps** `PBox ∩ {⟪v,·⟫ ≥ a + h}` and `PBox ∩ {⟪v,·⟫ ≤ a - h}` — the two halves
of the box cut by the slab.  Each cap is *convex* (a box cut by a half-space), so its frontier is an
embedded sphere (`Work.EpsW.isEmbeddedSphere_levelSet_of_convex`), and a slicing of the two caps
slices the whole frontier (`sphereSlicing_union`).

Consequently clause 1 above the `ℓ`-range follows from the slicings of the two caps, the level count
and the local structure of the trace — with **no genericity of the sweep height at all**, and with
the count that Pardon's two estimates provide (`encard_frontier_tiltedSweptBall_lt_min`, whose
hypotheses do not mention the level).  This is the `λ`-free half of obligation (R); the remaining
half is the intermediate levels, where the *wall* `{ℓ = lam}` meets the box. -/

/-- **Clause 1 above the `ℓ`-range of the box, from the slicings of the two caps.**

Above the `ℓ`-range the removed set is `PBox \ slabClosed`, which does not depend on the level, and
its frontier is the union of the frontiers of the two **caps** `PBox ∩ {⟪v,·⟫ ≥ a ± h}` (the frontier
identity is `Work.Drive.Mono.frontier_PBox_sdiff_slab_eq_caps`, and the disjointness of the two cap
frontiers is `disjoint_frontier_slabCaps`); a slicing of each cap is given and `sphereSlicing_union`
assembles them.  The level count and the local models of the trace then give clause 1 — with **no
genericity of the sweep height at all**. -/
theorem traceCurvesAt_of_lt_of_slicing_caps {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    (hhigh : ∀ y ∈ Submission.PBox s c σ, ℓ y < lam) (hh : 0 < h) (hv : v ≠ 0)
    (Slp : Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
      (frontier (slabCapPlus s c σ (inner ℝ v c + u) h v)))
    (Slm : Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
      (frontier (slabCapMinus s c σ (inner ℝ v c + u) h v)))
    (hcomp : IsCompact ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))
    (hloc : Work.Smooth.OneManifold.IsLocallyEuclidean
      ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))
    (hcount : Set.encard (Set.range K.curve ∩
      frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞)) :
    TraceCurvesAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam := by
  have hrem : tiltedLevelRemoved s c σ u v h ℓ lam = Submission.PBox s c σ \
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h :=
    tiltedLevelRemoved_eq_sdiff_of_lt (s := s) (c := c) (σ := σ) (u := u) (v := v) (h := h)
      (ℓ := ℓ) (lam := lam) hhigh
  have hfr : frontier (Submission.PBox s c σ \
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) =
      frontier (slabCapPlus s c σ (inner ℝ v c + u) h v) ∪
        frontier (slabCapMinus s c σ (inner ℝ v c + u) h v) :=
    frontier_PBox_sdiff_slab_eq_caps s c σ (inner ℝ v c + u) h hh hv
  have hfront_eq : frontier (tiltedLevelRemoved s c σ u v h ℓ lam) =
      frontier (slabCapPlus s c σ (inner ℝ v c + u) h v) ∪
        frontier (slabCapMinus s c σ (inner ℝ v c + u) h v) := by
    rw [hrem]; exact hfr
  refine traceCurvesAt_of_isLocallyEuclidean_of_counts p q hp hq hc ψ K himg hcl hcomp hloc
    ?_ hcount
  rw [hfront_eq]
  exact sphereSlicing_union Slp Slm isClosed_frontier isClosed_frontier
    (disjoint_frontier_slabCaps (s := s) (c := c) (σ := σ) (v := v) hh)

/-- **Clause 1 at every level above the `ℓ`-range of the box.**

This is `traceCurvesAt_of_lt_of_slicing_caps` with the two cap *slicings* no longer assumed: they are
generated from the cap structure (each cap frontier is an embedded sphere,
`isEmbeddedSphere_frontier_slabCaps`) together with the family of trace curves of the level
(`Work.EpsW.exists_family_of_isCompact_of_isLocallyEuclidean`, which needs only the compactness and
the local Euclidean structure of the trace).  The remaining inputs are the local models of the trace
and the level count. -/
theorem traceCurvesAt_at_window_top {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    (hs : 0 < s) (hhigh : ∀ y ∈ Submission.PBox s c σ, ℓ y < lam) (hh : 0 < h) (hv : v ≠ 0)
    (hcut : SlabCutsBox s c σ (inner ℝ v c + u) h v)
    (hcomp : IsCompact ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))
    (hloc : Work.Smooth.OneManifold.IsLocallyEuclidean
      ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))
    (hcount : Set.encard (Set.range K.curve ∩
      frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞)) :
    TraceCurvesAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam := by
  have hfr : frontier (Submission.PBox s c σ \
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) =
      frontier (slabCapPlus s c σ (inner ℝ v c + u) h v) ∪
        frontier (slabCapMinus s c σ (inner ℝ v c + u) h v) :=
    frontier_PBox_sdiff_slab_eq_caps s c σ (inner ℝ v c + u) h hh hv
  have hfr2 : frontier (tiltedLevelRemoved s c σ u v h ℓ lam) =
      frontier (slabCapPlus s c σ (inner ℝ v c + u) h v) ∪
        frontier (slabCapMinus s c σ (inner ℝ v c + u) h v) := by
    rw [tiltedLevelRemoved_eq_sdiff_of_lt (s := s) (c := c) (σ := σ) (u := u) (v := v)
      (h := h) (ℓ := ℓ) (lam := lam) hhigh]
    exact hfr
  have hsph := isEmbeddedSphere_frontier_slabCaps s c σ (inner ℝ v c + u) h hs hh hv hcut
  -- the family of trace curves of the level
  obtain ⟨n, cs, hsimple, hdisj, hZ⟩ :=
    Work.EpsW.exists_family_of_isCompact_of_isLocallyEuclidean
      (P := Work.Drive.EpsSphere.torusOf ψ)
      (Z := (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam))
      Set.inter_subset_left hcomp hloc
  have hcover : (frontier (slabCapPlus s c σ (inner ℝ v c + u) h v) ∪
      frontier (slabCapMinus s c σ (inner ℝ v c + u) h v)) ∩
      (Work.Drive.EpsSphere.torusOf ψ).carrier = ⋃ i, Set.range (cs i).γ := by
    rw [← hfr2, Set.inter_comm]
    exact hZ
  obtain ⟨SlU⟩ := sphereSlicing_union_of_curveFamily (P := Work.Drive.EpsSphere.torusOf ψ)
    hsph.1 hsph.2 isClosed_frontier isClosed_frontier
    (disjoint_frontier_slabCaps (s := s) (c := c) (σ := σ) (v := v) hh) hsimple hdisj hcover
  refine traceCurvesAt_of_isLocallyEuclidean_of_counts p q hp hq hc ψ K himg hcl hcomp hloc
    ?_ hcount
  rw [hfr2]
  exact SlU


/-- **Clause 1 at every level above the `ℓ`-range of the box, from the three counts.**

Combines `traceCurvesAt_at_window_top` with the level count at the top
(`Work.Drive.Mono.encard_frontier_lt_min_at_top`) and the containment of the top frontier in the box
sphere and the two faces (`frontier_sdiff_slab_subset_sphereSet_union_faces`).  The three counts are
the box-sphere count `A` (Pardon's `|∂PBox ∩ β|`), and the two face counts `B` (`|{⟪v,·⟫ = a ± h} ∩ β|`
inside the box) — for `v = e_{σ 2}` these are the *shifted plane* counts of
`Work.Drive.EpsForm.exists_shiftedPlaneCount_of_count`, and `A + 2B ≤ 75d + 2·(75/2)d = 150 d` is
exactly the crux's budget. -/
theorem traceCurvesAt_at_window_top_of_counts {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    {A B : ℕ∞}
    (hs : 0 < s) (hhigh : ∀ y ∈ Submission.PBox s c σ, ℓ y < lam) (hh : 0 < h) (hv : v ≠ 0)
    (hcut : SlabCutsBox s c σ (inner ℝ v c + u) h v)
    (hS : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} ≤ A)
    (hfaceP : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧ K.curve t ∈ facePlanePlus c u h v} ≤ B)
    (hfaceM : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧ K.curve t ∈ facePlaneMinus c u h v} ≤ B)
    (harith : A + 2 * B < (Nat.min p q : ℕ∞))
    (hcomp : IsCompact ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))
    (hloc : Work.Smooth.OneManifold.IsLocallyEuclidean
      ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam))) :
    TraceCurvesAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam :=
  traceCurvesAt_at_window_top (p := p) (q := q) hp hq hc ψ K himg hcl hs hhigh hh hv hcut
    hcomp hloc
    (encard_frontier_lt_min_at_top p q K hs hhigh
      (frontier_sdiff_slab_subset_sphereSet_union_faces (s := s) (c := c) (σ := σ) (u := u)
        (v := v) (h := h) hs hh)
      hS hfaceP hfaceM harith)


/-- **The removed chunk at a level, and the trace of the level.**  The removed set of the level is
`PBox \ C` with `C := PBox ∩ slabClosed ∩ {ℓ < lam}` — the *convex* chunk cut out of the box by the
slab and the wall — so the trace of the level is contained in `∂PBox ∪ ∂C`.  This is the
intermediate-level analogue of the cap decomposition of `frontier_PBox_sdiff_slab_eq_caps`; the
chunk boundary `∂C` is an embedded sphere (`isEmbeddedSphere_frontier_levelChunk`), whose intersection
with the surface is the *level* trace (`carrier ∩ ∂C ⊆ carrier ∩ (faces ∪ wall)`). -/
theorem frontier_tiltedLevelRemoved_subset_frontier_union_chunk {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} :
    frontier (tiltedLevelRemoved s c σ u v h ℓ lam) ⊆
      frontier (Submission.PBox s c σ) ∪
        frontier (Submission.PBox s c σ ∩
          Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
          {y : R3 | ℓ y < lam}) := by
  have hset : Submission.PBox s c σ \
        (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y < lam}) =
      Submission.PBox s c σ \
        (Submission.PBox s c σ ∩ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
          {y : R3 | ℓ y < lam}) := by
    ext y
    constructor
    · rintro ⟨hyb, hrem⟩
      exact ⟨hyb, fun h => hrem ⟨h.1.2, h.2⟩⟩
    · rintro ⟨hyb, hrem⟩
      exact ⟨hyb, fun h => hrem ⟨⟨hyb, h.1⟩, h.2⟩⟩
  refine subset_trans ?_ (Work.Drive.EpsFormSphere.frontier_sdiff_subset (Submission.PBox s c σ)
    (Submission.PBox s c σ ∩ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
      {y : R3 | ℓ y < lam}))
  rw [show tiltedLevelRemoved s c σ u v h ℓ lam = Submission.PBox s c σ \
      (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y < lam}) from rfl,
    hset]

/-! ## The local model of the trace at a point of the level wall -/


/-! ## The local models of the trace at the wall, the slab faces, and compactness

These three lemmas now live in the *lower* module `Submission.Work.Drive.Mono.TraceLocalModels` (the
junction assembly and the deliverable both consume them, and keeping them in a module that does not
import either breaks the import cycle).  They are re-exported here through the import below.
-/


/-! ## Compactness of the trace -/

/- ## (P2) clause 2 at the interior points of the box

The second clause of the trace data asks every point `z` of the surface in the closed box and the
closed slab at the level `lam` to lie in the closure of the level's region or on the level's trace.
At a point of the *open* box this is clause (i) of `Work.Drive.Final.TiltedGenericity`: the level
`lam ∉ exc` is a regular value of the sweep height, so the height takes values strictly above `lam`
arbitrarily close to `z`, and since `z` lies in the closed slab (so any point of the box at a level
above `lam` is in the region `openTiltedSweepRegion … lam`), the region accumulates at `z`.

At a point of the *box sphere* the statement is where the stratified genericity enters: it is false
at a point at which the surface touches the box from the outside at a local maximum of `ℓ`
(`Work.Drive.Mono.NOTES_STATE.md`, the third refutation), so the boundary case is carried as an
explicit hypothesis.  The two lemmas below are the two halves of the reduction. -/

/-- **A `C¹` function on the line with positive derivative at `0` takes values strictly above its
value at `0`, arbitrarily close to `0`.**  Differentiability is used through its slope form
`HasDerivAt.tendsto_slope_zero`. -/
theorem exists_near_gt_of_hasDerivAt {g : ℝ → ℝ} {c : ℝ} (hg : HasDerivAt g c 0) (hc : 0 < c) :
    ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, |t| < ε ∧ g 0 < g t := by
  intro ε hε
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) ({0}ᶜ : Set ℝ), c/2 < t⁻¹ * (g (0 + t) - g 0) := by
    have h := hg.tendsto_slope_zero.eventually (eventually_gt_nhds (show c/2 < c by linarith))
    simpa [smul_eq_mul] using h
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhdsWithin_iff.mp hev
  set t : ℝ := min δ ε / 2 with ht
  have htpos : 0 < t := by
    have h : 0 < min δ ε := lt_min hδpos hε
    rw [ht]; linarith
  have htδ : t < δ := by
    have h : min δ ε ≤ δ := min_le_left _ _
    rw [ht]; linarith
  have htε : t < ε := by
    have h : min δ ε ≤ ε := min_le_right _ _
    rw [ht]; linarith
  have htne : t ≠ 0 := ne_of_gt htpos
  have hmem : t ∈ Metric.ball (0:ℝ) δ ∩ ({0}ᶜ : Set ℝ) := by
    refine ⟨?_, htne⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos]
    exact htδ
  have h1 := hδ hmem
  have h2 : t * (c/2) < g (0+t) - g 0 := by
    have h3 := mul_lt_mul_of_pos_left h1 htpos
    rw [← mul_assoc, mul_inv_cancel₀ htne, one_mul] at h3
    exact h3
  refine ⟨t, by rw [abs_of_pos htpos]; exact htε, ?_⟩
  simp only [zero_add] at h2
  linarith [mul_pos htpos (by linarith : (0:ℝ) < c/2)]

/-- **A `C¹` function of two variables with non-vanishing derivative at `p` takes values strictly
above its value at `p`, arbitrarily close to `p`.**  Proof: a direction `w` of positive derivative
is chosen (through a nonzero value of the differential), and the one-variable function
`t ↦ F (p + t·w)` is handled by `exists_near_gt_of_hasDerivAt`.  (Named `…_gt_near_…` so
that it does not collide with the copy of the same statement in
`Submission/Work/Drive/Mono/aboveGenericAt_of_junctionGen.lean`, which makes the two modules
importable together.) -/
theorem exists_gt_near_of_fderiv_ne_zero {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hF : HasFDerivAt F (fderiv ℝ F p) p) (hne : fderiv ℝ F p ≠ 0) :
    ∀ ε : ℝ, 0 < ε → ∃ q : ℝ × ℝ, ‖q - p‖ < ε ∧ F p < F q := by
  intro ε hε
  obtain ⟨w, hw⟩ : ∃ w : ℝ × ℝ, fderiv ℝ F p w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (ContinuousLinearMap.ext fun x => by simpa using hcon x)
  set w' : ℝ × ℝ := if 0 < fderiv ℝ F p w then w else -w with hw'def
  have hpos : 0 < fderiv ℝ F p w' := by
    rw [hw'def]
    split_ifs with h
    · exact h
    · have h2 : fderiv ℝ F p w < 0 := lt_of_le_of_ne (le_of_not_gt h) hw
      simpa using neg_pos.mpr h2
  have hw'ne : w' ≠ 0 := fun h0 => hpos.ne' (by rw [h0, map_zero])
  have hwn : 0 < ‖w'‖ := norm_pos_iff.mpr hw'ne
  have hpath : HasDerivAt (fun t : ℝ => p + t • w') w' 0 := by
    have h : HasDerivAt (fun y : ℝ => y • w') ((1:ℝ) • w') 0 :=
      (hasDerivAt_id (0:ℝ)).smul_const w'
    have h'' : HasDerivAt (fun t : ℝ => p + t • w') ((1:ℝ) • w') 0 := h.const_add p
    simpa using h''
  have hF' : HasFDerivAt F (fderiv ℝ F p) (p + (0:ℝ) • w') := by simpa using hF
  have hcomp : HasDerivAt (F ∘ fun t : ℝ => p + t • w') (fderiv ℝ F p w') 0 := by
    have := hF'.comp_hasDerivAt (0:ℝ) hpath
    simpa using this
  obtain ⟨t, htabs, htval⟩ := exists_near_gt_of_hasDerivAt hcomp hpos (ε / (‖w'‖ + 1))
    (div_pos hε (by linarith [norm_nonneg w']))
  refine ⟨p + t • w', ?_, ?_⟩
  · have h1 : ‖(p + t • w') - p‖ = |t| * ‖w'‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    rw [h1]
    have h2 : |t| * ‖w'‖ < (ε / (‖w'‖ + 1)) * ‖w'‖ :=
      mul_lt_mul_of_pos_right htabs hwn
    have h3 : (ε / (‖w'‖ + 1)) * ‖w'‖ ≤ (ε / (‖w'‖ + 1)) * (‖w'‖ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [norm_nonneg w'])
        (le_of_lt (div_pos hε (by linarith [norm_nonneg w'])))
    have h4 : (ε / (‖w'‖ + 1)) * (‖w'‖ + 1) = ε :=
      div_mul_cancel₀ ε (by linarith [norm_nonneg w'])
    linarith [h2, h3, h4.le, h4.ge]
  · have h : (F ∘ fun t : ℝ => p + t • w') t = F (p + t • w') := rfl
    rw [h] at htval
    have h0 : (F ∘ fun t : ℝ => p + t • w') 0 = F p := by simp
    rw [h0] at htval
    exact htval

/-- **(P2), interior case: clause 2 from the genericity of the sweep height.**  At every point `z`
of the surface in the *open* box and the closed slab at a level `lam ∉ exc`, the region
`openTiltedSweepRegion … lam` — which contains every point of the box with `ℓ > lam` — accumulates
at `z`: clause (i) of `Work.Drive.Final.TiltedGenericity` makes the differential of the sweep height
nonzero at every lift of `z`, and a `C¹` function with nonzero differential at `z` takes values above
`lam` arbitrarily close to `z`.

The points of the *box sphere* are not covered here: they are exactly where the stratified
genericity of the data is needed, and they are carried by the hypothesis `hbound` (in the union form
in which clause 2 is stated). -/
theorem aboveGenericAt_of_regular_interior {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam : ℝ}
    (hgen : Work.Drive.Final.TiltedGenericity ψ s c σ u v h ℓ exc) (hne : lam ∉ (exc : Set ℝ))
    (hbound : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∉ Submission.PBox s c σ → z ∈ closure (Submission.PBox s c σ) →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = lam →
      z ∈ closure (Work.Drive.EpsFormSphere.openTiltedSweepRegion
            (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) ∪
          ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
            frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))) :
    Work.Drive.Mono.AboveGenericAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam := by
  intro z hzc hzcl hslab hzl
  by_cases hzb : z ∈ Submission.PBox s c σ
  · refine Or.inl (Metric.mem_closure_iff.mpr ?_)
    obtain ⟨p₀, hp₀⟩ : ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = z := hzc
    have hreg : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p₀ ≠ 0 := by
      refine hgen.1 lam hne p₀ ?_ ?_ ?_
      · rw [Work.BoxShrink.Pinch.par_def, hp₀]; exact hzb
      · rw [Work.BoxShrink.Pinch.par_def, hp₀]; exact hslab
      · rw [Work.BoxShrink.Pinch.par_def, hp₀]; exact hzl
    have hsw : ContDiff ℝ 1 (Work.Drive.EpsForm.sweepHeight ψ ℓ) :=
      Work.Smooth.Morse.pullback_contDiff_one ψ
        (ℓ.contDiff : ContDiff ℝ 1 (fun y : R3 => ℓ y))
    have hF : HasFDerivAt (Work.Drive.EpsForm.sweepHeight ψ ℓ)
        (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p₀) p₀ :=
      (hsw.contDiffAt.differentiableAt one_ne_zero).hasFDerivAt
    have hswv : Work.Drive.EpsForm.sweepHeight ψ ℓ p₀ = lam := by
      show ℓ (Work.Smooth.Morse.param ψ p₀) = lam
      rw [hp₀]; exact hzl
    have hboxopen : IsOpen (Submission.PBox s c σ) :=
      Work.Topology.SphereSlicing.isOpen_PBox s c σ
    obtain ⟨ρ, hρpos, hρ⟩ := Metric.isOpen_iff.mp hboxopen z hzb
    have hcont : ContinuousAt (Work.Smooth.Morse.param ψ) p₀ :=
      (Work.Smooth.Morse.param_continuous ψ).continuousAt
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont (min ε ρ) (lt_min hε hρpos)
    obtain ⟨q, hq, hqval⟩ := exists_gt_near_of_fderiv_ne_zero hF hreg δ hδpos
    have hdistz : dist (Work.Smooth.Morse.param ψ q) z < min ε ρ := by
      have h1 : dist (Work.Smooth.Morse.param ψ q) (Work.Smooth.Morse.param ψ p₀) <
          min ε ρ := hδ (by simpa [dist_eq_norm] using hq)
      rwa [hp₀] at h1
    refine ⟨Work.Smooth.Morse.param ψ q, ?_, ?_⟩
    · refine ⟨Work.Smooth.Morse.param_mem ψ q, ?_, ?_⟩
      · exact hρ (Metric.mem_ball.mpr (lt_of_lt_of_le hdistz (min_le_right _ _)))
      · intro hcon
        have hl : lam < ℓ (Work.Smooth.Morse.param ψ q) := by
          have h1 := hqval
          rw [hswv] at h1
          show lam < ℓ (Work.Smooth.Morse.param ψ q)
          exact h1
        exact absurd hcon.2 (not_le.mpr hl)
    · rw [dist_comm]
      exact lt_of_lt_of_le hdistz (min_le_left _ _)
  · exact hbound z hzc hzb hzcl hslab hzl

/- ## (P1)(a)+(b) packaging: the local models and the family of curves

The two lemmas below are the interface between the *local* structure of the trace (the pointwise
local models `WallFaceJunction_holds`, `IsLocallyEuclidean_trace_spherePoint_holds`, the two models
of this file, and the three junction models) and clause 1 of the trace data:

* `isLocallyEuclidean_trace_of_local_models`: a pointwise local model for every point of the trace
  gives the trace locally Euclidean of dimension one
  (`Work.EpsW.isLocallyEuclidean_of_forall_local`);
* `traceCurvesAt_of_local_models`: together with compactness
  (`isCompact_trace_torusOf`) and the inessentiality of the frontier (Pardon's Lemma 2), the
  pointwise local models give clause 1 (`traceCurvesAt_of_isLocallyEuclidean`). -/

/-- **The trace is locally Euclidean from pointwise local models.** -/
theorem isLocallyEuclidean_trace_of_local_models {P : Work.CoreTopology.ParamTorus} {s u : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    (H : ∀ z : R3,
      z ∈ P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) →
      ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
        Work.Smooth.OneManifold.IsLocallyEuclidean
          (O ∩ (P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))) :
    Work.Smooth.OneManifold.IsLocallyEuclidean
      (P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) :=
  Work.EpsW.isLocallyEuclidean_of_forall_local (fun x => H x x.2)

/-- **(P1)(a)+(b): clause 1 from the pointwise local models, compactness and the
inessentiality.** -/
theorem traceCurvesAt_of_local_models {P : Work.CoreTopology.ParamTorus} {s u : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    (hcomp : IsCompact (P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))
    (H : ∀ z : R3,
      z ∈ P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) →
      ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
        Work.Smooth.OneManifold.IsLocallyEuclidean
          (O ∩ (P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam))))
    (hnoess : ¬ P.ContainsEssentialLoop
      (frontier (tiltedLevelRemoved s c σ u v h ℓ lam))) :
    TraceCurvesAt P s c σ u v h ℓ lam :=
  traceCurvesAt_of_isLocallyEuclidean hcomp (isLocallyEuclidean_trace_of_local_models H) hnoess

/- ## Clause 4 is *vacuous* as soon as an essential loop avoids the closed slab

The fourth clause of the trace data (`NoJumpBelowAt` at the exceptional levels) is Pardon's
`2`-surgery count.  The observation recorded here is that it is needed *only* to rule out a sweep
whose region loses the essential loop inside the window: as soon as the region of *some* level of
the window carries an essential loop, every level does (the regions are nested), hence the hypothesis
`W (region lam) = ⊥` of `NoJumpBelowAt` is false at every level and the clause is vacuous.

The easiest way to make it vacuous is to produce an essential loop of the surface which lies in the
box and *avoids the closed slab*: the region of the sweep contains every point of the box outside the
closed slab, whatever the level.  For a tilt `v` close to `e_{σ 2}` and a half-width `h` of the order
of half the distance of the loop from the cutting plane, the size condition `‖v - e_{σ 2}‖ R < h`
holds and the loop avoids the closed slab — so for such data clause 4 costs nothing, and the whole
content of the residual moves to clauses 1 and 2.  (This is exactly the situation supplied by the
*crux*: `Work.Drive.Final.cruxCoreWd_of_noEquator_regular` produces an essential loop of the box
avoiding the cutting plane at a positive distance, so at configurations whose cutting plane misses
the box sphere the residual needs no counting at the exceptional levels.) -/

/-- **A point of the surface in the box outside the closed slab is in the level's region**, at every
level: the region is the part of the box either outside the closed slab or above the level. -/
theorem mem_openTiltedSweepRegion_of_not_mem_slab {P : Work.CoreTopology.ParamTorus} {y : R3}
    (hyc : y ∈ P.carrier) (hyb : y ∈ Submission.PBox s c σ)
    (hout : y ∉ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) :
    y ∈ Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam :=
  ⟨hyc, hyb, fun hcon => hout hcon.1⟩

/-- **An essential loop of the surface in the box avoiding the closed slab keeps the span of every
level of the sweep nonzero.** -/
theorem windingSpan_ne_bot_of_essentialLoop_sdiff_slab {P : Work.CoreTopology.ParamTorus}
    (γ : Work.CoreTopology.ClosedCurve P) (hess : Work.CoreTopology.IsEssential P γ)
    (hmem : ∀ t : ℝ, γ t ∈ Submission.PBox s c σ)
    (hout : ∀ t : ℝ, γ t ∉ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) :
    ∀ lam : ℝ, Work.SurgeryInvariance.WindingSpan P
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam) ≠ ⊥ := by
  intro lam hbot
  have hsub : Set.range γ.γ ⊆
      Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam :=
    fun z ⟨t, ht⟩ => ht ▸ mem_openTiltedSweepRegion_of_not_mem_slab (γ.mem t) (hmem t) (hout t)
  have h1 : Work.SurgeryInvariance.WindingSpan P (Set.range γ.γ) ≤
      Work.SurgeryInvariance.WindingSpan P
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam) :=
    Work.SurgeryInvariance.WindingSpan_mono P hsub
  rw [hbot] at h1
  have h2 : Work.SurgeryInvariance.WindingSpan P (Set.range γ.γ) ≠ ⊥ :=
    (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr ⟨γ, hess, fun t => ⟨t, rfl⟩⟩
  exact h2 (le_bot_iff.mp h1)

/-- **Clause 4 is vacuous when no level of the window has vanishing span.** -/
theorem noJumpBelowAt_of_windingSpan_ne_bot {P : Work.CoreTopology.ParamTorus}
    (hnb : ∀ lam : ℝ, Work.SurgeryInvariance.WindingSpan P
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam) ≠ ⊥) :
    NoJumpBelowAt P s c σ u v h ℓ lam :=
  fun hbot => absurd hbot (hnb lam)

/-- **Clause 4 is free as soon as the span is constant on a left-neighbourhood of the level.**

`NoJumpBelowAt lam` asks that no level just below `lam` carry the full span when the span at `lam`
vanishes.  If the span of the level region is *constant* on `[mu0, lam)` then the vanishing at `lam`
propagates, so the hypothesis is false at every `mu ∈ [mu0, lam)` and the clause holds.  This is the
form in which clause 4 is discharged for data whose level regions are the members of a
`Work.SurgeryInvariance.Sweep` (Pardon's family of spheres with finitely many `2`-surgeries, along
which the *whole* span is constant by `Work.SurgeryInvariance.Sweep.windingSpan_eq`): there the
constancy is not a local but a global property, and clause 4 costs nothing. -/
theorem noJumpBelowAt_of_span_const {P : Work.CoreTopology.ParamTorus} {mu0 : ℝ} (hmu0 : mu0 < lam)
    (hconst : ∀ mu ∈ Set.Ico mu0 lam,
      Work.SurgeryInvariance.WindingSpan P
          (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ mu) =
        Work.SurgeryInvariance.WindingSpan P
          (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam)) :
    NoJumpBelowAt P s c σ u v h ℓ lam := by
  intro hbot
  refine ⟨mu0, hmu0, fun mu hmu => ?_⟩
  rw [hconst mu hmu, hbot]
  exact fun hcon => by
    have h1 : ((1 : ℚ × ℚ)) ∈ (⊥ : Submodule ℚ (ℚ × ℚ)) := hcon ▸ Submodule.mem_top
    simpa using h1

/-- **Clause 4 is free when the exceptional levels carry no vanishing span at all.**  (The
trivial case: the hypothesis of `NoJumpBelowAt` is simply false.) -/
theorem noJumpBelowAt_of_span_ne_bot
    (hne : Work.SurgeryInvariance.WindingSpan P
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam) ≠ ⊥) :
    NoJumpBelowAt P s c σ u v h ℓ lam :=
  fun hbot => absurd hbot hne

/-- **A point of the box strictly below the cutting plane by `d`, and close enough to it relative to
the tilt, lies outside the closed tilted slab.**  This is the tilt estimate in the direction needed
here: `⟪v, y - c⟫ - u` differs from `y (σ 2) - c (σ 2) - u` by at most
`‖v - shiftVσ σ 1‖ · ‖y - c‖ ≤ ‖v - shiftVσ σ 1‖ · R`, so if the gap `d` exceeds
`‖v - shiftVσ σ 1‖ · R + h` the point is at distance more than `h` from the tilted plane. -/
theorem not_mem_tiltedSlabClosed_of_coord_lt {y : R3} {d R h : ℝ}
    (hgap : y (σ 2) < c (σ 2) + u - d) (hR : ‖y - c‖ ≤ R)
    (hd : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R + h < d) :
    y ∉ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h := by
  intro hmem
  have hbig : |inner ℝ v (y - c) - u| ≤ h := by
    have h2 : inner ℝ v y - (inner ℝ v c + u) = inner ℝ v (y - c) - u := by
      rw [inner_sub_right]; ring
    rw [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_setOf_eq, h2] at hmem
    exact hmem
  set e : R3 := Work.BoxShrink.shiftVσ σ 1 with he
  have hcoord : inner ℝ e (y - c) = y (σ 2) - c (σ 2) := by
    rw [he, Work.BoxShrink.shiftVσ]
    simp [PiLp.inner_apply, Real.inner_apply]
  have hsplit : inner ℝ v (y - c) - u = (y (σ 2) - c (σ 2) - u) + inner ℝ (v - e) (y - c) := by
    rw [inner_sub_left, hcoord]; ring
  have hCS : |inner ℝ (v - e) (y - c)| ≤ ‖v - e‖ * ‖y - c‖ := abs_real_inner_le_norm _ _
  have hmono : ‖v - e‖ * ‖y - c‖ ≤ ‖v - e‖ * R := mul_le_mul_of_nonneg_left hR (norm_nonneg _)
  have hlt : inner ℝ v (y - c) - u < -h := by
    have h2 : inner ℝ (v - e) (y - c) ≤ ‖v - e‖ * R := le_trans (le_abs_self _) (le_trans hCS hmono)
    have h3 : y (σ 2) - c (σ 2) - u < -d := by linarith
    rw [hsplit]; linarith
  have h4 := (abs_le.mp hbig).1
  linarith

/-- **The half-width at which clause 4 costs nothing.**  If an essential loop of the surface in the
box stays at distance at least `d > 0` *below* the cutting plane, then for every unit tilt `v` with
`‖v - shiftVσ σ 1‖ · R ≤ d / 4` there is a half-width `h` (of the order `d/2`) with the size
condition `‖v - shiftVσ σ 1‖ * R < h` for which the span of *every* level of the sweep is nonzero —
so that clause 4 (`NoJumpBelowAt`) is vacuous at every level of every window, for every functional
`ℓ` and every exceptional set. -/
theorem exists_h_of_windingSpan_ne_bot {P : Work.CoreTopology.ParamTorus}
    (γ : Work.CoreTopology.ClosedCurve P) (hess : Work.CoreTopology.IsEssential P γ)
    (hmem : ∀ t : ℝ, γ t ∈ Submission.PBox s c σ) {d R : ℝ} (hd : 0 < d)
    (hgap : ∀ t : ℝ, γ t (σ 2) < c (σ 2) + u - d)
    (hRbox : ∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R)
    (hclose : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R ≤ d / 4) :
    ∃ h : ℝ, ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R < h ∧ 0 < h ∧ h < d ∧
      ∀ lam : ℝ, Work.SurgeryInvariance.WindingSpan P
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam) ≠ ⊥ := by
  refine ⟨d / 2, by linarith, by linarith, by linarith, ?_⟩
  intro lam
  refine windingSpan_ne_bot_of_essentialLoop_sdiff_slab (s := s) (c := c) (σ := σ) (u := u)
    (v := v) (ℓ := ℓ) (h := d / 2) (lam := lam) γ hess hmem (fun t => ?_)
  exact not_mem_tiltedSlabClosed_of_coord_lt (c := c) (σ := σ) (u := u) (v := v)
    (h := d / 2) (hgap t) (hRbox _ (hmem t)) (by linarith)

/-- **The trace data from clauses 1 and 2 alone, when no level has vanishing span.**  This is the
form in which the residual is proved at the configurations of the crux at which an essential loop of
the box avoids the cutting plane (`Work.Drive.Final.cruxCoreWd_of_noEquator_regular`): clause 4 is
then vacuous and the whole content of the trace data is clauses 1 and 2. -/
theorem tiltedTraceDataW_of_clauses_and_loop {P : Work.CoreTopology.ParamTorus}
    (hc1 : ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) → TraceCurvesAt P s c σ u v h ℓ lam)
    (hc2 : ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) → AboveGenericAt P s c σ u v h ℓ lam)
    (hloop : ∀ lam : ℝ, Work.SurgeryInvariance.WindingSpan P
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam) ≠ ⊥) :
    TiltedTraceDataW P s c σ u v h ℓ exc lam0 lam1 :=
  ⟨hc1, hc2, fun lam _ _ => noJumpBelowAt_of_windingSpan_ne_bot hloop⟩

/-- **The trace data from clauses 1 and 2 alone, given an essential loop of the box avoiding the
closed slab** (the form supplied by the crux at a configuration whose cutting plane misses the box
sphere, with the half-width `exists_h_of_windingSpan_ne_bot`). -/
theorem tiltedTraceDataW_of_clauses_of_essentialLoop_sdiff_slab {P : Work.CoreTopology.ParamTorus}
    (hc1 : ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) → TraceCurvesAt P s c σ u v h ℓ lam)
    (hc2 : ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) → AboveGenericAt P s c σ u v h ℓ lam)
    (γ : Work.CoreTopology.ClosedCurve P) (hess : Work.CoreTopology.IsEssential P γ)
    (hmem : ∀ t : ℝ, γ t ∈ Submission.PBox s c σ)
    (hout : ∀ t : ℝ, γ t ∉ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) :
    TiltedTraceDataW P s c σ u v h ℓ exc lam0 lam1 :=
  tiltedTraceDataW_of_clauses_and_loop hc1 hc2
    (windingSpan_ne_bot_of_essentialLoop_sdiff_slab γ hess hmem hout)

/-- **(P2), boundary case: clause 2 from the absence of a local maximiser of the level function on
the box sphere.**  At a point `z` of the surface on the box sphere at the level `lam ∉ exc`, if the
surface enters the box near `z` at levels strictly above `lam` (the hypothesis `hnotmax`, the
negation of "`z` is a local maximiser of `ℓ` on the surface's part of the closed box"), then `z` is a
limit of points of the level's region, because every point of the box with `ℓ > lam` is in the region
whatever its slab status.

The hypothesis is *not* automatic: at a point at which the surface touches the box sphere from the
outside at a local maximum of `ℓ` (and the box lies in the closed slab below the level) neither
alternative of clause 2 holds (`NOTES_STATE.md`, the third refutation).  Those points are finitely
many for a generic `ℓ`, and their levels must be put into `exc` by the data-choice step — the
stratified genericity of the tilt data. -/
theorem aboveGenericAt_of_no_localMax {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam : ℝ}
    (hgen : Work.Drive.Final.TiltedGenericity ψ s c σ u v h ℓ exc) (hne : lam ∉ (exc : Set ℝ))
    (hnotmax : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∉ Submission.PBox s c σ → z ∈ closure (Submission.PBox s c σ) →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = lam →
      ∀ ρ : ℝ, 0 < ρ → ∃ y : R3, y ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∧
        y ∈ Submission.PBox s c σ ∧ ‖y - z‖ < ρ ∧ lam < ℓ y) :
    Work.Drive.Mono.AboveGenericAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam :=
  aboveGenericAt_of_regular_interior hgen hne fun z hzc hznb hzcl hslab hzl =>
    Or.inl (Metric.mem_closure_iff.mpr fun ε hε => by
      obtain ⟨y, hyc, hyb, hyd, hyl⟩ := hnotmax z hzc hznb hzcl hslab hzl ε hε
      refine ⟨y, ⟨hyc, hyb, fun hcon => absurd hcon.2 (not_le.mpr hyl)⟩, ?_⟩
      rw [dist_comm]; exact hyd)


/-! ## (P1) assembly: clause 1 from the local models, the sphere-ness of the level's frontier and
the level count

The local models of the trace (the interior, wall, slab-face and box-sphere point types, the four
junction types, assembled as `Work.Drive.Mono.trace_locallyEuclidean_of_junctionGen` from the
stratified genericity `Work.Drive.Mono.JunctionGen`) give the trace as a compact locally Euclidean
`1`-dimensional subset of the surface; the classification of such subsets
(`Work.EpsW.exists_family_of_isCompact_of_isLocallyEuclidean`) decomposes it into finitely many
pairwise disjoint simple closed curves; the *sphere-ness* of the level's frontier
(`Work.InnermostDisk.IsEmbeddedSphere`, `Work.InnermostDisk.sphereSlicing_of_isEmbeddedSphere_of_traceCurves`)
turns that decomposition into a `SphereSlicing`; and Pardon's Lemma 2 at the level count makes every
one of those curves inessential.

The lemma below performs that composition at one level, with the local models, the sphere-ness and
the count as explicit hypotheses (the first two are supplied at `TiltData` + `JunctionGen` data by
`Work.Drive.Mono.trace_locallyEuclidean_of_junctionGen` and the geometry of the sweep; the third by
`Work.Drive.EpsFormSphere.encard_frontier_tiltedSweptBall_lt_min`). -/

/-- **(P1) at one level, from the local models, the sphere-ness and the count.** -/
theorem traceCurvesAt_of_local_models_of_isEmbeddedSphere {ψ : Submission.Diffeo} {s u : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    (H : ∀ z : R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam) →
      ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
        Work.Smooth.OneManifold.IsLocallyEuclidean
          (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
            frontier (tiltedLevelRemoved s c σ u v h ℓ lam))))
    (hsphere : Work.InnermostDisk.IsEmbeddedSphere
      (frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    (hcount : Set.encard (Set.range K.curve ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞)) :
    TraceCurvesAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam := by
  have hcomp : IsCompact ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) :=
    isCompact_trace_torusOf ψ s u c σ v h ℓ lam
  have hloc : Work.Smooth.OneManifold.IsLocallyEuclidean
      ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) :=
    isLocallyEuclidean_trace_of_local_models H
  obtain ⟨n, γ, hsimple, hdisj, hZ⟩ :=
    Work.EpsW.exists_family_of_isCompact_of_isLocallyEuclidean
      (P := Work.Drive.EpsSphere.torusOf ψ)
      (Z := (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam))
      Set.inter_subset_left hcomp hloc
  have hcover : frontier (tiltedLevelRemoved s c σ u v h ℓ lam) ∩
      (Work.Drive.EpsSphere.torusOf ψ).carrier = ⋃ i, Set.range (γ i).γ := by
    rw [Set.inter_comm, hZ]
  obtain ⟨Sl⟩ := Work.InnermostDisk.sphereSlicing_of_isEmbeddedSphere_of_traceCurves
    hsphere n γ hsimple hdisj hcover
  exact traceCurvesAt_of_local_models hcomp H
    (not_containsEssentialLoop_frontier_of_counts p q hp hq hc ψ K himg hcl Sl hcount)

/-! ## The trace data from the three clauses, and the residual from the inputs

The split `TiltedTraceDataW` is a plain conjunction of the three clauses, and the residual
`TiltedTraceDataWExists` is the existential quantification of `TiltData` and `TiltedTraceDataW` over
the data.  Both directions are recorded here explicitly so that the *exact* remaining obligation of
the residual is visible: the geometric inputs of `TraceDataInputs` below (the data, the local models
of the trace, the sphere-ness of the level's frontier, the level count, clause 2 and clause 4). -/

/-- **The trace data from its three clauses.** -/
theorem tiltedTraceDataW_of_clauses {P : Work.CoreTopology.ParamTorus} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ}
    (hc1 : ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
      TraceCurvesAt P s c σ u v h ℓ lam)
    (hc2 : ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
      AboveGenericAt P s c σ u v h ℓ lam)
    (hc4 : ∀ lam ∈ Set.Icc lam0 lam1, lam ∈ (exc : Set ℝ) →
      NoJumpBelowAt P s c σ u v h ℓ lam) :
    TiltedTraceDataW P s c σ u v h ℓ exc lam0 lam1 :=
  ⟨hc1, hc2, hc4⟩

/-- **The geometric inputs of the residual at one datum.**  Besides `TiltData`, at every
non-exceptional level of the window: the pointwise local models of the trace, the sphere-ness of the
level's frontier and the level count; clause 2 at every non-exceptional level; and clause 4 at every
exceptional level. -/
def TraceDataInputs (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ) (p q : ℕ) (K : Knot) :
    Prop :=
  TiltData ψ s c σ u v h R ℓ exc lam0 lam1 ∧
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
    (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam) →
      ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
        Work.Smooth.OneManifold.IsLocallyEuclidean
          (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
            frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))) ∧
    Work.InnermostDisk.IsEmbeddedSphere
      (frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) ∧
    Set.encard (Set.range K.curve ∩
      frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞)) ∧
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
    AboveGenericAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) ∧
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∈ (exc : Set ℝ) →
    NoJumpBelowAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam)

/-- **The trace data at a datum satisfying the geometric inputs.** -/
theorem tiltedTraceDataW_of_inputs {p q : ℕ} {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} {K : Knot}
    (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    (hI : TraceDataInputs ψ s c σ u v h R ℓ exc lam0 lam1 p q K) :
    TiltedTraceDataW (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ exc lam0 lam1 :=
  tiltedTraceDataW_of_clauses
    (fun lam hlam hne => traceCurvesAt_of_local_models_of_isEmbeddedSphere
      (hI.2.1 lam hlam hne).1 (hI.2.1 lam hlam hne).2.1 p q hp hq hc K himg hcl
      (hI.2.1 lam hlam hne).2.2)
    (fun lam hlam hne => hI.2.2.1 lam hlam hne)
    (fun lam hlam he => hI.2.2.2 lam hlam he)

/-- **The geometric inputs of the residual, in the lean form.**

This is `TraceDataInputs` with two changes, both of them strict weakenings:

* the pointwise **local models** of the trace are *dropped*: clause 1 follows from a
  `Work.InnermostDisk.SphereSlicing` of the level's frontier alone
  (`traceCurvesAt_of_slicing`), the slicing being exactly the family of curves that clause 1 asks
  for;
* the **sphere-ness** `Work.InnermostDisk.IsEmbeddedSphere` of the frontier is *replaced by a
  slicing of it*: `IsEmbeddedSphere` requires a *single* sphere, which the frontier of an arbitrary
  level is not (above the `ell`-range of the box it is a disjoint union of two, and at a corner of
  the wall with the boundary of the box the union-of-spheres statement is `false` — see
  `NOTES_H381_count_decoration.md` §6.1--6.1bis); a slicing is what Pardon's second input actually
  consumes, and slicings of disjoint unions are assembled by `sphereSlicing_union`.

The remaining fields are the level count, clause 2 and clause 4, unchanged. -/
def TraceDataInputsW (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ) (p q : ℕ) (K : Knot) :
    Prop :=
  TiltData ψ s c σ u v h R ℓ exc lam0 lam1 ∧
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
    Nonempty (Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
      (frontier (tiltedLevelRemoved s c σ u v h ℓ lam))) ∧
    Set.encard (Set.range K.curve ∩
      frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞)) ∧
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
    AboveGenericAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) ∧
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∈ (exc : Set ℝ) →
    NoJumpBelowAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam)

/-- **The trace data at a datum satisfying the lean geometric inputs.** -/
theorem tiltedTraceDataW_of_inputsW {p q : ℕ} {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} {K : Knot}
    (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    (hI : TraceDataInputsW ψ s c σ u v h R ℓ exc lam0 lam1 p q K) :
    TiltedTraceDataW (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ exc lam0 lam1 :=
  tiltedTraceDataW_of_clauses
    (fun lam hlam hne => by
      obtain ⟨⟨Sl⟩, hcount⟩ := hI.2.1 lam hlam hne
      exact traceCurvesAt_of_slicing Sl
        (not_containsEssentialLoop_frontier_of_counts p q hp hq hc ψ K himg hcl Sl hcount) rfl)
    (fun lam hlam hne => hI.2.2.1 lam hlam hne)
    (fun lam hlam he => hI.2.2.2 lam hlam he)

/-- **The residual from the geometric inputs**: the deliverable `TiltedTraceDataWExists` follows as
soon as at every crux configuration there are tilt data satisfying `TraceDataInputs`.  This is the
exact form in which the deliverable is attacked: the data choice (the thin slab with the stratified
genericity), the local models (`JunctionGen`), the sphere-ness of the level's frontier, the level
count, and clause 4 are the five remaining obligations. -/
theorem TiltedTraceDataWExists_of_inputs
    (H : ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
      (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (hd : 0 ≤ d),
      Work.Sweep.IsDistortionBound K d →
      Set.range K.curve = Set.range
        (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
          (Work.CoreTopology.standardCurve p q)).γ →
      Submission.countConst * d < (Nat.min p q : ℝ) →
      Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ) →
      ∀ (r : ℝ) (hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
        Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ →
        ∀ (s : ℝ) (hrs : r < s) (hs : s < (1 + Submission.eps) * r),
          Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
              {y : R3 | Submission.boxNorm c σ y = s} →
          ∀ (u : ℝ) (hu : |u| < Submission.eps * r),
            ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
                Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
              ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
            ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
                K.curve t ∈ Submission.PBox s c σ ∧
                (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
              ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
            ∃ (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
              TraceDataInputs ψ s c σ u v h R ℓ exc lam0 lam1 p q K) :
    Work.Drive.Mono.TiltedTraceDataWExists := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  obtain ⟨v, h, R, ℓ, lam0, lam1, exc, hinputs⟩ :=
    H p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  exact ⟨v, h, R, ℓ, lam0, lam1, exc, hinputs.1,
    tiltedTraceDataW_of_inputs hp hq hc himg hcl hinputs⟩


/-- **The residual from the lean geometric inputs**: `TiltedTraceDataWExists` follows as soon as at
every crux configuration there are tilt data satisfying `TraceDataInputsW`.  Compared with
`TiltedTraceDataWExists_of_inputs` this needs neither the local models of the trace nor the
sphere-ness of the level's frontier; the remaining obligation is the *slicing* of the level's
frontier (assembled from its pieces by `sphereSlicing_union`), the level count and clauses 2 and 4. -/
theorem TiltedTraceDataWExists_of_inputsW
    (H : ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
      (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (hd : 0 ≤ d),
      Work.Sweep.IsDistortionBound K d →
      Set.range K.curve = Set.range
        (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
          (Work.CoreTopology.standardCurve p q)).γ →
      Submission.countConst * d < (Nat.min p q : ℝ) →
      Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ) →
      ∀ (r : ℝ) (hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
        Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ →
        ∀ (s : ℝ) (hrs : r < s) (hs : s < (1 + Submission.eps) * r),
          Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
              {y : R3 | Submission.boxNorm c σ y = s} →
          ∀ (u : ℝ) (hu : |u| < Submission.eps * r),
            ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
                Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
              ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
            ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
                K.curve t ∈ Submission.PBox s c σ ∧
                (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
              ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
            ∃ (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
              TraceDataInputsW ψ s c σ u v h R ℓ exc lam0 lam1 p q K) :
    Work.Drive.Mono.TiltedTraceDataWExists := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  obtain ⟨v, h, R, ℓ, lam0, lam1, exc, hinputs⟩ :=
    H p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  exact ⟨v, h, R, ℓ, lam0, lam1, exc, hinputs.1,
    tiltedTraceDataW_of_inputsW hp hq hc himg hcl hinputs⟩


/-- **Clause 2 of the bundle is free given the junction genericity of the data.**

`TraceDataInputsW` carries clause 2 (`AboveGenericAt`) as an opaque hypothesis at every
non-exceptional level of the window.  This lemma *derives* it from the data conditions alone: the
tilt data (`TiltData`) and the stratified genericity of the sweep at the junctions of the trace
(`Work.Drive.Mono.JunctionGen`), through the proved
`Work.Drive.Mono.aboveGenericAt_of_junctionGen` (which uses only clause (i) of `TiltedGenericity` at
the interior points of the box and clause (a) of `JunctionGen` at the box sphere).  So the field is
not an independent obligation: it is part of the choice of the data, together with `TiltData`. -/
theorem traceDataInputsW_of_junctionGen {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} {p q : ℕ} {K : Knot} (hs : 0 < s)
    (hT : TiltData ψ s c σ u v h R ℓ exc lam0 lam1)
    (hJ : JunctionGen ψ s c σ u v h ℓ exc lam0 lam1)
    (hslice : ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
      Nonempty (Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
        (frontier (tiltedLevelRemoved s c σ u v h ℓ lam))) ∧
      Set.encard (Set.range K.curve ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞))
    (h4 : ∀ lam ∈ Set.Icc lam0 lam1, lam ∈ (exc : Set ℝ) →
      NoJumpBelowAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) :
    TraceDataInputsW ψ s c σ u v h R ℓ exc lam0 lam1 p q K :=
  ⟨hT, hslice, fun lam hl hne => aboveGenericAt_of_junctionGen hs hT hJ hl hne, h4⟩

/-- **The residual from the data conditions and the geometry of the level.**

At every crux configuration there are tilt data satisfying `TiltData` **and** `JunctionGen` at which,
at every non-exceptional level of the window, the frontier of the level's removed set admits a
slicing and the knot meets it in fewer than `min p q` points, and clause 4 holds at the exceptional
levels.  The clause 2 part of `TraceDataInputsW` has been discharged into the data conditions. -/
theorem TiltedTraceDataWExists_of_data_of_junctionGen
    (H : ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
      (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (hd : 0 ≤ d),
      Work.Sweep.IsDistortionBound K d →
      Set.range K.curve = Set.range
        (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
          (Work.CoreTopology.standardCurve p q)).γ →
      Submission.countConst * d < (Nat.min p q : ℝ) →
      Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ) →
      ∀ (r : ℝ) (hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
        Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ →
        ∀ (s : ℝ) (hrs : r < s) (hs : s < (1 + Submission.eps) * r),
          Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
              {y : R3 | Submission.boxNorm c σ y = s} →
          ∀ (u : ℝ) (hu : |u| < Submission.eps * r),
            ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
                Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
              ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
            ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
                K.curve t ∈ Submission.PBox s c σ ∧
                (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
              ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
            ∃ (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
              TiltData ψ s c σ u v h R ℓ exc lam0 lam1 ∧
              JunctionGen ψ s c σ u v h ℓ exc lam0 lam1 ∧
              (∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
                Nonempty (Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
                  (frontier (tiltedLevelRemoved s c σ u v h ℓ lam))) ∧
                Set.encard (Set.range K.curve ∩
                  frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞)) ∧
              (∀ lam ∈ Set.Icc lam0 lam1, lam ∈ (exc : Set ℝ) →
                NoJumpBelowAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam)) :
    Work.Drive.Mono.TiltedTraceDataWExists := by
  refine TiltedTraceDataWExists_of_inputsW (fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ
    hbox s hrs hs hslice u hu hS hU => ?_)
  obtain ⟨v, h, R, ℓ, lam0, lam1, exc, hT, hJ, hsl, h4⟩ :=
    H p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  exact ⟨v, h, R, ℓ, lam0, lam1, exc, traceDataInputsW_of_junctionGen (lt_trans hr hrs) hT hJ hsl h4⟩

/-! ## The leanest residual: the trace of every level carries no essential loop

The local models of the trace are *available from the data*: `Work.Drive.Mono.trace_localModels_of_junctionGen`
(`Submission/Work/Drive/Mono/TraceLocalModelsJunction.lean`, the rehomed copy of the assembly, whose
module imports `TraceLocalModels` instead of this file and is therefore importable *by* this file)
derives the pointwise local Euclidean structure of the trace at every point of a non-exceptional level
from the tilt data, the junction genericity and the face regularity.  Hence, by
`Work.Drive.Mono.traceCurvesAt_of_local_models` and the compactness of the trace
(`Work.Drive.Mono.isCompact_trace_torusOf`), clause 1 at a level is *equivalent* to the single
statement that the level's frontier carries no essential loop.  There is no need for a slicing of the
frontier (Pardon's Lemma 2 via the innermost disc), nor for a count at the level: the *whole* content
of clause 1 is the inessentiality. -/

/-- **The inputs of the residual, in the form in which the geometry is attacked**: the data
conditions of the design (the tilt data, the junction genericity and the face regularity), the
inessentiality of the level's frontier at every non-exceptional level of the window, and clause 4 at
the exceptional levels. -/
def TraceDataInputsL (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ) : Prop :=
  TiltData ψ s c σ u v h R ℓ exc lam0 lam1 ∧
  JunctionGen ψ s c σ u v h ℓ exc lam0 lam1 ∧
  (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → z ∈ Submission.PBox s c σ →
    |inner ℝ v z - (inner ℝ v c + u)| = h →
    ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0) ∧
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
    ¬ (Work.Drive.EpsSphere.torusOf ψ).ContainsEssentialLoop
      (frontier (tiltedLevelRemoved s c σ u v h ℓ lam))) ∧
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∈ (exc : Set ℝ) →
    NoJumpBelowAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam)

/-- **The trace data from the lean inputs.** -/
theorem tiltedTraceDataW_of_inputsL {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} (hs : 0 < s)
    (hslice : Nonempty (Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
      {y : R3 | Submission.boxNorm c σ y = s}))
    (hI : TraceDataInputsL ψ s c σ u v h R ℓ exc lam0 lam1) :
    TiltedTraceDataW (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ exc lam0 lam1 :=
  tiltedTraceDataW_of_clauses
    (fun lam hl hne => traceCurvesAt_of_local_models
      (isCompact_trace_torusOf ψ s u c σ v h ℓ lam)
      (trace_localModels_of_junctionGen hs hslice hI.2.2.1 hI.1 hI.2.1 hl hne)
      (hI.2.2.2.1 lam hl hne))
    (fun lam hl hne => aboveGenericAt_of_junctionGen hs hI.1 hI.2.1 hl hne)
    (fun lam hl he => hI.2.2.2.2 lam hl he)

/-- **A loop homotopic in the surface to a loop of a region of vanishing span is inessential.**

This is the abstract core of the *geometric* route to clause 1 (§4(ii) of
`NOTES_H381L520_state.md`): the trace curves of a level of the tilted sweep are geometrically
homotopic to loops of the "thick flat slice" `carrier ∩ PBox ∩ tiltedSlabClosed`, and that slice
carries no essential loop — the content, *at the flat slice*, of Pardon's Lemma 2
(`Work.EpsW.sliceSpan_bot_of_sliceArcs` in the arcs case,
`Work.Drive.Final.sliceRegion_not_containsEssentialLoop_of_counts_of_regular` in the regular one).
No counting at the *level* is needed, only the vanishing of the span of the slice, which is a single
`lam`-independent statement. -/
theorem not_isEssential_of_homotopic_of_mem_of_windingSpan_eq_bot
    {P : Work.CoreTopology.ParamTorus} {S : Set R3}
    (hW : Work.SurgeryInvariance.WindingSpan P S = ⊥)
    {κ κ' : Work.CoreTopology.ClosedCurve P} (hhom : Work.CoreTopology.Homotopic P κ κ')
    (hκ' : ∀ t : ℝ, κ' t ∈ S) :
    ¬ Work.CoreTopology.IsEssential P κ := by
  have hne : ¬ P.ContainsEssentialLoop S :=
    (Work.SurgeryInvariance.WindingSpan_eq_bot_iff P S).mp hW
  have hκ'ne : ¬ Work.CoreTopology.IsEssential P κ' := fun hess => hne ⟨κ', hess, hκ'⟩
  exact Work.InnermostDisk.not_isEssential_of_homotopic hhom hκ'ne

/-- **Clause 1's inessentiality from a homotopy cover by a region of vanishing span.**

If every loop of the level's trace `T` is homotopic in the surface to a loop of a region `S` of
vanishing span, then `T` carries no essential loop.  This is (R) of `NOTES_H381L520_state.md` with
the geometric input separated out: the *only* obligation is "every trace loop is homotopic to a loop
of the flat slice (or of the thick slice)", i.e. the collar/thickening statement — the counting is
spent once, at the slice. -/
theorem not_containsEssentialLoop_of_homotopic_cover {P : Work.CoreTopology.ParamTorus}
    {S T : Set R3} (hW : Work.SurgeryInvariance.WindingSpan P S = ⊥)
    (h : ∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ T) →
      ∃ γ' : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ' t ∈ S) ∧
        Work.CoreTopology.Homotopic P γ γ') :
    ¬ P.ContainsEssentialLoop T := by
  rintro ⟨γ, hess, hγ⟩
  obtain ⟨γ', hγ'S, hhom⟩ := h γ hγ
  exact not_isEssential_of_homotopic_of_mem_of_windingSpan_eq_bot hW hhom hγ'S hess

/-- **The residual from the lean inputs**: `TiltedTraceDataWExists` follows as soon as at every crux
configuration there are data satisfying `TraceDataInputsL`.  The remaining obligation is the
*inessentiality of the trace* at every non-exceptional level — Pardon's Lemma 2 at the level — and
clause 4; the data conditions and the local structure of the trace (clause 1's family of curves,
clause 2) are discharged. -/
theorem TiltedTraceDataWExists_of_inputsL
    (H : ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
      (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (hd : 0 ≤ d),
      Work.Sweep.IsDistortionBound K d →
      Set.range K.curve = Set.range
        (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
          (Work.CoreTopology.standardCurve p q)).γ →
      Submission.countConst * d < (Nat.min p q : ℝ) →
      Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ) →
      ∀ (r : ℝ) (hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
        Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ →
        ∀ (s : ℝ) (hrs : r < s) (hs : s < (1 + Submission.eps) * r),
          Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
              {y : R3 | Submission.boxNorm c σ y = s} →
          ∀ (u : ℝ) (hu : |u| < Submission.eps * r),
            ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
                Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
              ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
            ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
                K.curve t ∈ Submission.PBox s c σ ∧
                (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
              ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
            ∃ (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
              TraceDataInputsL ψ s c σ u v h R ℓ exc lam0 lam1) :
    Work.Drive.Mono.TiltedTraceDataWExists := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  obtain ⟨v, h, R, ℓ, lam0, lam1, exc, hI⟩ :=
    H p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  exact ⟨v, h, R, ℓ, lam0, lam1, exc, hI.1,
    tiltedTraceDataW_of_inputsL (lt_trans hr hrs) hslice hI⟩


/-! ## The level count: the box-sphere part and the in-box part

Pardon's Lemma 2 (`Work.EpsW.trace_inessential_of_slicing_of_countsWd`) needs the level frontier of
the tilted sweep to meet the knot in fewer than `min p q` points.  The frontier is the union of three
pieces (the box sphere, the two slab faces, and the level wall inside the slab), and the two lemmas
below split the count accordingly:

* `encard_frontier_le_boxSphere_add_inbox` — the level count is at most the number of crossings of
  the knot with the **box sphere** plus the number of its crossings with the frontier **inside the
  box** (the slab faces behind the level and the wall inside the slab);
* `encard_frontier_lt_min_of_parts` — hence, if the two parts are bounded by `A` and `B` with
  `A + B < min p q`, the level count is `< min p q`;
* `inbox_paramSet_eq_empty_of_avoids_slab` and `encard_frontier_lt_min_of_avoids_slab` — the in-box
  part is *zero* as soon as the knot misses the closed slab in the box (every frontier point of the
  removed set inside the box lies in the closed slab), so in that case the crux's box-sphere count
  `hS` alone bounds the level count.

The in-box part is the delicate one: the wall `{ℓ = lam}` *moves* with the level, so its crossings
with the knot are not bounded by the crux's fixed plane count `hU` at the level `u`; the honest
bound is combinatorial — the in-box frontier points of the knot are the endpoints of its arcs inside
the trench `PBox ∩ slabClosed ∩ {ℓ < lam}`, hence at most twice the number of those arcs (see the
notes `NOTES_tiltedTraceDataWExists.md`). -/

/-- **The parameter count dominates the geometric count.**  For any set `A`, the number of points of
`range K ∩ A` is at most the number of parameters in the fundamental interval whose image lies in
`A`.  No injectivity is needed: the image of a set has no more elements than the set. -/
theorem encard_range_inter_le_paramSet (K : Knot) (A : Set R3) :
    Set.encard (Set.range K.curve ∩ A) ≤
      Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ A} := by
  have h1 : Set.range K.curve ∩ A =
      K.curve '' {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ A} := by
    rw [Work.Drive.EpsForm.range_knot_eq_image_Ico K]
    ext y
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hyA⟩
      exact ⟨t, ⟨ht, hyA⟩, rfl⟩
    · rintro ⟨t, ⟨ht, htA⟩, rfl⟩
      exact ⟨⟨t, ht, rfl⟩, htA⟩
  rw [h1]
  exact Set.encard_image_le K.curve _

/-- **The level count splits into the box-sphere part and the in-box part.**  A point of the knot on
the level frontier either lies on the box sphere, or lies in the (open) box, where the frontier of
the removed set is the frontier of the slab chunk. -/
theorem encard_frontier_le_boxSphere_add_inbox (K : Knot) {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} (hs : 0 < s) :
    Set.encard (Set.range K.curve ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) ≤
      Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          Submission.boxNorm c σ (K.curve t) = s} +
      Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          K.curve t ∈ Submission.PBox s c σ ∧
          K.curve t ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)} := by
  have hfrPBox : frontier (Submission.PBox s c σ) = Work.BoxShrink.Core.sphereSet c σ s := by
    rw [Work.Topology.SphereSlicing.frontier_PBox hs c σ,
      Work.BoxShrink.Core.sphereSet_eq_BoxSphere]
  have hsub : Set.range K.curve ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) ⊆
      (Set.range K.curve ∩ Work.BoxShrink.Core.sphereSet c σ s) ∪
        (Set.range K.curve ∩ (Submission.PBox s c σ ∩
          frontier (tiltedLevelRemoved s c σ u v h ℓ lam))) := by
    rintro y ⟨hyK, hyF⟩
    have hcl : y ∈ closure (Submission.PBox s c σ) :=
      closure_mono (show tiltedLevelRemoved s c σ u v h ℓ lam ⊆ Submission.PBox s c σ from
        fun z hz => hz.1) (frontier_subset_closure hyF)
    rw [closure_eq_self_union_frontier, hfrPBox] at hcl
    rcases hcl with hybox | hysph
    · exact Or.inr ⟨hyK, hybox, hyF⟩
    · exact Or.inl ⟨hyK, hysph⟩
  refine le_trans (Set.encard_le_encard hsub) (le_trans (Set.encard_union_le _ _) ?_)
  refine add_le_add ?_ ?_
  · exact encard_range_inter_le_paramSet K (Work.BoxShrink.Core.sphereSet c σ s)
  · exact encard_range_inter_le_paramSet K
      (Submission.PBox s c σ ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam))

/-- **The level count from the two parts.** -/
theorem encard_frontier_lt_min_of_parts (p q : ℕ) (K : Knot) {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {A B : ℕ∞}
    (hs : 0 < s)
    (hS : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} ≤ A)
    (hin : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        K.curve t ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)} ≤ B)
    (hAB : A + B < (Nat.min p q : ℕ∞)) :
    Set.encard (Set.range K.curve ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) <
      (Nat.min p q : ℕ∞) :=
  lt_of_le_of_lt
    (le_trans (encard_frontier_le_boxSphere_add_inbox (K := K) (s := s) (u := u) (c := c)
      (σ := σ) (v := v) (h := h) (ℓ := ℓ) (lam := lam) hs) (add_le_add hS hin)) hAB

/-- **A frontier point of the removed set inside the box lies in the closed slab.**  This is
`Work.Drive.EpsFormSphere.frontier_tiltedSwept_subset`: inside the box the frontier of the removed
set is the frontier of the slab chunk, which lies in the closed slab. -/
theorem abs_le_of_mem_PBox_frontier_tiltedLevelRemoved {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {y : R3}
    (hybox : y ∈ Submission.PBox s c σ)
    (hyfr : y ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) :
    |inner ℝ v y - (inner ℝ v c + u)| ≤ h := by
  have hfr := Work.Drive.EpsFormSphere.frontier_tiltedSwept_subset s (inner ℝ v c + u) h lam c v
    σ ℓ hyfr
  rcases hfr with hf | hf
  · have hmem : y ∈ interior (Submission.PBox s c σ) := by
      rw [(Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq]
      exact hybox
    exact absurd hmem hf.2
  · rcases hf with hf | hf
    · exact le_of_eq hf
    · exact le_of_lt hf.1

/-- **The in-box part of the level count vanishes when the knot misses the slab.** -/
theorem inbox_paramSet_eq_empty_of_avoids_slab (K : Knot) {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    (havoid : ∀ t : ℝ, t ∈ Set.Ico 0 (2 * Real.pi) → K.curve t ∈ Submission.PBox s c σ →
      h < |inner ℝ v (K.curve t) - (inner ℝ v c + u)|) :
    {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ Submission.PBox s c σ ∧
      K.curve t ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro t ⟨htIco, htbox, htfr⟩
  exact absurd (abs_le_of_mem_PBox_frontier_tiltedLevelRemoved htbox htfr)
    (not_le.mpr (havoid t htIco htbox))

/-- **The level count when the knot misses the slab in the box**: only the box-sphere part
remains. -/
theorem encard_frontier_lt_min_of_avoids_slab (p q : ℕ) (K : Knot) {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {A : ℕ∞}
    (hs : 0 < s)
    (havoid : ∀ t : ℝ, t ∈ Set.Ico 0 (2 * Real.pi) → K.curve t ∈ Submission.PBox s c σ →
      h < |inner ℝ v (K.curve t) - (inner ℝ v c + u)|)
    (hS : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} ≤ A)
    (hA : A < (Nat.min p q : ℕ∞)) :
    Set.encard (Set.range K.curve ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) <
      (Nat.min p q : ℕ∞) := by
  refine encard_frontier_lt_min_of_parts p q K (A := A) (B := 0) hs hS ?_ ?_
  · rw [inbox_paramSet_eq_empty_of_avoids_slab (K := K) (s := s) (u := u) (c := c) (σ := σ)
      (v := v) (h := h) (ℓ := ℓ) (lam := lam) havoid, Set.encard_empty]
  · rw [add_zero]; exact hA


/-- **Clause 1 at a level where the knot misses the closed slab in the box.**  With the local models
of the trace, the sphere-ness of the level frontier and the crux's box-sphere count, the inessentiality
input of clause 1 is free at every level at which the knot stays outside the closed slab: the count of
`(★)` reduces to the box-sphere part (`encard_frontier_lt_min_of_avoids_slab`). -/
theorem traceCurvesAt_of_isEmbeddedSphere_of_avoids_slab {ψ : Submission.Diffeo} {s u : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    (H : ∀ z : R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam) →
      ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
        Work.Smooth.OneManifold.IsLocallyEuclidean
          (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
            frontier (tiltedLevelRemoved s c σ u v h ℓ lam))))
    (hsphere : Work.InnermostDisk.IsEmbeddedSphere
      (frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot) {A : ℕ∞}
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ)) (hs : 0 < s)
    (havoid : ∀ t : ℝ, t ∈ Set.Ico 0 (2 * Real.pi) → K.curve t ∈ Submission.PBox s c σ →
      h < |inner ℝ v (K.curve t) - (inner ℝ v c + u)|)
    (hS : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} ≤ A)
    (hA : A < (Nat.min p q : ℕ∞)) :
    TraceCurvesAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam :=
  traceCurvesAt_of_local_models_of_isEmbeddedSphere H hsphere p q hp hq hc K himg hcl
    (encard_frontier_lt_min_of_avoids_slab p q K hs havoid hS hA)


/-! ## The in-box part of the level count, from the trench structure

`Work.Drive.Mono.inbox_frontier_subset` (proved by a colleague) says that the parameters in the
fundamental interval whose image lies in the box and on the frontier of the level's removed set are
boundary points of the *trench* parameter set, save for three degenerate kinds (critical points of
the sweep height, tangencies with the slab faces, and the wall/face corners);
`Work.Drive.Mono.encard_le_two_mul_of_cover` says that a set covered by `m` intervals has at most
`2 m` frontier points.  Together: if the trench of the level is a finite union of `m` intervals and
the level meets none of the degenerate points, then the in-box part of the level count is at most
`2 m`.  Combined with `encard_frontier_lt_min_of_parts`, this makes the level count `< min p q` as
soon as the box-sphere count and twice the number of trench arcs fit the budget `150 d`.

The number of trench arcs `m` is bounded by the number of visits of the knot to `box ∩ slab`, which
in turn is bounded by the number of crossings of the knot with the cutting plane provided no visit
"grazes" the slab (see `NOTES_H381_count_decoration.md` §3–§4 for the analysis and the data
conditions that make this hold). -/

/-- **The in-box part of the level count from the trench structure.** -/
theorem encard_inbox_le_two_mul_of_trench {K : Knot} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {m : ℕ}
    (a b : Fin m → ℝ) (hh : 0 < h)
    (hA : frontier {t : ℝ | K.curve t ∈ Submission.PBox s c σ ∧
        |inner ℝ v (K.curve t) - (inner ℝ v c + u)| < h ∧ ℓ (K.curve t) < lam} =
      frontier (⋃ i : Fin m, Set.Icc (a i) (b i)))
    (hclean : ∀ t : ℝ, t ∈ Set.Ico 0 (2 * Real.pi) → K.curve t ∈ Submission.PBox s c σ →
      K.curve t ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) →
      deriv (fun s : ℝ => ℓ (K.curve s)) t ≠ 0 ∧
      (|inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h →
        deriv (fun s : ℝ => inner ℝ v (K.curve s)) t ≠ 0) ∧
      (|inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h → ℓ (K.curve t) ≠ lam)) :
    Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ Submission.PBox s c σ ∧
        K.curve t ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)} ≤ 2 * m := by
  have hsub : {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ Submission.PBox s c σ ∧
        K.curve t ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)} ⊆
      frontier (⋃ i : Fin m, Set.Icc (a i) (b i)) := by
    intro t ht
    obtain ⟨htIco, htbox, htfr⟩ := ht
    have hcl := hclean t htIco htbox htfr
    have h1 := Work.Drive.Mono.inbox_frontier_subset (K := K) (s := s) (u := u) (c := c)
      (σ := σ) (v := v) (h := h) (ℓ := ℓ) (lam := lam) hh ⟨htIco, htbox, htfr⟩
    rcases h1 with h2 | h2
    · rcases h2 with h2 | h2
      · rcases h2 with h2 | h2
        · rw [hA] at h2; exact h2
        · exact absurd h2 hcl.1
      · exact absurd h2.2 (hcl.2.1 h2.1)
    · exact absurd h2.2 (hcl.2.2 h2.1)
  exact encard_le_two_mul_of_cover a b hsub


/-- **The capstone of the level count**: the box-sphere count plus twice the number of trench arcs. -/
theorem encard_frontier_lt_min_of_trench (p q : ℕ) {K : Knot} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {m : ℕ}
    (a b : Fin m → ℝ) (hs : 0 < s) (hh : 0 < h)
    (hA : frontier {t : ℝ | K.curve t ∈ Submission.PBox s c σ ∧
        |inner ℝ v (K.curve t) - (inner ℝ v c + u)| < h ∧ ℓ (K.curve t) < lam} =
      frontier (⋃ i : Fin m, Set.Icc (a i) (b i)))
    (hclean : ∀ t : ℝ, t ∈ Set.Ico 0 (2 * Real.pi) → K.curve t ∈ Submission.PBox s c σ →
      K.curve t ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) →
      deriv (fun s : ℝ => ℓ (K.curve s)) t ≠ 0 ∧
      (|inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h →
        deriv (fun s : ℝ => inner ℝ v (K.curve s)) t ≠ 0) ∧
      (|inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h → ℓ (K.curve t) ≠ lam)) {A : ℕ∞}
    (hS : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} ≤ A)
    (harith : A + 2 * m < (Nat.min p q : ℕ∞)) :
    Set.encard (Set.range K.curve ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) <
      (Nat.min p q : ℕ∞) :=
  encard_frontier_lt_min_of_parts p q K hs hS
    (encard_inbox_le_two_mul_of_trench a b hh hA hclean) harith


/-! ## The trace of the tilted sweep lies on the box sphere and within `2h` of the cutting plane

**(P1) of the design, geometrically.**  The trace of a level of the tilted sweep is the part on the
surface of the frontier of `PBox \ (tiltedSlabClosed ∩ {ℓ < lam})`; the elementary fact proved in
this section is that **every point of it is either on the box sphere, or within `2h` of the *flat
cutting plane*** `{y | y (σ 2) = c (σ 2) + u}`, where `h` is the half-width of the tilted slab and
`‖v - e_{σ 2}‖ R < h`, `‖y - c‖ ≤ R` on the box.

This is the geometric reason the fleet's *corrected* design (`Work.Drive.wallDisc`,
`Work.EpsW.discWallFrontier`) walls by the **flat cutting disc** rather than by a slab: with the flat
wall the trace lies on the *footprint* `∂PBox ∪ cutDisc` itself, and the crux's two counts control
the knot's intersections with the trace **uniformly in the level**
(`Work.EpsW.encard_trace_discWallRegion_lt`, proved).  With the tilted slab the trace lies only in
the `2h`-neighbourhood of the cutting plane, whose intersections with the knot are *not* controlled
by the two counts — the `hatt` obstruction of
`Work.Drive.EpsFormSphere.encard_frontier_tiltedSweptBall_lt_min`.  What is nevertheless immediate,
and recorded here, is:

* `frontier_tiltedLevelRemoved_subset_sphereSet_union_thickCutPlane` — the containment;
* `inbox_paramSet_subset_thickCutPlane` — the in-box part of the level count is a subset of the
  knot parameters in that `2h`-neighbourhood;
* `encard_frontier_lt_min_of_avoids_thickCutPlane` — **the level count at every level** when the
  knot avoids that neighbourhood: this is strictly weaker than the "avoids the closed tilted slab"
  hypothesis of `encard_frontier_lt_min_of_avoids_slab`, and (the containment being level-free) the
  count holds at *every* level at once. -/

section TraceGeometry

/-- `Work.BoxShrink.shiftVσ σ 1` is the unit vector of the `σ 2`-coordinate. -/
theorem inner_shiftVσ_one (σ : Equiv.Perm (Fin 3)) (y : R3) :
    inner ℝ (Work.BoxShrink.shiftVσ σ 1) y = y (σ 2) := by
  rw [PiLp.inner_apply, Finset.sum_eq_single (σ 2)]
  · simp
  · intro b _ hb; simp [Work.BoxShrink.shiftVσ, hb]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Inside the box the flat coordinate and the tilted coordinate differ by at most
`‖v - e_{σ 2}‖ R`.** -/
theorem abs_coord_sub_inner_le {y c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {R : ℝ}
    (hR : ‖y - c‖ ≤ R) :
    |y (σ 2) - c (σ 2) - (inner ℝ v y - inner ℝ v c)| ≤
      ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R := by
  have h1 : y (σ 2) - c (σ 2) = inner ℝ (Work.BoxShrink.shiftVσ σ 1) (y - c) := by
    rw [inner_sub_right, inner_shiftVσ_one, inner_shiftVσ_one]
  have h2 : inner ℝ v y - inner ℝ v c = inner ℝ v (y - c) := (inner_sub_right v y c).symm
  rw [h1, h2]
  have h3 : inner ℝ (Work.BoxShrink.shiftVσ σ 1) (y - c) - inner ℝ v (y - c) =
      inner ℝ (Work.BoxShrink.shiftVσ σ 1 - v) (y - c) := (inner_sub_left _ _ _).symm
  rw [h3]
  calc |inner ℝ (Work.BoxShrink.shiftVσ σ 1 - v) (y - c)|
      ≤ ‖Work.BoxShrink.shiftVσ σ 1 - v‖ * ‖y - c‖ := abs_real_inner_le_norm _ _
    _ = ‖v - Work.BoxShrink.shiftVσ σ 1‖ * ‖y - c‖ := by rw [norm_sub_rev]
    _ ≤ ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R :=
        mul_le_mul_of_nonneg_left hR (norm_nonneg _)

/-- **On the box, a point of the tilted closed slab is within `2h` of the flat cutting plane.** -/
theorem abs_coord_le_two_mul_h_of_mem_slab {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {v y : R3} {h R : ℝ} (hRbox : ‖y - c‖ ≤ R)
    (hsize : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R < h)
    (hslab : |inner ℝ v y - (inner ℝ v c + u)| ≤ h) :
    |y (σ 2) - (c (σ 2) + u)| ≤ 2 * h := by
  have hd := abs_coord_sub_inner_le (v := v) (σ := σ) (c := c) (y := y) (R := R) hRbox
  have hkey : y (σ 2) - (c (σ 2) + u) =
      (inner ℝ v y - (inner ℝ v c + u)) +
        (y (σ 2) - c (σ 2) - (inner ℝ v y - inner ℝ v c)) := by ring
  show |y (σ 2) - (c (σ 2) + u)| ≤ 2 * h
  rw [hkey]
  calc |(inner ℝ v y - (inner ℝ v c + u)) +
          (y (σ 2) - c (σ 2) - (inner ℝ v y - inner ℝ v c))|
      ≤ |inner ℝ v y - (inner ℝ v c + u)| +
          |y (σ 2) - c (σ 2) - (inner ℝ v y - inner ℝ v c)| := abs_add_le _ _
    _ ≤ h + ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R := add_le_add hslab hd
    _ ≤ h + h := add_le_add le_rfl (le_of_lt hsize)
    _ = 2 * h := by ring

/-- **At a point of the box on the frontier of the removed set, the frontier of the *slab chunk*
already contains it.** -/
theorem frontier_slabChunk_of_mem_PBox {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3}
    {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {y : R3} (hs : 0 < s)
    (hy : y ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam))
    (hybox : y ∈ Submission.PBox s c σ) :
    y ∈ frontier (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
      {z : R3 | ℓ z < lam}) := by
  rcases Work.Drive.EpsFormSphere.frontier_sdiff_subset (Submission.PBox s c σ)
      (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {z : R3 | ℓ z < lam}) hy with
    hfr | hfrB
  · have hfr' : frontier (Submission.PBox s c σ) = Work.BoxShrink.Core.sphereSet c σ s := by
      rw [Work.Topology.SphereSlicing.frontier_PBox hs c σ,
        Work.BoxShrink.Core.sphereSet_eq_BoxSphere]
    rw [hfr', Work.BoxShrink.Core.mem_sphereSet] at hfr
    rw [Submission.mem_PBox_iff] at hybox
    exact absurd hfr (ne_of_lt hybox)
  · exact hfrB

/-- A point of the frontier of the slab chunk is in the closed slab. -/
theorem abs_inner_le_of_mem_frontier_slabChunk {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {y : R3}
    (hy : y ∈ frontier (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
      {z : R3 | ℓ z < lam})) :
    |inner ℝ v y - (inner ℝ v c + u)| ≤ h := by
  have hcl : y ∈ closure (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
      {z : R3 | ℓ z < lam}) := frontier_subset_closure hy
  have h2 : y ∈ closure (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) :=
    closure_mono Set.inter_subset_left hcl
  rwa [(Work.Drive.EpsForm.isClosed_tiltedSlabClosed _ _ _).closure_eq] at h2

/-- **The trace of a level of the tilted sweep lies on the box sphere or within `2h` of the flat
cutting plane.** -/
theorem frontier_tiltedLevelRemoved_subset_sphereSet_union_thickCutPlane {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} (hs : 0 < s)
    (hRbox : ∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R)
    (hsize : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R < h) :
    frontier (tiltedLevelRemoved s c σ u v h ℓ lam) ⊆
      Work.BoxShrink.Core.sphereSet c σ s ∪
        {y : R3 | |y (σ 2) - (c (σ 2) + u)| ≤ 2 * h} := by
  have hfrPBox : frontier (Submission.PBox s c σ) = Work.BoxShrink.Core.sphereSet c σ s := by
    rw [Work.Topology.SphereSlicing.frontier_PBox hs c σ,
      Work.BoxShrink.Core.sphereSet_eq_BoxSphere]
  intro y hy
  rcases Work.Drive.EpsFormSphere.frontier_sdiff_subset_frontier_union (Submission.PBox s c σ)
      (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {z : R3 | ℓ z < lam}) hy with
    hfr | hbox
  · exact Or.inl (by rw [← hfrPBox]; exact hfr)
  · refine Or.inr ?_
    exact abs_coord_le_two_mul_h_of_mem_slab (hRbox y hbox) hsize
      (abs_inner_le_of_mem_frontier_slabChunk (c := c) (σ := σ) (u := u) (v := v) (h := h)
        (ℓ := ℓ) (lam := lam)
        (frontier_slabChunk_of_mem_PBox (s := s) (u := u) (c := c) (σ := σ) (v := v) (h := h)
          (ℓ := ℓ) (lam := lam) hs hy hbox))

/-- **The in-box part of the level count is contained in the knot parameters of the
`2h`-neighbourhood of the cutting plane.** -/
theorem inbox_paramSet_subset_thickCutPlane (K : Knot) {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    (hRbox : ∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R)
    (hsize : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R < h) :
    {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ Submission.PBox s c σ ∧
      K.curve t ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)} ⊆
      {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        |(K.curve t) (σ 2) - (c (σ 2) + u)| ≤ 2 * h} := by
  rintro t ⟨htIco, htbox, htfr⟩
  refine ⟨htIco, ?_⟩
  have h1 : |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ h :=
    abs_le_of_mem_PBox_frontier_tiltedLevelRemoved (s := s) (u := u) (c := c) (σ := σ) (v := v)
      (h := h) (ℓ := ℓ) (lam := lam) htbox htfr
  exact abs_coord_le_two_mul_h_of_mem_slab (hRbox (K.curve t) htbox) hsize h1

/-- **The level count when the knot avoids the `2h`-neighbourhood of the cutting plane (at every
level at once).**  This is `encard_frontier_lt_min_of_avoids_slab` with the tilted *slab* replaced
by the `2h`-neighbourhood of the flat cutting plane — a strictly weaker avoidance condition, and
one dispensed at every level simultaneously, because the containment
`frontier_tiltedLevelRemoved_subset_sphereSet_union_thickCutPlane` does not mention the level. -/
theorem encard_frontier_lt_min_of_avoids_thickCutPlane (p q : ℕ) (K : Knot) {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {A : ℕ∞}
    (hs : 0 < s)
    (hRbox : ∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R)
    (hsize : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R < h)
    (havoid : ∀ t : ℝ, t ∈ Set.Ico 0 (2 * Real.pi) → K.curve t ∈ Submission.PBox s c σ →
      2 * h < |(K.curve t) (σ 2) - (c (σ 2) + u)|)
    (hS : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} ≤ A)
    (hA : A < (Nat.min p q : ℕ∞)) :
    Set.encard (Set.range K.curve ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) <
      (Nat.min p q : ℕ∞) := by
  refine encard_frontier_lt_min_of_parts p q K (A := A) (B := 0) hs hS ?_ ?_
  · rw [show {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ Submission.PBox s c σ ∧
        K.curve t ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)} = (∅ : Set ℝ) from ?_,
      Set.encard_empty]
    rw [Set.eq_empty_iff_forall_notMem]
    rintro t ⟨htIco, htbox, htfr⟩
    exact absurd (inbox_paramSet_subset_thickCutPlane (K := K) (hRbox := hRbox) (hsize := hsize)
      ⟨htIco, htbox, htfr⟩).2 (not_le.mpr (havoid t htIco htbox))
  · rw [add_zero]; exact hA


/-! ## The forced slab visit at the cutting levels of the box sphere

At the cutting level `u := z₀ (σ 2) - c (σ 2)` determined by a point `z₀` of the **box sphere**,
every datum satisfying the size condition `‖v - e_{σ 2}‖ * R < h` puts `z₀` into the **open** tilted
slab: the tilted slab height of `z₀` differs from its flat height `z₀ (σ 2) - c (σ 2)` by at most
`‖v - e_{σ 2}‖ * R < h` (`abs_slabHeight_lt_h_of_coord_eq`).

This is the machine-checked obstruction to the counting route of clause 1 at *every* cutting level.
The no-grazing conjunct

    hboxsph : ∀ t, boxNorm c σ (K.curve t) = s → h ≤ |⟪v, K.curve t⟫ - (⟪v, c⟫ + u)|

of the counted data (the fifth knot-genericity conjunct of `Work.Drive.Mono.Geom2Data`, consumed by
`Work.Drive.Mono.visit_facts`, `Work.Drive.Mono.encard_tiltedCrossings_le_flat` and
`Work.Drive.Mono.levelCount_lt_min_all`) is **unsatisfiable for every datum** as soon as the flat
cutting plane `{y (σ 2) = c (σ 2) + u}` meets the knot's box-sphere points
(`not_hboxsph_of_coord_eq`).  Since the deliverable quantifies over *every* cutting level `u`, the
counted data of the tilted sweep are therefore genuinely an almost-everywhere object in `u`:
`hboxsph` implies the first conjunct of the fleet's general position hypothesis
`Work.Drive.Mono.CutTransverse K s c σ u` (`mem_PBox_of_hboxsph_of_coord_eq`), so at the cutting
levels excluded by `CutTransverse` the count of `Work.Drive.Mono.levelCount_lt_min_all` is
unavailable and clause 1 needs a different argument.  This is the machine-checked form of §6 of
`NOTES_H381_s10_thinSlab_producer.md` (conjuncts 10--14 are almost-everywhere in `u`). -/

/-- The box norm is continuous in the point. -/
private theorem continuous_boxNorm_aux (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Continuous (fun y : R3 => Submission.boxNorm c σ y) := by
  unfold Submission.boxNorm
  fun_prop

/-- The closure of the open box is contained in the sublevel set `{boxNorm ≤ s}`. -/
private theorem closure_PBox_subset_boxNorm_aux (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    closure (Submission.PBox s c σ) ⊆ {y : R3 | Submission.boxNorm c σ y ≤ s} := by
  refine closure_minimal (fun y hy => ?_) ?_
  · show Submission.boxNorm c σ y ≤ s
    exact le_of_lt ((Submission.mem_PBox_iff s c σ y).mp hy)
  · exact isClosed_le (continuous_boxNorm_aux c σ) continuous_const

/-- **The radius bound of the tilt data extends to the closure of the box.** -/
theorem norm_sub_le_R_of_mem_closure_PBox {s R : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {y : R3}
    (hRbox : ∀ z ∈ Submission.PBox s c σ, ‖z - c‖ ≤ R)
    (hy : y ∈ closure (Submission.PBox s c σ)) : ‖y - c‖ ≤ R := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨z, hz, hzd⟩ := Metric.mem_closure_iff.mp hy ε hε
  have h1 : y - c = (y - z) + (z - c) := by abel
  have h2 : ‖y - z‖ < ε := by rwa [dist_eq_norm] at hzd
  calc ‖y - c‖ = ‖(y - z) + (z - c)‖ := by rw [h1]
    _ ≤ ‖y - z‖ + ‖z - c‖ := norm_add_le _ _
    _ ≤ ε + R := add_le_add (le_of_lt h2) (hRbox z hz)
    _ = R + ε := by ring

/-- **A point of the closed box at the flat cutting height lies strictly inside the tilted slab**,
for every datum satisfying the size condition. -/
theorem abs_slabHeight_lt_h_of_coord_eq {s u h R : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v y : R3}
    (hRbox : ∀ z ∈ Submission.PBox s c σ, ‖z - c‖ ≤ R)
    (hy : y ∈ closure (Submission.PBox s c σ))
    (hsize : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R < h)
    (hu : u = y (σ 2) - c (σ 2)) :
    |inner ℝ v y - (inner ℝ v c + u)| < h := by
  have hR : ‖y - c‖ ≤ R := norm_sub_le_R_of_mem_closure_PBox hRbox hy
  have hd := abs_coord_sub_inner_le (v := v) (σ := σ) (c := c) (y := y) (R := R) hR
  have hkey : inner ℝ v y - (inner ℝ v c + u)
      = -(y (σ 2) - c (σ 2) - (inner ℝ v y - inner ℝ v c)) := by
    rw [hu]; ring
  rw [hkey, abs_neg]
  exact lt_of_le_of_lt hd hsize

/-- **At the cutting level of a knot point of the box sphere the no-grazing conjunct `hboxsph` of
the counted data fails, for every datum.** -/
theorem not_hboxsph_of_coord_eq {ψ : Submission.Diffeo} {K : Knot} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} (hs : 0 < s)
    (hT : TiltData ψ s c σ u v h R ℓ exc lam0 lam1) {t₀ : ℝ}
    (hbox : Submission.boxNorm c σ (K.curve t₀) = s)
    (hu : u = (K.curve t₀) (σ 2) - c (σ 2)) :
    ¬ (h ≤ |inner ℝ v (K.curve t₀) - (inner ℝ v c + u)|) := by
  obtain ⟨_, _, _, _, hsize, _, hRbox, _, _, _, _⟩ := hT
  have hmem : K.curve t₀ ∈ closure (Submission.PBox s c σ) := by
    refine frontier_subset_closure ?_
    rw [Work.Topology.SphereSlicing.frontier_PBox hs c σ,
      ← Work.BoxShrink.Core.sphereSet_eq_BoxSphere]
    exact Work.BoxShrink.Core.mem_sphereSet.mpr hbox
  exact not_le.mpr (abs_slabHeight_lt_h_of_coord_eq hRbox hmem hsize hu)

/-- **The no-grazing conjunct `hboxsph` implies the first conjunct of the fleet's general position
condition `Work.Drive.Mono.CutTransverse`**: a knot point of the closed box at the cutting height
lies in the *open* box.  Hence the two conditions are not independent, and the cutting levels at
which `hboxsph` fails are exactly those at which a knot point of the box sphere sits on the flat
cutting plane. -/
theorem mem_PBox_of_hboxsph_of_coord_eq {ψ : Submission.Diffeo} {K : Knot} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} (hs : 0 < s)
    (hT : TiltData ψ s c σ u v h R ℓ exc lam0 lam1)
    (hboxsph : ∀ t : ℝ, Submission.boxNorm c σ (K.curve t) = s →
      h ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)|)
    {t : ℝ} (ht : K.curve t ∈ closure (Submission.PBox s c σ))
    (hcoord : (K.curve t) (σ 2) = c (σ 2) + u) :
    K.curve t ∈ Submission.PBox s c σ := by
  by_contra hnot
  have hle : Submission.boxNorm c σ (K.curve t) ≤ s :=
    closure_PBox_subset_boxNorm_aux s c σ ht
  have hne : Submission.boxNorm c σ (K.curve t) ≠ s := by
    intro heq
    exact (not_hboxsph_of_coord_eq (K := K) hs hT heq (by rw [hcoord]; ring))
      (hboxsph t heq)
  exact hnot ((Submission.mem_PBox_iff s c σ (K.curve t)).mpr (lt_of_le_of_ne hle hne))

/-- **The slack of the `hboxsph`-free level count is *forced*, at the cutting levels of the knot's
box-sphere points.**

`Work.Drive.Mono.not_hboxsph_of_coord_eq` says that at the cutting level `u = z₀ (σ 2) - c (σ 2)` of
a knot point `z₀` of the box sphere, the no-grazing conjunct

    hboxsph : ∀ t, boxNorm c σ (K.curve t) = s → h ≤ |⟪v, K.curve t⟫ - (⟪v, c⟫ + u)|

of `Work.Drive.Mono.visit_facts_le` / `Work.Drive.Mono.levelCount_lt_min_all` fails *for every
datum*.  The lemma below says more: it fails at a point of the fundamental interval, i.e. the set of
knot parameters

    {t ∈ [0, 2π) | boxNorm c σ (K.curve t) = s ∧ |⟪v, K.curve t⟫ - (⟪v, c⟫ + u)| < h}

— the set whose `encard` is the slack `k` of
`Work.Drive.Mono.levelCount_lt_min_all_of_boxSphereSlabPts` (which replaces `hboxsph` by the extra
arithmetic `A + 2 * B + 4 * k < min p q`) — is **nonempty**, for every datum satisfying `TiltData`.

Consequence (the reason the level count is not available at the cutting levels of the knot's
box-sphere points, in this framework): at those levels the slack of that statement is at least `4`
(resp. `2`, under the transversality of `Work.Drive.Mono.boxA` at the box-sphere points), while the
crux supplies only the *exactly tight* arithmetic `countConst * d = 150 * d < min p q` of the counts
`hS ≤ 75 d`, `hU ≤ 37.5 d`.  No amount of bookkeeping in the visit machinery closes the gap there;
one needs a different argument, or the general position provided by the a.e. hypotheses `CutTransverse`
and `BoxGenE` (which is why the fleet's producers are stated a.e. in the cutting level). -/
theorem one_le_encard_boxSphere_openSlab {ψ : Submission.Diffeo} {K : Knot} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} (hs : 0 < s)
    (hT : TiltData ψ s c σ u v h R ℓ exc lam0 lam1) {t₀ : ℝ}
    (hbox : Submission.boxNorm c σ (K.curve t₀) = s)
    (hu : u = (K.curve t₀) (σ 2) - c (σ 2)) :
    (1 : ℕ∞) ≤ Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      Submission.boxNorm c σ (K.curve t) = s ∧
      |inner ℝ v (K.curve t) - (inner ℝ v c + u)| < h} := by
  obtain ⟨_, _, _, _, hsize, _, hRbox, _, _, _, _⟩ := hT
  have hper : Function.Periodic K.curve (2 * Real.pi) := fun t => K.periodic t
  set m : ℤ := ⌊t₀ / (2 * Real.pi)⌋ with hm
  set t₁ : ℝ := t₀ - 2 * Real.pi * (m : ℝ) with ht₁
  have ht₁_eq : t₁ = t₀ + (((-m : ℤ)) : ℝ) * (2 * Real.pi) := by
    rw [ht₁]; push_cast; ring
  have hcurve : K.curve t₁ = K.curve t₀ := by
    rw [ht₁_eq, hper.int_mul]
  have hmul : (t₀ / (2 * Real.pi) - (m : ℝ)) * (2 * Real.pi) = t₁ := by
    have h2 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    rw [ht₁, sub_mul, div_mul_cancel₀ t₀ h2]; ring
  have ht₁_mem : t₁ ∈ Set.Ico 0 (2 * Real.pi) := by
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    have h1 : 0 ≤ t₀ / (2 * Real.pi) - (m : ℝ) := by
      have := Int.fract_nonneg (t₀ / (2 * Real.pi))
      rw [Int.fract] at this
      linarith
    have h2 : t₀ / (2 * Real.pi) - (m : ℝ) < 1 := by
      have := Int.fract_lt_one (t₀ / (2 * Real.pi))
      rw [Int.fract] at this
      linarith
    refine ⟨?_, ?_⟩
    · rw [← hmul]; exact mul_nonneg h1 h2pi.le
    · rw [← hmul]
      calc (t₀ / (2 * Real.pi) - (m : ℝ)) * (2 * Real.pi)
          < 1 * (2 * Real.pi) := mul_lt_mul_of_pos_right h2 h2pi
        _ = 2 * Real.pi := one_mul _
  have hcut : |inner ℝ v (K.curve t₁) - (inner ℝ v c + u)| < h := by
    rw [hcurve]
    refine abs_slabHeight_lt_h_of_coord_eq hRbox ?_ hsize hu
    refine frontier_subset_closure ?_
    rw [Work.Topology.SphereSlicing.frontier_PBox hs c σ,
      ← Work.BoxShrink.Core.sphereSet_eq_BoxSphere]
    exact Work.BoxShrink.Core.mem_sphereSet.mpr hbox
  have hmem : t₁ ∈ {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      Submission.boxNorm c σ (K.curve t) = s ∧
      |inner ℝ v (K.curve t) - (inner ℝ v c + u)| < h} :=
    ⟨ht₁_mem, by rw [hcurve]; exact hbox, hcut⟩
  have hpos : (0 : ℕ∞) < _ := Set.encard_pos.mpr ⟨t₁, hmem⟩
  exact Order.one_le_iff_ne_zero.mpr hpos.ne'

/-- **A point of the trace at which the trace is *not* locally Euclidean defeats clause 1.**  This is
the contrapositive of `Work.Drive.Mono.LocalEuclideanTrace_of_traceCurves` in the pointwise form which
the junction analysis produces: the local structure of the trace at a box-sphere point of the open
slab at its own level is a "T" (three branches) exactly when the level curve of `ℓ` on the surface is
tangent to the box-sphere trace there with an even-order contact, and such a point can never lie on a
union of pairwise disjoint simple closed curves. -/
theorem not_traceCurvesAt_of_not_isLocallyEuclidean {P : Work.CoreTopology.ParamTorus} {s u : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {z : R3}
    (hz : z ∈ P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam))
    (hbad : ∀ O : Set R3, IsOpen O → z ∈ O →
      ¬ Work.Smooth.OneManifold.IsLocallyEuclidean
        (O ∩ (P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))) :
    ¬ TraceCurvesAt P s c σ u v h ℓ lam := by
  intro hTC
  refine hbad Set.univ isOpen_univ (Set.mem_univ z) ?_
  simpa using Work.Drive.Mono.LocalEuclideanTrace_of_traceCurves (P := P) hTC

end TraceGeometry


/-! ## The obstruction at the *intermediate* levels: the knot's in-box slab points are trace points

The trace of the tilted sweep at a level `lam` is `F ∩ frontier (tiltedLevelRemoved … lam)`, and the
frontier of the removed set is the frontier of `PBox \ (slabClosed ∩ {ℓ < lam})`.  The point of the
lemma below is that **every** point of the *open* slab inside the box lies on the frontier of the
removed set *of its own level*: the wall `{ℓ = lam}` is not an obstacle which the surface may avoid,
it is a genuine part of the trace at every level.

This is the exact obstruction to the counting strategy for clause 1 (Pardon's Lemma 2) at the
*intermediate* levels of the window (the levels at which the wall meets the box): the count
`Work.Drive.EpsFormSphere.encard_frontier_tiltedSweptBall_lt_min` has to bound the number of knot
parameters whose point lies in the closed box, in the closed slab and on the level frontier, and the
parameter set of the knot's in-box *open*-slab points at level `lam` is contained in it
(`wallParamSet_subset_traceParamSet`).  The hypotheses `hatt`/`hcover` of that count are precisely
what makes this contribution finite (one in-box slab visit along which `ℓ` is monotone); they are a
general-position condition on the *knot*, not a consequence of `TiltData`. -/

/-- The closure of the open half-space `{y | L y < c}` of `ℝ³` is the closed half-space
`{y | L y ≤ c}`, for a nonzero functional. -/
theorem closure_setOf_clm_lt_of_ne_zero {L : R3 →L[ℝ] ℝ} (hL : L ≠ 0) (c : ℝ) :
    closure {y : R3 | L y < c} = {y : R3 | L y ≤ c} := by
  refine Set.Subset.antisymm
    (closure_minimal (fun y hy => by
        show L y ≤ c
        exact le_of_lt (show L y < c from hy))
      (isClosed_le L.continuous continuous_const)) ?_
  intro y hy
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨w, hw, hwpos⟩ := Work.Drive.EpsFormSphere.exists_norm_lt_apply_pos hL hε
  have hy' : L y ≤ c := hy
  refine ⟨y - w, ?_, ?_⟩
  · show L (y - w) < c
    rw [map_sub]
    linarith
  · rw [dist_eq_norm, show y - (y - w) = w by abel]
    exact hw

/-- **A point of the box in the interior of the tilted slab lies on the frontier of the removed set
at its own level.** -/
theorem mem_frontier_tiltedLevelRemoved_of_mem_slab {s u h : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) {z : R3}
    (hzbox : z ∈ Submission.PBox s c σ)
    (hzslab : |inner ℝ v z - (inner ℝ v c + u)| < h) :
    z ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ (ℓ z)) := by
  have hzR : z ∈ tiltedLevelRemoved s c σ u v h ℓ (ℓ z) := by
    rw [tiltedLevelRemoved]
    exact ⟨hzbox, fun hc => absurd (show ℓ z < ℓ z from hc.2) (lt_irrefl _)⟩
  have hcl : z ∈ closure (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
      {y : R3 | ℓ y < ℓ z}) := by
    have h1 : z ∈ closure {y : R3 | ℓ y < ℓ z} := by
      rw [closure_setOf_clm_lt_of_ne_zero hℓ (ℓ z)]
      show ℓ z ≤ ℓ z
      exact le_rfl
    have h2 : z ∈ {y : R3 | |inner ℝ v y - (inner ℝ v c + u)| < h} := hzslab
    have hopen : IsOpen {y : R3 | |inner ℝ v y - (inner ℝ v c + u)| < h} :=
      isOpen_lt ((continuous_const.inner continuous_id).sub continuous_const).abs continuous_const
    have h3 := (hopen.inter_closure (t := {y : R3 | ℓ y < ℓ z})) ⟨h2, h1⟩
    refine closure_mono ?_ h3
    rintro y ⟨hy1, hy2⟩
    exact ⟨by show |inner ℝ v y - (inner ℝ v c + u)| ≤ h
              exact le_of_lt (show |inner ℝ v y - (inner ℝ v c + u)| < h from hy1), hy2⟩
  have hnotint : z ∉ interior (tiltedLevelRemoved s c σ u v h ℓ (ℓ z)) := by
    intro hint
    rw [tiltedLevelRemoved, Set.sdiff_eq, interior_inter,
      (Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq, interior_compl] at hint
    exact hint.2 hcl
  exact ⟨subset_closure hzR, hnotint⟩

/-- **The parameter set of the knot's in-box slab points at a level is contained in the parameter
set of the level's trace.**  This is the machine-checked form of the obstruction to the counting
strategy of clause 1 at the intermediate levels of the window. -/
theorem wallParamSet_subset_traceParamSet {K : Knot} {s u h lam : ℝ} {c : R3} {v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    {t : ℝ | K.curve t ∈ Submission.PBox s c σ ∧
        |inner ℝ v (K.curve t) - (inner ℝ v c + u)| < h ∧ ℓ (K.curve t) = lam} ⊆
      {t : ℝ | K.curve t ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)} := by
  rintro t ⟨htbox, htslab, htlam⟩
  have h := mem_frontier_tiltedLevelRemoved_of_mem_slab (s := s) (u := u) (h := h) (c := c)
    (σ := σ) (v := v) (ℓ := ℓ) hℓ htbox htslab
  rwa [htlam] at h


/-- **An embedded sphere whose intersection with the surface is a compact `1`-manifold is sliced.**

This is the reusable half of Pardon's first innermost argument, in the form in which the
*intermediate* levels of the tilted sweep need it: the local models of the trace
(`Work.Smooth.OneManifold.IsLocallyEuclidean`) together with compactness produce the finite family of
pairwise disjoint simple closed curves of `S ∩ F`
(`Work.EpsW.exists_family_of_isCompact_of_isLocallyEuclidean`), and Jordan–Schoenflies on the
embedded sphere `S` turns that family into a `SphereSlicing`
(`Work.InnermostDisk.sphereSlicing_of_isEmbeddedSphere_of_traceCurves`). -/
theorem sphereSlicing_of_isEmbeddedSphere_of_localModels
    {P : Work.CoreTopology.ParamTorus} {S : Set R3}
    (hsphere : Work.InnermostDisk.IsEmbeddedSphere S)
    (hcomp : IsCompact (S ∩ P.carrier))
    (hloc : Work.Smooth.OneManifold.IsLocallyEuclidean (S ∩ P.carrier)) :
    Nonempty (Work.InnermostDisk.SphereSlicing P S) := by
  obtain ⟨n, γ, hsimple, hdisj, hcover⟩ :=
    Work.EpsW.exists_family_of_isCompact_of_isLocallyEuclidean (P := P) (Z := S ∩ P.carrier)
      Set.inter_subset_right hcomp hloc
  exact Work.InnermostDisk.sphereSlicing_of_isEmbeddedSphere_of_traceCurves hsphere n γ
    hsimple hdisj hcover


/- ## Clause 1 from a decomposition of the level frontier into disjoint embedded spheres

The trace of a level is `F ∩ S_λ` with `S_λ = frontier (tiltedLevelRemoved …)` the *level frontier*.
The two sufficient conditions known so far close clause 1 by slicing one sphere containing the trace:
`∂PBox` at the bottom of the window, and the two caps above the `ℓ`-range (a *disjoint union* of two
spheres, `Work.Drive.Mono.sphereSlicing_union_of_curveFamily`).  In the *middle* of the window the
level frontier is the box sphere with the chunk boundary `∂C_λ` sewn in along the seam, and the
assembly through `∂PBox ∪ ∂C_λ` **fails**: the two spheres' traces are not disjoint along the seam,
so a trace circle can cross from the box sphere to the chunk boundary, and "each sphere carries no
essential loop" says nothing about such a circle (`NOTES_H381_L547_state.md` §4).

The lemma below is the correct shape of the assembly: it consumes a decomposition of the *level
frontier itself* into pairwise disjoint sets.  Since those sets are disjoint, closed and cover
`S_λ`, a connected trace circle lies in **one** of them; each of them carries no essential loop by
Pardon's Lemma 2 (`Work.EpsW.trace_inessential_of_slicing_of_countsWd`) applied to its own slicing
(`Work.Drive.Mono.sphereSlicing_of_isEmbeddedSphere_of_localModels`) and the *level* count (the
count on a member is at most the level count, because the member is a subset of the frontier).
Hence the only geometric input left for the intermediate levels is the decomposition of `S_λ` into
disjoint embedded spheres with compact locally Euclidean intersection with the surface. -/
theorem traceCurvesAt_of_sphereDecomposition
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u h lam : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ}
    {m : ℕ} {Ss : Fin m → Set R3}
    (hcomp : IsCompact ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))
    (hloc : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam) →
      ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
        Work.Smooth.OneManifold.IsLocallyEuclidean
          (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
            frontier (tiltedLevelRemoved s c σ u v h ℓ lam))))
    (hdecomp : frontier (tiltedLevelRemoved s c σ u v h ℓ lam) = ⋃ i, Ss i)
    (hdisj : ∀ i j : Fin m, i ≠ j → Disjoint (Ss i) (Ss j))
    (hsph : ∀ i : Fin m, Work.InnermostDisk.IsEmbeddedSphere (Ss i))
    (hcompI : ∀ i : Fin m, IsCompact (Ss i ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier))
    (hlocI : ∀ i : Fin m, Work.Smooth.OneManifold.IsLocallyEuclidean
      (Ss i ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier))
    (hcount : Set.encard (Set.range K.curve ∩
      frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞)) :
    TraceCurvesAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam := by
  set P := Work.Drive.EpsSphere.torusOf ψ with hP
  have hsub_i : ∀ i : Fin m, Ss i ⊆ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) := by
    intro i
    rw [hdecomp]
    exact Set.subset_iUnion _ i
  have hclosed_i : ∀ i : Fin m, IsClosed (Ss i) := by
    intro i
    obtain ⟨e, -, he⟩ := hsph i
    rw [← he]
    exact (isCompact_range e.continuous).isClosed
  have hnoess_i : ∀ i : Fin m, ¬ P.ContainsEssentialLoop (Ss i) := by
    intro i
    obtain ⟨Sl⟩ := sphereSlicing_of_isEmbeddedSphere_of_localModels (P := P) (S := Ss i)
      (hsph i) (hcompI i) (hlocI i)
    refine Work.EpsW.trace_inessential_of_slicing_of_countsWd p q hp hq hc ψ K himg Sl hcl ?_
    exact lt_of_le_of_lt
      (Set.encard_le_encard (Set.inter_subset_inter_right _ (hsub_i i))) hcount
  have hnoess : ¬ P.ContainsEssentialLoop
      (frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) := by
    rintro ⟨γ, hess, hγ⟩
    have hsub : Set.range γ.γ ⊆ ⋃ i, Ss i := by
      intro x hx
      obtain ⟨t, rfl⟩ := hx
      rw [← hdecomp]
      exact hγ t
    obtain ⟨i, hi⟩ := Work.InnermostDisk.exists_subset_of_preconnected_iUnion
      (isPreconnected_range γ.cont) ⟨γ.γ 0, ⟨0, rfl⟩⟩ Ss hclosed_i
      (fun i j hij => hdisj i j hij) hsub
    exact hnoess_i i ⟨γ, hess, fun t => hi ⟨t, rfl⟩⟩
  exact traceCurvesAt_of_local_models hcomp hloc hnoess


/-- **A point of the box on the wall `{ℓ = lam}`, inside the *closed* slab, lies on the frontier of
the removed set of the level `lam`.**  This is the complement of
`mem_frontier_tiltedLevelRemoved_of_mem_slab` (which treats the *interior* of the slab): together they
say that the whole of `PBox ∩ {ℓ = lam} ∩ slabClosed` is on the trace of the level.  The descent uses
a direction tangent to the slab along which `ℓ` decreases (`hdesc`), which exists as soon as
`ℓ v = 0`, `ℓ ≠ 0`, `v ≠ 0` — the hypotheses carried by `TiltData`. -/
theorem mem_frontier_tiltedLevelRemoved_of_mem_wall {s u h lam : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {z : R3}
    (hdesc : ∃ w : R3, inner ℝ v w = 0 ∧ ℓ w < 0)
    (hzbox : z ∈ Submission.PBox s c σ) (hzℓ : ℓ z = lam)
    (hzslab : |inner ℝ v z - (inner ℝ v c + u)| ≤ h) :
    z ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) := by
  have hzR : z ∈ tiltedLevelRemoved s c σ u v h ℓ lam := by
    rw [tiltedLevelRemoved]
    exact ⟨hzbox, fun hc => absurd (show ℓ z < lam from hc.2) (by rw [hzℓ]; exact lt_irrefl _)⟩
  have hzcl : z ∈ closure (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
      {y : R3 | ℓ y < lam}) := by
    obtain ⟨w, hwv, hwℓ⟩ := hdesc
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hden : 0 < 2 * (‖w‖ + 1) := by positivity
    set t : ℝ := min ε 1 / (2 * (‖w‖ + 1)) with ht
    have htpos : 0 < t := by rw [ht]; positivity
    have htε : t * ‖w‖ < ε := by
      have h1 : min ε 1 ≤ ε := min_le_left _ _
      have h2 : t ≤ ε / (2 * (‖w‖ + 1)) := by
        rw [ht, div_le_div_iff_of_pos_right hden]
        exact min_le_left _ _
      have h3 : ε / (2 * (‖w‖ + 1)) * ‖w‖ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
        nlinarith [norm_nonneg w, hε]
      calc t * ‖w‖ ≤ ε / (2 * (‖w‖ + 1)) * ‖w‖ := by
            exact mul_le_mul_of_nonneg_right h2 (norm_nonneg w)
        _ < ε := h3
    refine ⟨z + t • w, ⟨?_, ?_⟩, ?_⟩
    · show |inner ℝ v (z + t • w) - (inner ℝ v c + u)| ≤ h
      rw [inner_add_right, inner_smul_right, hwv, mul_zero, add_zero]
      exact hzslab
    · show ℓ (z + t • w) < lam
      rw [map_add, map_smul, smul_eq_mul, hzℓ]
      nlinarith [mul_neg_of_pos_of_neg htpos hwℓ]
    · rw [dist_eq_norm, show z - (z + t • w) = -(t • w) by abel, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_pos htpos]
      exact htε
  refine ⟨subset_closure hzR, fun hint => ?_⟩
  rw [tiltedLevelRemoved, Set.sdiff_eq, interior_inter,
    (Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq, interior_compl] at hint
  exact hint.2 hzcl

/-- **The knot's points on the wall of a level, inside the closed slab of the level's box, are trace
points of that level.**  This is the sharp form of the obstruction of §3: the *wall term* `hwall` of
the level count (`Work.Drive.Mono.encard_frontier_lt_min_of_face_wall`,
`Work.Drive.Mono.encard_frontier_chunk_lt_min`) is not an artifact of the faces or of the box sphere
— it is a subset of the parameter set of the level's trace. -/
theorem wallClosedParamSet_subset_traceParamSet {K : Knot} {s u h lam : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ}
    (hdesc : ∃ w : R3, inner ℝ v w = 0 ∧ ℓ w < 0) :
    {t : ℝ | K.curve t ∈ Submission.PBox s c σ ∧ ℓ (K.curve t) = lam ∧
        |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ h} ⊆
      {t : ℝ | K.curve t ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)} := by
  rintro t ⟨htbox, htℓ, htslab⟩
  exact mem_frontier_tiltedLevelRemoved_of_mem_wall (s := s) (u := u) (h := h) (c := c)
    (σ := σ) (v := v) (ℓ := ℓ) hdesc htbox htℓ htslab


/-- **The in-box part of the level frontier is on the slab faces (below the wall) or on the wall
(inside the closed slab).**  A point of the *open box* on the frontier of the removed set has either
`|⟪v,·⟫ - (⟪v,c⟫+u)| = h` and `ℓ ≤ lam` (a point of a slab face below the wall), or `ℓ = lam` and
`|⟪v,·⟫ - (⟪v,c⟫+u)| ≤ h` (a point of the wall inside the closed slab).  This sharpens the proved
`Work.Drive.EpsFormSphere.frontier_tiltedSwept_subset`, which gives the wall part only as
`{|⟪v,·⟫-a| < h ∧ ℓ = lam}`; the descent along a slab-tangent direction (`hdesc`) is what computes the
interior of the removed set. -/
theorem frontier_tiltedLevelRemoved_inter_PBox_subset {s u h lam : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ}
    (hdesc : ∃ w : R3, inner ℝ v w = 0 ∧ ℓ w < 0) :
    ∀ z : R3, z ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) →
      z ∈ Submission.PBox s c σ →
      (|inner ℝ v z - (inner ℝ v c + u)| = h ∧ ℓ z ≤ lam) ∨
        (ℓ z = lam ∧ |inner ℝ v z - (inner ℝ v c + u)| ≤ h) := by
  -- the closure of the removed part of the slab is the closed slab below the wall
  have hcl : closure (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
      {y : R3 | ℓ y < lam}) =
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y ≤ lam} := by
    refine Set.Subset.antisymm ?_ ?_
    · refine closure_minimal ?_ ?_
      · intro y hy
        have hy' : |inner ℝ v y - (inner ℝ v c + u)| ≤ h ∧ ℓ y < lam := hy
        exact ⟨hy'.1, le_of_lt hy'.2⟩
      · exact (Work.Drive.EpsForm.isClosed_tiltedSlabClosed (inner ℝ v c + u) v h).inter
          (isClosed_Iic.preimage ℓ.continuous)
    · intro y hy
      have hy' : |inner ℝ v y - (inner ℝ v c + u)| ≤ h ∧ ℓ y ≤ lam := hy
      obtain ⟨w, hwv, hwℓ⟩ := hdesc
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hden : 0 < 2 * (‖w‖ + 1) := by positivity
      set t : ℝ := min ε 1 / (2 * (‖w‖ + 1)) with ht
      have htpos : 0 < t := by rw [ht]; positivity
      have htε : t * ‖w‖ < ε := by
        have h2 : t ≤ ε / (2 * (‖w‖ + 1)) := by
          rw [ht, div_le_div_iff_of_pos_right hden]
          exact min_le_left _ _
        have h3 : ε / (2 * (‖w‖ + 1)) * ‖w‖ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
          nlinarith [norm_nonneg w, hε]
        calc t * ‖w‖ ≤ ε / (2 * (‖w‖ + 1)) * ‖w‖ :=
              mul_le_mul_of_nonneg_right h2 (norm_nonneg w)
          _ < ε := h3
      refine ⟨y + t • w, ?_, ?_⟩
      · have h1 : |inner ℝ v (y + t • w) - (inner ℝ v c + u)| ≤ h := by
          rw [inner_add_right, inner_smul_right, hwv, mul_zero, add_zero]
          exact hy'.1
        have h2 : ℓ (y + t • w) < lam := by
          rw [map_add, map_smul, smul_eq_mul]
          nlinarith [mul_neg_of_pos_of_neg htpos hwℓ, hy'.2]
        exact ⟨h1, h2⟩
      · rw [dist_eq_norm, show y - (y + t • w) = -(t • w) by abel, norm_neg, norm_smul,
          Real.norm_eq_abs, abs_of_pos htpos]
        exact htε
  have hint : interior (tiltedLevelRemoved s c σ u v h ℓ lam) =
      Submission.PBox s c σ \ (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
        {y : R3 | ℓ y ≤ lam}) := by
    rw [tiltedLevelRemoved, Set.sdiff_eq, interior_inter,
      (Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq, interior_compl, hcl]
    rw [Set.sdiff_eq]
  intro z hzfr hzbox
  rw [frontier, Set.mem_sdiff] at hzfr
  obtain ⟨hzcl, hznotint⟩ := hzfr
  -- `z` is in the closed slab and below the wall
  have hzS : |inner ℝ v z - (inner ℝ v c + u)| ≤ h ∧ ℓ z ≤ lam := by
    by_contra hc
    exact hznotint (by rw [hint]; exact ⟨hzbox, hc⟩)
  -- and `z` is outside the open slab or above the wall
  have hout : h ≤ |inner ℝ v z - (inner ℝ v c + u)| ∨ lam ≤ ℓ z := by
    have hsub : tiltedLevelRemoved s c σ u v h ℓ lam ⊆
        {y : R3 | h ≤ |inner ℝ v y - (inner ℝ v c + u)|} ∪ {y : R3 | lam ≤ ℓ y} := by
      rintro y ⟨hybox, hyrem⟩
      by_cases h1 : |inner ℝ v y - (inner ℝ v c + u)| ≤ h
      · refine Or.inr ?_
        by_contra h2
        refine hyrem ⟨show |inner ℝ v y - (inner ℝ v c + u)| ≤ h from h1,
          show ℓ y < lam from not_le.mp h2⟩
      · exact Or.inl (le_of_lt (not_le.mp h1))
    have hclosed : IsClosed ({y : R3 | h ≤ |inner ℝ v y - (inner ℝ v c + u)|} ∪
        {y : R3 | lam ≤ ℓ y}) :=
      (isClosed_le continuous_const
        ((continuous_const.inner continuous_id).sub continuous_const).abs).union
        (isClosed_Ici.preimage ℓ.continuous)
    have h1 : z ∈ ({y : R3 | h ≤ |inner ℝ v y - (inner ℝ v c + u)|} ∪
        {y : R3 | lam ≤ ℓ y}) := by
      have h2 := closure_mono hsub hzcl
      rwa [hclosed.closure_eq] at h2
    rcases h1 with h | h
    · simp only [Set.mem_ofPred_eq] at h
      exact Or.inl h
    · simp only [Set.mem_ofPred_eq] at h
      exact Or.inr h
  rcases hout with hbig | hbig
  · have heq : |inner ℝ v z - (inner ℝ v c + u)| = h := le_antisymm hzS.1 hbig
    exact Or.inl ⟨heq, hzS.2⟩
  · by_cases hh : |inner ℝ v z - (inner ℝ v c + u)| ≤ h
    · have heq : ℓ z = lam := le_antisymm hzS.2 hbig
      exact Or.inr ⟨heq, hh⟩
    · have hge : h ≤ |inner ℝ v z - (inner ℝ v c + u)| := le_of_lt (not_le.mp hh)
      have heq : |inner ℝ v z - (inner ℝ v c + u)| = h := le_antisymm hzS.1 hge
      exact Or.inl ⟨heq, hzS.2⟩

/-! ## The deliverable -/

/- (Removed: the unproved stub `TiltedTraceDataWExists_holds` stated here; nothing uses it.)
**The residual of the tilted sweep** (see `Submission/Work/Drive/Mono/Split.lean` and
`Submission/Work/Drive/Mono/Residual.lean`): at every crux configuration there exist tilt data `v, h,
R, ℓ, lam0, lam1, exc` satisfying `Work.Drive.Mono.TiltData` (the genericity of the sweep height on
the surface, the size conditions and the window conditions) together with
`Work.Drive.Mono.TiltedTraceDataW` — clause 1 (the trace of every non-exceptional level of the window
is a finite union of pairwise disjoint simple *inessential* closed curves equal to the frontier of the
level's removed set), clause 2 (every point of the surface in the closed box and closed slab at such a
level is in the closure of the level's region or on the level's trace), and clause 4 (at every
exceptional level, no level just below a level of vanishing span carries the full span).

The lemmas proved in this module are the fixed-datum consequences of the trace data that the assembly
`Work.Drive.Mono.tiltedSweepMono_of_traceDataWExists` uses only in the universally quantified form,
and the reduction of the residual to the geometric conditions of the design:

* `windingSpan_bot_or_top_of_traceCurvesAt` — Pardon's dichotomy `(D)` at a fixed datum, from clause 1;
* `windingSpan_end_ne_bot_of_tiltedTraceDataW`, `windingSpan_ne_bot_of_tiltedTraceDataW` — the
  infimum assembly at a fixed datum, and hence the *necessary condition* on any datum satisfying the
  trace data: the span of the sweep region does not vanish anywhere in the window.  In particular the
  fat-slab data of `Work.Drive.EpsForm.tiltedSweepGenericity_holds_sized` cannot witness the residual
  (`not_tiltedTraceDataW_of_slab_contains_box`), which is the machine-checked form of the diagnosis in
  the statement below;
* `traceCurvesAt_of_isLocallyEuclidean`, `not_containsEssentialLoop_frontier_of_counts` and
  `tiltedTraceDataW_of_geometric_hypotheses` — `(P1)`: clause 1 from the local structure of the trace
  and the level count, and the packaging of the whole residual into the four geometric conditions of
  the design (the data, the local structure, clause 2, clause 4);
* `traceCurvesAt_of_slab_disjoint_carrier` and `tiltedTraceDataW_of_slab_disjoint_carrier` — the trace
  data at a datum whose slab misses the surface, where both clauses are elementary (`exc = ∅`).

Route, in the order in which the pieces must be built.  **(P0) the data**: `Work.Drive.Mono.DataExists_holds`
(proved) supplies `TiltData` with the half-width `h = ε·R + R + |u| + 1`, whose slab strictly contains
the box; the data needed here have a *thin* slab (`Work.Drive.Mono.ThinSlabData_holds`), so that removing
the slab really carves a trench across the box — as `not_tiltedTraceDataW_of_slab_contains_box` shows,
the fat data cannot witness the trace data at all.  **(P1) clause 1**: the trace is a compact
`1`-manifold (local models), a finite family of disjoint simple curves
(`Work.EpsW.exists_family_of_isCompact_of_isLocallyEuclidean`, packaged as
`traceCurvesAt_of_isLocallyEuclidean`), and the curves are inessential by Pardon's second input at the
level count (`not_containsEssentialLoop_frontier_of_counts`).  **(P2) clause 2**: the stratified
genericity of the sweep height on the box sphere and inside the box.  **(P3) clause 4**: Pardon's
`2`-surgery count at the exceptional levels.

## State of the reduction (see `NOTES_H381_L547_state.md` for the full account)

The residual is now the obligation **(R)**: at every non-exceptional level of the window,

    ¬ ContainsEssentialLoop F (frontier (tiltedLevelRemoved s c σ u v h ℓ lam))

with clause 2 free from `TiltData + JunctionGen` (`aboveGenericAt_of_junctionGen`) and clause 4 free
from clauses 1 and 2 at the same level (`noJumpBelow_of_traceCurves`) — so the residual is
`TraceDataInputsL` of this module, or equivalently clause 1 everywhere with a suitably chosen `exc`.

Clause 1 at a level needs two inputs:

1. the *count* `encard (range K ∩ frontier (tiltedLevelRemoved …)) < min p q`.  It is at least the
   number of knot parameters whose point lies in the box and the *interior* of the slab at that level
   (`wallParamSet_subset_traceParamSet`, proved here), and those levels form an interval — so the
   finite exceptional set `exc` can never remove them.  The design's `hatt` (a *single* in-box slab
   visit of the knot, with `ℓ` monotone along it) makes the in-box contribution at most `4`; it is a
   condition on the *knot*, not derivable from `TiltData`.  The count from the three explicit pieces
   (box sphere, the two slab faces — which for `v = e_{σ2}` *are* the crux's shifted planes — and the
   wall) is `Work.Drive.Mono.encard_frontier_lt_min_of_face_wall` / `encard_frontier_chunk_lt_min`
   (delegated and proved), i.e. `hS + hfaces + hwall < min p q`;
2. a `SphereSlicing` of a set containing the trace with the same count.  At the bottom of the window
   it is `hslice` (the trace is `F ∩ ∂PBox`), above the `ℓ`-range it is the disjoint union of the two
   caps.  In the *middle* the level frontier is the box sphere with the chunk boundary sewn in along
   the seam, and the assembly through `∂PBox ∪ ∂C_λ` fails there (the two spheres' traces are not
   disjoint along the seam).  The correct shape is the *decomposition of the level frontier itself*
   into pairwise disjoint embedded spheres,
   `Work.Drive.Mono.traceCurvesAt_of_sphereDecomposition` (proved here) then gives clause 1 from the
   level count; supplying that decomposition for generic data is the remaining geometric obligation.

## State of the reduction (this session)

The case analysis of `level_trichotomy` shows that the removed set of a level depends on the level
only through the *convex* set `slabBox = PBox ∩ slabClosed`: either the wall `{ℓ = lam}` meets
`slabBox` (the middle regime), or it misses it, in which case the removed set is the whole box (its
frontier is the box sphere — clause 1 is `traceCurvesAt_at_window_bottom_slab`) or the box minus the
slab (its frontier is the two convex caps — clause 1 is `traceCurvesAt_at_window_top_slab`).  Hence
clause 1 at *every* level of the window reduces to the middle regime, where the geometric input is
exactly `Work.Drive.Mono.LevelSphereDecomposition` (`levelSphereDecomposition_of_cases`), which the
delegated brick `Work.Drive.Mono.tiltedLevel_disjoint_spheres` supplies (its remaining hypotheses —
the wall containing no box edge, passing through no vertex, and not tangent to the face seams — are
satisfied at all but finitely many levels and may be absorbed into `exc`).  The residual in this form
is `Work.Drive.Mono.TraceDataInputsS`, and the reduction is
`Work.Drive.Mono.TiltedTraceDataWExists_of_inputsS`.  The geometric input itself is *proved*:
`levelSphereDecomposition_of_levelFrontierGen` derives it from the explicit genericity
`Work.Drive.Mono.LevelFrontierGen` and the (proved) brick
`Work.Drive.Mono.tiltedLevel_disjoint_spheres`, and `levelSphereDecomposition_of_cases` supplies it at
the levels where the wall misses the box ∩ slab.  Hence the residual takes its final form
`Work.Drive.Mono.TraceDataInputsB`, with the reduction
`Work.Drive.Mono.TiltedTraceDataWExists_of_inputsB`; its obligations are the *stratified genericity of
the data* (`JunctionGen` and the face regularity — not produced anywhere yet — together with
`LevelFrontierGen`, whose offending levels are finitely many and explicit), the *count*
(`Work.Drive.Mono.ae_levelCount_lt_min` with the knot's non-grazing conditions,
`Work.Drive.Mono.exists_noGraze_tiltData` in flight) and clause 4 at the exceptional levels
(Pardon's `2`-surgery count — the pinch).

## State of the reduction (session H381-s9; full account in `NOTES_H381_s9_count_and_trivial_case.md`)

Two whole classes of obligation have since been removed from the residual, in the *downstream* modules
(this file cannot import them: they depend on it):

* **the level count is not an obligation**: `Mono/LevelCountTilted.lean` derives the level count of
  *every* level of the window from the crux's own two counted hypotheses together with the four
  knot-genericity conditions of the data and the crossing count of the data's own (tilted) slab plane
  (`Work.Drive.Mono.nat_arith_of_crux_counts`, `Work.Drive.Mono.levelCount_of_tiltedData`; the
  arithmetic `75d + 2·37.5d = 150d < min p q` is exactly tight), and records that
  `Work.Drive.Final.TiltedGenericity` is monotone in the half-width (`tiltedGenericity_mono_h`,
  `tiltData_mono_h`), so thin-slab data follow from the fat-slab upstream genericity modulo the face
  clause alone.  `Mono/TiltedTraceDataWExistsU.lean` states the residual `TraceDataInputsU` with the
  count removed (`TiltedTraceDataWExists_of_inputsU`);
* **the trivial case is proved**: `Mono/FlatMissData.lean` shows that when the chosen slab misses the
  surface's part in the closed box the genericity of the sweep is *vacuous*, the trace of every level
  is the box-sphere trace (`trace_eq_sphereSet_of_slab_misses`), the level regions are all equal, and
  the trace data hold with the empty exceptional set; `Mono/CuttingResidual.lean` turns this into
  `Work.Drive.Mono.TiltedTraceDataWExists_of_cuttingResidual`: it is enough to produce the data at the
  crux configurations at which the *flat* cutting plane meets the surface inside the closed box;
* `Mono/FleetResidual.lean` + `Mono/CuttingFleetResidual.lean` state the residual in the shape of the
  fleet's data producer (`Work.Drive.Mono.TraceDataInputsF`: `TiltData`, `JunctionGenC`, the face
  regularity, `SlabCutsBox`, `LevelFrontierGen`, `GrazeConditions`, the four knot-genericity
  conditions, the tilted crossing count and clause 4) and prove
  `Work.Drive.Mono.TiltedTraceDataWExists_of_cuttingInputsF`;
* `Mono/GrazeObstruction.lean` machine-checks the algebraic core of the graze obstruction
  (`Work.Drive.Mono.not_const_on_two_grazeFaces`, `lt_slabHeight_of_coord_eq_boxSide`).

The three obligations left are: the ∀-transfer for the producer's a.e.-`u` hypotheses, the graze
conditions at graze box levels, and the pinch at the exceptional levels — see §4 of the notes.

## State of the reduction (session H381-s10; full account in `NOTES_H381_s10_thinSlab_producer.md`)

The *data* conjuncts of the residual are now **produced**, at every cutting level and every box level,
with the thin slab which the trace data require — by the module `Mono/TiltDataSmallSlab.lean` (which
this file may not import: it imports `Mono/Band`, and it is used downstream).  Its content:

* `Work.Drive.Mono.exists_tiltData_smallSlab` — for every `η > 0` there are `v, h < η, R = 5/2*s, ℓ,
  lam0, lam1, exc` with `TiltData ψ s c σ u v h R ℓ exc lam0 lam1` and `h + |u| < boxWidth s σ v`;
* `Work.Drive.Mono.exists_tiltData_smallSlab_cuts` — the same with `‖v‖ = 1`, `0 < h` and
  `SlabCutsBox` exposed;
* `Work.Drive.Mono.exists_tiltData_smallSlab_levelFrontier` — the same with the exceptional set
  enlarged so that `LevelFrontierGen` holds (the geometric input of clause 1, via
  `Work.Drive.Mono.exists_levelFrontierGen`);
* `Work.Drive.Mono.exists_tiltData_smallSlab_faceReg` — the same with the face regularity `faceReg`
  of the slab faces (via `Work.Drive.Mono.tiltData_small_of_dir_near_junction`).

The producer has **no almost-everywhere hypothesis** on the cutting level `u` and **no
general-position hypothesis** on the box level `s` (the data of `Mono/LevelCountTilted.lean` and of
`Work.Drive.Final.noGraze_tiltData_exists` are `∀ᵐ u`; the fleet's geometric producers assume
`BoxGenE ψ c σ s`).  So the residual `Work.Drive.Mono.TraceDataInputsF`'s conjuncts `TiltData`,
`faceReg`, `SlabCutsBox`, `LevelFrontierGen` — and, through
`Work.Drive.Mono.levelSphereDecomposition_of_levelFrontierGen`, the disjoint-sphere decomposition of
the level frontier — are no longer obligations of the deliverable.  What remains is `JunctionGenE`
(the corrected junction bundle), `GrazeConditions`, the four knot-genericity conditions, the tilted
crossing count of the data's plane, and clause 4.

The same session analysed the **graze case** again and corrected the previous reading: `TiltData`
constrains `ℓ` only by `ℓ ≠ 0` and `ℓ v = 0`, so the level functional is *not* forced to be close to
the flat functional `e_{σ2}*`; at a torus of revolution tangent to the box top face along its top
circle there *is* a datum (`v = shiftVσ σ 1`, `ℓ` = the height functional) — so the obstruction feared
in session 9 does not materialise there.  What is genuinely necessary is (N1) of `GrazeConditions`
(no graze point of the box sphere on a slab face: the trace then has three branches at every level)
and, for a graze *curve* meeting the slab, that `ℓ` be constant along it (otherwise the trace has
three branches at the levels of its points, infinitely many of which cannot be absorbed by the finite
`exc`).  The residual obstruction is therefore a *pair* of graze curves in two different face planes,
both meeting the slab — exactly the case of `Work.Drive.Mono.not_const_on_two_grazeFaces`.  No
counterexample is available (a refutation would need a configuration satisfying all the crux's
hypotheses, in particular `hbound : IsDistortionBound K d` with `countConst·d < min p q`, i.e. an
*upper* bound on the distortion of a tight curve — the hard direction of Pardon's theorem), so the


## State of the reduction (session H381-s11; full account in `NOTES_H381_s11_forced_slab.md`)

**The forced slab visit of a box-sphere point, and why the count is only almost-everywhere in the
cutting level.**  At the cutting level `u := z₀ (σ 2) - c (σ 2)` of a point `z₀` of the box sphere,
*every* datum satisfying the size condition `‖v - e_{σ 2}‖ * R < h` of `TiltData` puts `z₀` strictly
inside the tilted slab (`abs_slabHeight_lt_h_of_coord_eq`), and hence the no-grazing conjunct

    hboxsph : ∀ t, boxNorm c σ (K.curve t) = s → h ≤ |⟪v, K.curve t⟫ - (⟪v, c⟫ + u)|

— the fifth knot-genericity conjunct of `Work.Drive.Mono.Geom2Data`, consumed by the whole visit
count of `Work.Drive.Mono.visit_facts` and by `Work.Drive.Mono.levelCount_lt_min_all` — is
**unsatisfiable for every datum** (`not_hboxsph_of_coord_eq`).  The counted data of the tilted sweep
are therefore an almost-everywhere object in the cutting level `u`: `hboxsph` in fact *implies* the
first conjunct of the fleet's general position hypothesis `Work.Drive.Mono.CutTransverse`
(`mem_PBox_of_hboxsph_of_coord_eq`).  Since the deliverable quantifies over *every* cutting level,
clause 1 at the levels above cannot be obtained from the level count, and the residual's two
remaining obligations are the *junction genericity* `JunctionGenE` (a finiteness obligation on the
levels at which the level curve of `ℓ` is tangent to the box-sphere trace — the necessity of the
condition is the "T" of the junction analysis, whose machine-checked form is the delegated
`Work.Drive.Mono.LocalEuclideanTrace_of_traceCurves`, clause 1 being a union of pairwise disjoint
simple curves) and the *graze conditions* `GrazeConditions`.  The companion module
`Submission/Work/Drive/Mono/SlabDisjointJunction.lean` records the case in which both vanish (the
slab misses the box-sphere trace) and that `Work.Drive.Mono.Geom2Data` is unsatisfiable at the
cutting levels above.

## State of the reduction (session H381-s25; full account in `NOTES_H381_s25_boxSphereTrace_complete.md`)

Three lemmas appended at the end of this file complete the box-sphere characterisation of session
H381-s24 (`Γ ∩ ({|⟪v,·⟫-(⟪v,c⟫+u)| ≥ h} ∪ {ℓ ≥ lam})`) in every case but one: a box-sphere point of
the surface *inside* the slab with `ℓ z = lam` is a trace point of its level
(`Work.Drive.Mono.mem_frontier_tiltedLevelRemoved_of_boxSphere_of_wall`, given an inward direction
of the box that preserves the slab height and increases `ℓ`), a box-sphere point inside the slab
*strictly above* the wall is a trace point with no genericity at all
(`Work.Drive.Mono.mem_frontier_tiltedLevelRemoved_of_boxSphere_of_above_wall`), and hence the knot's
*equator* point — a knot point of the box sphere whose flat height is the cutting height `u` — is a
point of the trace of its own level (`Work.Drive.Mono.knot_mem_trace_of_equator`).  The single
remaining case — `|⟪v,·⟫-(⟪v,c⟫+u)| = h` with `ℓ z < lam`, session H381-s24's corner case — is closed
for *generic* tilt directions in the downstream module
`Submission/Work/Drive/Mono/BoxSphereFaceBelowWall.lean`
(`Work.Drive.Mono.mem_frontier_tiltedLevelRemoved_of_boxSphere_of_face_of_below_wall_of_coord_ne`).  The latter is the trace-level form
of `Work.Drive.Mono.not_hboxsph_of_coord_eq`: at those cutting levels the visit count (hence the
level count from the crux's arithmetic, which is exactly tight) is unavailable, while the trace
really does contain the knot point — so clause 1 at the equator levels has to come from the
*geometric* route, not from counting.  The session also re-confirmed that the *wall* term of the
level count is not an obstruction (the machine-checked per-visit bound
`((facePtsLe ∪ wallPts) ∩ closure (visit …)).encard ≤ 2` of `Mono/visit_facts_le.lean`), and
corrected the shape of the geometric route: on the round torus with a thin horizontal plate the
*chunk* `belt ∩ {ℓ < lam}` is a pair of pants while the trace curves nonetheless bound the
*superlevel* lens discs — so "the chunk components are discs" is not the right spelling, and the
fibre-monotonicity condition of session H381-s24 §7 is not achievable on a 2-dimensional belt.

## State of the reduction (session H381-s24; full account in `NOTES_H381_s24_boxSphereTrace.md`)

**Clause 2 is free.**  The new module `Submission/Work/Drive/Mono/BoxSphereTrace.lean` proves that a
point of the box sphere of the surface is a point of the *frontier* of the level's removed set as
soon as there is a direction which is both inward for the box and `ℓ`-increasing, and that such a
direction exists unless `ℓ` is a multiple of the active face's coordinate functional; on the edges
and corners `EdgeFree` excludes the clause-2 hypothesis.  Consequently
(`Submission/Work/Drive/Mono/Clause2EdgeFree.lean`)

* `Work.Drive.Mono.aboveGenericAt_of_tiltData_edgeFree` — clause 2 follows from `TiltData` plus
  `Work.Drive.Mono.EdgeFree` and `Work.Drive.Mono.CoordFree ℓ σ` (the latter being automatic when the
  tilt direction has all its `σ`-coordinates nonzero);
* `Work.Drive.Mono.tiltedTraceDataW_of_clause1_clause4` — the trace data of the window reduce to
  **clause 1 and clause 4 alone**.

So `JunctionGenE` and `GrazeConditions` are obligations of clause 1 alone (the local models of the
trace at its junctions), and the residual's clause-2 obligation is replaced by two *data choices*
which the thin-slab producer already satisfies.  (`Submission/Work/Drive/Mono/TraceCurvesSimplyConnected.lean`
adds the matching interface for clause 1: `Work.Drive.Mono.traceCurvesAt_of_simplyConnected` produces
clause 1 from a family of simple curves each lying in a simply connected piece of the surface, and
`Work.Drive.Mono.mem_frontier_tiltedLevelRemoved_iff_of_mem_PBox` identifies the in-box part of the
trace with the frontier of the removed chunk.)  The same module computes the box-sphere part of the
trace:

    carrier ∩ frontier (tiltedLevelRemoved … lam)
      = Γ ∩ ({|slabFn| = h} ∪ {ℓ ≥ lam})  ∪  (carrier ∩ PBox ∩ ∂K),

i.e. *arcs* of the box-sphere trace `Γ` cut by the wall together with the in-box part (the relative
frontier of the chunk `carrier ∩ PBox ∩ slabClosed ∩ {ℓ < lam}`); and it proves the matching failure
case (`Work.Drive.Mono.not_aboveGenericAt_of_bad_coord`): if `ℓ` is a bad multiple of a coordinate
functional, clause 2 fails, so the coordinate-freeness is necessary and the tilt direction must have
all its `σ`-coordinates nonzero.

## State of the reduction (session H381-s23; full account in `NOTES_H381_s23_forallGap.md`)

The residual is *strictly stronger* than the project needs: through the proved bridges
(`Mono/BridgeDataPackage.lean`) it is equivalent to the **universally quantified** form of the
fleet's data producer together with the no-jump, whereas the fleet's live route
(`Work.Drive.Mono.CruxCoreWdAEG2`, `Mono/Bridges2.lean`) is almost-everywhere in the cutting level
`u` and in the box level `s`.  This session machine-checked where the difference bites:

* `Work.Drive.Mono.one_le_encard_boxSphere_openSlab` — at the cutting level of a knot point `z₀` of
  the box sphere, the set of knot parameters whose point lies on the box sphere *inside* the tilted
  slab is nonempty **for every datum**;
* the delegated and proved `Work.Drive.Mono.levelCount_lt_min_all_of_boxSphereSlabPts`
  (`Mono/levelCount_lt_min_all_of_boxSphereSlabPts.lean`) derives the level count from the slack
  arithmetic `A + 2 * B + 4 * k < min p q` instead of the unsatisfiable `hboxsph`, and its sharp
  form `Work.Drive.Mono.levelCount_lt_min_all_of_boxSphereSlabPts_trans` improves the slack to
  `2 * k` under the transversality of `boxA`;
* the new residual `Work.Drive.Mono.TraceDataInputsV` / `TraceDataInputsVt`
  (`Mono/TraceDataInputsV.lean`) and the assemblies `TiltedTraceDataWExists_of_inputsV` /
  `..._of_inputsVt` reduce the whole obligation at those levels to that arithmetic.

The remaining gaps are (R1) the ∀`s` junction genericity (`JunctionGenE` at *every* box level; the
fleet's producers give it only under `BoxGen ψ c σ s`, i.e. a.e. in `s`), (R2) the forced slack at
the cutting levels of the knot's box-sphere points (two units in the sharp form, while the crux's
arithmetic `countConst * d = 150 * d < min p q` is exactly tight), (R3) the graze conditions, and
(R4) clause 4 at the exceptional levels (Pardon's `2`-surgery count, the fleet's field `(L)`).

-/



/- ## The two ends of the window, and the trichotomy

At a level `lam` the removed set is `PBox ∖ (slabClosed ∩ {ℓ < lam})`: it depends on `lam` only
through the part `slabBox := PBox ∩ slabClosed` of the box that the slab sees.  If the wall
`{ℓ = lam}` misses `slabBox`, the removed set is *independent of the level*:

* on the side `lam ≤ ℓ` of `slabBox` the removed set is the whole box, its frontier is the box
  sphere, and clause 1 is `Work.Drive.Mono.traceCurvesAt_at_window_bottom_slab` (`hslice` + the
  box-sphere count);
* on the side `ℓ < lam` of `slabBox` the removed set is `PBox ∖ slabClosed`, its frontier is the two
  caps of the box cut by the slab, and clause 1 is
  `Work.Drive.Mono.traceCurvesAt_at_window_top_slab`.

`slabBox` is convex, hence connected, so `ℓ` maps it to an interval: at every level either the wall
meets `slabBox`, or the wall sits strictly above it, or strictly below it
(`Work.Drive.Mono.level_trichotomy`).  Consequently clause 1 at *every* level of the window is
reduced to the single middle case — the geometry of the level frontier at the levels where the wall
really cuts the slab, which is the input `Work.Drive.Mono.LevelSphereDecomposition` below. -/

/-- The part of the box that the level of the sweep can see: the box intersected with the closed
tilted slab. -/
def slabBox (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ) : Set R3 :=
  Submission.PBox s c σ ∩ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h

/-- The closed tilted slab is convex. -/
theorem convex_tiltedSlabClosed (a : ℝ) (v : R3) (h : ℝ) :
    Convex ℝ (Work.Drive.EpsForm.tiltedSlabClosed a v h) := by
  have hset : Work.Drive.EpsForm.tiltedSlabClosed a v h =
      {y : R3 | inner ℝ v y ≤ a + h} ∩ {y : R3 | a - h ≤ inner ℝ v y} := by
    ext y
    simp only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro hy
      exact ⟨by linarith [(abs_le.mp hy).2], by linarith [(abs_le.mp hy).1]⟩
    · intro hy
      exact abs_le.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩
  rw [hset]
  exact (convex_setOf_inner_le v (a + h)).inter (convex_setOf_le_inner v (a - h))

/-- The box intersected with the closed slab is convex. -/
theorem convex_slabBox (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ) :
    Convex ℝ (slabBox s c σ u v h) :=
  (Work.Topology.SphereSlicing.convex_PBox s c σ).inter (convex_tiltedSlabClosed _ _ _)

/-- **The trichotomy of the level against the wall on `PBox ∩ slabClosed`.**  At every level, either
the wall `{ℓ = lam}` meets the box ∩ slab, or it misses it on the low side, or on the high side. -/
theorem level_trichotomy {s u h : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3}
    {ℓ : R3 →L[ℝ] ℝ} (lam : ℝ) :
    (∃ y ∈ slabBox s c σ u v h, ℓ y = lam) ∨
      (∀ y ∈ slabBox s c σ u v h, ℓ y < lam) ∨
      (∀ y ∈ slabBox s c σ u v h, lam ≤ ℓ y) := by
  by_cases h1 : ∃ y ∈ slabBox s c σ u v h, ℓ y = lam
  · exact Or.inl h1
  simp only [not_exists, not_and] at h1
  by_cases h2 : ∃ y ∈ slabBox s c σ u v h, lam ≤ ℓ y
  · by_cases h3 : ∃ y ∈ slabBox s c σ u v h, ℓ y < lam
    · exfalso
      obtain ⟨y₁, hy₁, hle⟩ := h2
      obtain ⟨y₂, hy₂, hlt⟩ := h3
      have hgt : lam < ℓ y₁ := lt_of_le_of_ne hle (fun hh => h1 y₁ hy₁ hh.symm)
      set g : ℝ → ℝ := fun t => ℓ (y₂ + t • (y₁ - y₂)) with hgdef
      have hgcont : Continuous g :=
        ℓ.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
      have hsub : Set.Icc (g 0) (g 1) ⊆ g '' Set.Icc (0 : ℝ) 1 :=
        intermediate_value_Icc (by norm_num) hgcont.continuousOn
      have hg0 : g 0 = ℓ y₂ := by simp [hgdef]
      have hg1 : g 1 = ℓ y₁ := by simp [hgdef]
      have hmem : lam ∈ Set.Icc (g 0) (g 1) := by
        rw [hg0, hg1]; exact ⟨le_of_lt hlt, le_of_lt hgt⟩
      obtain ⟨t, ht, hgt'⟩ := hsub hmem
      have hconv := convex_slabBox (s := s) (c := c) (σ := σ) (u := u) (v := v) (h := h)
      have hmemS : (1 - t) • y₂ + t • y₁ ∈ slabBox s c σ u v h :=
        hconv hy₂ hy₁ (by linarith [ht.2]) ht.1 (by ring)
      have heq : (1 - t) • y₂ + t • y₁ = y₂ + t • (y₁ - y₂) := by module
      exact h1 _ hmemS (by rw [heq]; exact hgt')
    · push_neg at h3
      exact Or.inr (Or.inr h3)
  · push_neg at h2
    exact Or.inr (Or.inl h2)

/-- **Below the level on the box ∩ slab the removed set is the whole box.** -/
theorem tiltedLevelRemoved_eq_PBox_of_slab_le
    (hle : ∀ y ∈ slabBox s c σ u v h, lam ≤ ℓ y) :
    tiltedLevelRemoved s c σ u v h ℓ lam = Submission.PBox s c σ := by
  ext y
  rw [tiltedLevelRemoved]
  simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · exact fun h' => h'.1
  · intro hy
    exact ⟨hy, fun hc => absurd (hle y ⟨hy, hc.1⟩) (not_le.mpr hc.2)⟩

/-- **Above the level on the box ∩ slab the removed set is the box minus the slab.** -/
theorem tiltedLevelRemoved_eq_sdiff_of_slab_lt
    (hlt : ∀ y ∈ slabBox s c σ u v h, ℓ y < lam) :
    tiltedLevelRemoved s c σ u v h ℓ lam =
      Submission.PBox s c σ \ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h := by
  ext y
  rw [tiltedLevelRemoved]
  simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hy, hrem⟩
    exact ⟨hy, fun hslab => hrem ⟨hslab, hlt y ⟨hy, hslab⟩⟩⟩
  · rintro ⟨hy, hnot⟩
    exact ⟨hy, fun hcon => hnot hcon.1⟩

/-- **Clause 1 below the level on the box ∩ slab** (the bottom of the window): the removed set is the
whole box, the frontier is the box sphere, and the given slicing of the box sphere together with the
crux's box-sphere count gives the clause. -/
theorem traceCurvesAt_at_window_bottom_slab
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hslice : Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
      {y : R3 | Submission.boxNorm c σ y = s})
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
    {u : ℝ} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    (hlam : ∀ y ∈ slabBox s c σ u v h, lam ≤ ℓ y) :
    TraceCurvesAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam := by
  have hrem : tiltedLevelRemoved s c σ u v h ℓ lam = Submission.PBox s c σ :=
    tiltedLevelRemoved_eq_PBox_of_slab_le hlam
  have hfr : frontier (tiltedLevelRemoved s c σ u v h ℓ lam) =
      {y : R3 | Submission.boxNorm c σ y = s} := by
    rw [hrem, Work.Topology.SphereSlicing.frontier_PBox hs c σ]
    rfl
  have hnoess : ¬ (Work.Drive.EpsSphere.torusOf ψ).ContainsEssentialLoop
      ({y : R3 | Submission.boxNorm c σ y = s}) :=
    Work.EpsW.sphereTrace_inessential_of_countsWd p q hp hq hc ψ K hd himg hsmall hs c σ
      hslice hcl hcount
  obtain ⟨Sl⟩ := hslice
  exact traceCurvesAt_of_slicing (S := {y : R3 | Submission.boxNorm c σ y = s}) Sl hnoess hfr.symm

/-- **Clause 1 above the level on the box ∩ slab**: the removed set is `PBox ∖ slabClosed`, whose
frontier is the union of the frontiers of the two caps of the box cut by the slab
(`Work.Drive.Mono.frontier_PBox_sdiff_slab_eq_caps`); each cap is convex, hence its frontier is an
embedded sphere (`Work.Drive.Mono.isEmbeddedSphere_frontier_slabCaps`), the two are disjoint, and the
trace curves of the level furnish the family which `sphereSlicing_union_of_curveFamily` assembles
into a slicing. -/
theorem traceCurvesAt_at_window_top_slab {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    (hs : 0 < s) (hhigh : ∀ y ∈ slabBox s c σ u v h, ℓ y < lam) (hh : 0 < h) (hv : v ≠ 0)
    (hcut : SlabCutsBox s c σ (inner ℝ v c + u) h v)
    (hcomp : IsCompact ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))
    (hloc : Work.Smooth.OneManifold.IsLocallyEuclidean
      ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))
    (hcount : Set.encard (Set.range K.curve ∩
      frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞)) :
    TraceCurvesAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam := by
  have hfr : frontier (Submission.PBox s c σ \
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) =
      frontier (slabCapPlus s c σ (inner ℝ v c + u) h v) ∪
        frontier (slabCapMinus s c σ (inner ℝ v c + u) h v) :=
    frontier_PBox_sdiff_slab_eq_caps s c σ (inner ℝ v c + u) h hh hv
  have hfr2 : frontier (tiltedLevelRemoved s c σ u v h ℓ lam) =
      frontier (slabCapPlus s c σ (inner ℝ v c + u) h v) ∪
        frontier (slabCapMinus s c σ (inner ℝ v c + u) h v) := by
    rw [tiltedLevelRemoved_eq_sdiff_of_slab_lt hhigh]
    exact hfr
  have hsph := isEmbeddedSphere_frontier_slabCaps s c σ (inner ℝ v c + u) h hs hh hv hcut
  obtain ⟨n, cs, hsimple, hdisj, hZ⟩ :=
    Work.EpsW.exists_family_of_isCompact_of_isLocallyEuclidean
      (P := Work.Drive.EpsSphere.torusOf ψ)
      (Z := (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam))
      Set.inter_subset_left hcomp hloc
  have hcover : (frontier (slabCapPlus s c σ (inner ℝ v c + u) h v) ∪
      frontier (slabCapMinus s c σ (inner ℝ v c + u) h v)) ∩
      (Work.Drive.EpsSphere.torusOf ψ).carrier = ⋃ i, Set.range (cs i).γ := by
    rw [← hfr2, Set.inter_comm]
    exact hZ
  obtain ⟨SlU⟩ := sphereSlicing_union_of_curveFamily (P := Work.Drive.EpsSphere.torusOf ψ)
    hsph.1 hsph.2 isClosed_frontier isClosed_frontier
    (disjoint_frontier_slabCaps (s := s) (c := c) (σ := σ) (v := v) hh) hsimple hdisj hcover
  refine traceCurvesAt_of_isLocallyEuclidean_of_counts p q hp hq hc ψ K himg hcl hcomp hloc
    ?_ hcount
  rw [hfr2]
  exact SlU

/- ## Clause 1 from a decomposition of the level frontier into disjoint embedded spheres -/

/-- **Each member of a disjoint sphere decomposition of the level frontier meets the surface in a
`1`-manifold.**  The trace is the disjoint union of the `Ss i ∩ P.carrier`; each member is closed
(it is an embedded sphere) and so is the union of the others, so `Ss i` is open in the frontier, and
near a point of the member its trace coincides with the whole trace, which is locally Euclidean. -/
theorem isLocallyEuclidean_sphereDecomposition_member
    {P : Work.CoreTopology.ParamTorus} {S : Set R3} {m : ℕ} {Ss : Fin m → Set R3}
    (hdecomp : S = ⋃ i, Ss i)
    (hdisj : ∀ i j : Fin m, i ≠ j → Disjoint (Ss i) (Ss j))
    (hsph : ∀ i : Fin m, Work.InnermostDisk.IsEmbeddedSphere (Ss i))
    (hloc : Work.Smooth.OneManifold.IsLocallyEuclidean (S ∩ P.carrier))
    (i : Fin m) : Work.Smooth.OneManifold.IsLocallyEuclidean (Ss i ∩ P.carrier) := by
  have hcl : ∀ j : Fin m, IsClosed (Ss j) := by
    intro j
    obtain ⟨e, -, he⟩ := hsph j
    rw [← he]
    exact (isCompact_range e.continuous).isClosed
  have hclosed_others : IsClosed (⋃ j ∈ (Finset.univ.filter (fun j : Fin m => j ≠ i)), Ss j) :=
    isClosed_biUnion_finset (fun j _ => hcl j)
  have hUopen : IsOpen ((⋃ j ∈ (Finset.univ.filter (fun j : Fin m => j ≠ i)), Ss j)ᶜ) :=
    hclosed_others.isOpen_compl
  have hSU : S ∩ ((⋃ j ∈ (Finset.univ.filter (fun j : Fin m => j ≠ i)), Ss j)ᶜ) = Ss i := by
    apply Subset.antisymm
    · rintro x ⟨hxS, hxU⟩
      rw [hdecomp] at hxS
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxS
      by_contra hji
      have hji' : j ≠ i := fun hji'' => hji (hji'' ▸ hxj)
      exact hxU (Set.mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hji'⟩, hxj⟩)
    · intro x hx
      exact ⟨by rw [hdecomp]; exact Set.mem_iUnion.mpr ⟨i, hx⟩, by
        rw [Set.mem_compl_iff, Set.mem_iUnion₂]
        rintro ⟨j, hj, hxj⟩
        exact (Set.disjoint_left.mp
          (hdisj i j (Ne.symm (Finset.mem_filter.mp hj).2))) hx hxj⟩
  refine Work.Smooth.OneManifold.IsLocallyEuclidean.of_isOpenIn ?_ ?_ hloc
  · intro x hx
    have h1 : (x : R3) ∈ S ∩ (⋃ j ∈ (Finset.univ.filter (fun j : Fin m => j ≠ i)), Ss j)ᶜ := by
      rw [hSU]; exact hx.1
    exact ⟨h1.1, hx.2⟩
  · show IsOpen ((Subtype.val ⁻¹' (Ss i ∩ P.carrier) : Set ↥(S ∩ P.carrier)))
    have hset : (Subtype.val ⁻¹' (Ss i ∩ P.carrier) : Set ↥(S ∩ P.carrier)) =
        Subtype.val ⁻¹' ((⋃ j ∈ (Finset.univ.filter (fun j : Fin m => j ≠ i)), Ss j)ᶜ) := by
      ext x
      constructor
      · intro hx
        have h1 : (x : R3) ∈ S ∩
            (⋃ j ∈ (Finset.univ.filter (fun j : Fin m => j ≠ i)), Ss j)ᶜ := by
          rw [hSU]; exact hx.1
        exact h1.2
      · intro hx
        exact ⟨by rw [← hSU]; exact ⟨x.2.1, hx⟩, x.2.2⟩
    rw [hset]
    exact hUopen.preimage continuous_subtype_val

/-- **Clause 1 from a decomposition of the level frontier into pairwise disjoint embedded spheres,
with the local structure of the trace as the only local input.**  This is
`Work.Drive.Mono.traceCurvesAt_of_sphereDecomposition` with the compactness and the local Euclidean
structure of each member of the decomposition *derived* from the decomposition and from the pointwise
local structure of the trace (`Work.Drive.Mono.isLocallyEuclidean_sphereDecomposition_member`). -/
theorem traceCurvesAt_of_sphereDecomposition'
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u h lam : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ}
    {m : ℕ} {Ss : Fin m → Set R3}
    (hcomp : IsCompact ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (tiltedLevelRemoved s c σ u v h ℓ lam)))
    (hloc : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam) →
      ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
        Work.Smooth.OneManifold.IsLocallyEuclidean
          (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
            frontier (tiltedLevelRemoved s c σ u v h ℓ lam))))
    (hdecomp : frontier (tiltedLevelRemoved s c σ u v h ℓ lam) = ⋃ i, Ss i)
    (hdisj : ∀ i j : Fin m, i ≠ j → Disjoint (Ss i) (Ss j))
    (hsph : ∀ i : Fin m, Work.InnermostDisk.IsEmbeddedSphere (Ss i))
    (hcount : Set.encard (Set.range K.curve ∩
      frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞)) :
    TraceCurvesAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam := by
  refine traceCurvesAt_of_sphereDecomposition p q hp hq hc ψ K himg hcl hcomp hloc hdecomp hdisj
    hsph ?_ ?_ hcount
  · intro i
    obtain ⟨e, -, he⟩ := hsph i
    have hcomp' : IsCompact (Ss i) := by
      rw [← he]
      exact isCompact_range e.continuous
    exact hcomp'.inter_right
      (Work.Smooth.Morse.Surface.isCompact_torus ψ).isClosed
  · intro i
    refine isLocallyEuclidean_sphereDecomposition_member (P := Work.Drive.EpsSphere.torusOf ψ)
      (S := frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) hdecomp hdisj hsph ?_ i
    rw [Set.inter_comm]
    exact isLocallyEuclidean_trace_of_local_models hloc

/- ## Clause 1 at every level of the window, and the residual in this form -/

/-- **The geometric input of clause 1**: at every non-exceptional level of the window, the frontier of
the level's removed set is a finite disjoint union of pairwise disjoint embedded spheres.
`Work.Drive.Mono.tiltedLevel_disjoint_spheres` supplies it at every level at which its genericity
hypotheses hold (all but finitely many — those levels go into `exc`), and at the levels where the wall
misses `PBox ∩ slabClosed` the frontier is one of the two λ-independent surfaces (`∂PBox` at the
bottom, the two caps at the top), whose decomposition is given by
`Work.Drive.Mono.isEmbeddedSphere_frontier_of_convex`. -/
def LevelSphereDecomposition (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ) : Prop :=
  ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
    ∃ (n : ℕ) (S : Fin n → Set R3),
      (∀ i, Work.InnermostDisk.IsEmbeddedSphere (S i)) ∧
      (∀ i j : Fin n, i ≠ j → Disjoint (S i) (S j)) ∧
      frontier (tiltedLevelRemoved s c σ u v h ℓ lam) = ⋃ i, S i

/-- **Clause 1 at every non-exceptional level of the window** from the data conditions (`TiltData`,
`JunctionGen`, the face regularity), the slicing of the box sphere, the geometric input
`LevelSphereDecomposition` and the *level count*.  The pointwise local models of the trace come from
`Work.Drive.Mono.trace_localModels_of_junctionGen`, the compactness from
`Work.Drive.Mono.isCompact_trace_torusOf`, and the rest is
`Work.Drive.Mono.traceCurvesAt_of_sphereDecomposition'`. -/
theorem traceCurvesAt_of_levelSphereDecomposition
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    {exc : Finset ℝ} {lam0 lam1 : ℝ} (hs : 0 < s)
    (hT : TiltData ψ s c σ u v h R ℓ exc lam0 lam1)
    (hJ : JunctionGenC ψ s c σ u v h ℓ exc lam0 lam1)
    (hfaceReg : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ Submission.PBox s c σ → |inner ℝ v z - (inner ℝ v c + u)| = h →
      ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0)
    (hslice : Nonempty (Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
      {y : R3 | Submission.boxNorm c σ y = s}))
    (hD : LevelSphereDecomposition ψ s c σ u v h ℓ exc lam0 lam1)
    (hcount : ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
      Set.encard (Set.range K.curve ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞)) :
    ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
      TraceCurvesAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam := by
  intro lam hlam hne
  obtain ⟨n, Ss, hsph, hdisj, hdecomp⟩ := hD lam hlam hne
  refine traceCurvesAt_of_sphereDecomposition' p q hp hq hc ψ K himg hcl
    (isCompact_trace_torusOf ψ s u c σ v h ℓ lam) ?_ hdecomp hdisj hsph (hcount lam hlam hne)
  exact trace_localModels_of_junctionGenC hs hslice hfaceReg hT hJ hlam hne

/-- **The trace data of the window from the data conditions, the geometric input and the count.** -/
theorem tiltedTraceDataW_of_levelSphereDecomposition
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    {exc : Finset ℝ} {lam0 lam1 : ℝ} (hs : 0 < s)
    (hT : TiltData ψ s c σ u v h R ℓ exc lam0 lam1)
    (hJ : JunctionGenC ψ s c σ u v h ℓ exc lam0 lam1)
    (hfaceReg : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ Submission.PBox s c σ → |inner ℝ v z - (inner ℝ v c + u)| = h →
      ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0)
    (hslice : Nonempty (Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
      {y : R3 | Submission.boxNorm c σ y = s}))
    (hD : LevelSphereDecomposition ψ s c σ u v h ℓ exc lam0 lam1)
    (hcount : ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
      Set.encard (Set.range K.curve ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞))
    (h4 : ∀ lam ∈ Set.Icc lam0 lam1, lam ∈ (exc : Set ℝ) →
      NoJumpBelowAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) :
    TiltedTraceDataW (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ exc lam0 lam1 :=
  ⟨traceCurvesAt_of_levelSphereDecomposition p q hp hq hc ψ K himg hcl hs hT hJ hfaceReg hslice
      hD hcount,
   fun lam hl hne => aboveGenericAt_of_junctionGenC hs hT hJ hl hne,
   h4⟩

/-- **The inputs of the residual, in the form in which the geometry of the level frontier is
attacked**: the data conditions of the design, the geometric input
`LevelSphereDecomposition`, the level count and clause 4 at the exceptional levels.

**Note on the stratified genericity.**  The bundle used here is the *corrected*
`Work.Drive.Mono.JunctionGenC` (clause (c) restricted to the closed slab): the older bundle
`Work.Drive.Mono.JunctionGen` is **not satisfiable** in general
(`Submission/Work/Drive/Mono/NOTES_JunctionGen_OBSTRUCTIONS.md`), so the residual `TraceDataInputsL`
and `TraceDataInputsW` of this file (and hence their chains) describe an empty class of data; they are
kept for compatibility, and the same assembly with the corrected bundle is
`Work.Drive.Mono.traceCurvesAt_of_levelSphereDecomposition` below (via
`Work.Drive.Mono.trace_localModels_of_junctionGenC` and
`Work.Drive.Mono.aboveGenericAt_of_junctionGenC`).  Compared with
`TraceDataInputsL` this replaces the *inessentiality* of the level frontier at every level by the
disjoint-sphere decomposition (which is a statement about the frontier alone, independent of the
surface) plus the level count (which is available from the knot's general position, e.g.
`Work.Drive.Mono.ae_levelCount_lt_min`). -/
def TraceDataInputsS (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ) (p q : ℕ)
    (K : Knot) : Prop :=
  TiltData ψ s c σ u v h R ℓ exc lam0 lam1 ∧
  JunctionGenC ψ s c σ u v h ℓ exc lam0 lam1 ∧
  (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → z ∈ Submission.PBox s c σ →
    |inner ℝ v z - (inner ℝ v c + u)| = h →
    ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0) ∧
  LevelSphereDecomposition ψ s c σ u v h ℓ exc lam0 lam1 ∧
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
    Set.encard (Set.range K.curve ∩
      frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞)) ∧
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∈ (exc : Set ℝ) →
    NoJumpBelowAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam)

/-- **The residual from the data conditions, the disjoint-sphere geometry of the level frontier and
the level count**: `TiltedTraceDataWExists` follows as soon as at every crux configuration there are
data satisfying `TraceDataInputsS`. -/
theorem TiltedTraceDataWExists_of_inputsS
    (H : ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
      (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (hd : 0 ≤ d),
      Work.Sweep.IsDistortionBound K d →
      Set.range K.curve = Set.range
        (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
          (Work.CoreTopology.standardCurve p q)).γ →
      Submission.countConst * d < (Nat.min p q : ℝ) →
      Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ) →
      ∀ (r : ℝ) (hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
        Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ →
        ∀ (s : ℝ) (hrs : r < s) (hs : s < (1 + Submission.eps) * r),
          Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
              {y : R3 | Submission.boxNorm c σ y = s} →
          ∀ (u : ℝ) (hu : |u| < Submission.eps * r),
            ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
                Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
              ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
            ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
                K.curve t ∈ Submission.PBox s c σ ∧
                (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
              ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
            ∃ (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
              TraceDataInputsS ψ s c σ u v h R ℓ exc lam0 lam1 p q K) :
    Work.Drive.Mono.TiltedTraceDataWExists := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  obtain ⟨v, h, R, ℓ, lam0, lam1, exc, hI⟩ :=
    H p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  exact ⟨v, h, R, ℓ, lam0, lam1, exc, hI.1,
    tiltedTraceDataW_of_levelSphereDecomposition p q hp hq hc ψ K himg hcl (lt_trans hr hrs)
      hI.1 hI.2.1 hI.2.2.1 hslice hI.2.2.2.1 hI.2.2.2.2.1 hI.2.2.2.2.2⟩
/- ## The geometric input from the two regimes of the level -/

/-- **The geometric input `LevelSphereDecomposition` from its two regimes.**  `hwall` is the
conclusion of `Work.Drive.Mono.tiltedLevel_disjoint_spheres` at the levels where the wall meets
`PBox ∩ slabClosed` (all the hypotheses of that lemma being part of the data conditions); at the
levels where the wall misses `PBox ∩ slabClosed` the level has a side (`level_trichotomy`), the
removed set is one of the two λ-independent surfaces, and the decomposition is given by convexity:
`PBox` below the level (frontier the box sphere, an embedded sphere since the box is convex,
bounded, with nonempty interior) and `PBox ∖ slabClosed` above it (frontier the two caps, each
convex). -/
theorem levelSphereDecomposition_of_cases {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} (hs : 0 < s) (hh : 0 < h) (hv : v ≠ 0)
    (hcut : SlabCutsBox s c σ (inner ℝ v c + u) h v)
    (hwall : ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
      (∃ y ∈ slabBox s c σ u v h, ℓ y = lam) →
      ∃ (n : ℕ) (S : Fin n → Set R3),
        (∀ i, Work.InnermostDisk.IsEmbeddedSphere (S i)) ∧
        (∀ i j : Fin n, i ≠ j → Disjoint (S i) (S j)) ∧
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam) = ⋃ i, S i) :
    LevelSphereDecomposition ψ s c σ u v h ℓ exc lam0 lam1 := by
  intro lam hlam hne
  by_cases hmeet : ∃ y ∈ slabBox s c σ u v h, ℓ y = lam
  · exact hwall lam hlam hne hmeet
  rcases level_trichotomy (s := s) (u := u) (h := h) (c := c) (σ := σ) (v := v) (ℓ := ℓ) lam with
    h' | hlt | hle
  · exact absurd h' hmeet
  · -- above the level on the box ∩ slab: the two caps
    refine ⟨2, ![frontier (slabCapPlus s c σ (inner ℝ v c + u) h v),
        frontier (slabCapMinus s c σ (inner ℝ v c + u) h v)], ?_, ?_, ?_⟩
    · intro i
      have h2 := isEmbeddedSphere_frontier_slabCaps s c σ (inner ℝ v c + u) h hs hh hv hcut
      fin_cases i
      · exact h2.1
      · exact h2.2
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · simpa using disjoint_frontier_slabCaps (s := s) (c := c) (σ := σ) (v := v) hh
      · simpa using (disjoint_frontier_slabCaps (s := s) (c := c) (σ := σ) (v := v) hh).symm
      · exact absurd rfl hij
    · rw [tiltedLevelRemoved_eq_sdiff_of_slab_lt hlt,
        frontier_PBox_sdiff_slab_eq_caps s c σ (inner ℝ v c + u) h hh hv]
      ext x
      simp only [Set.mem_union, Set.mem_iUnion, Matrix.cons_val_zero, Matrix.cons_val_one,
        Fin.exists_fin_two]
  · -- below the level on the box ∩ slab: the box sphere
    refine ⟨1, fun _ => Work.BoxShrink.Core.sphereSet c σ s, ?_, ?_, ?_⟩
    · intro i
      have h2 : Work.InnermostDisk.IsEmbeddedSphere
          (Work.Topology.SphereSlicing.BoxSphere s c σ) :=
        Work.Topology.SphereSlicing.isEmbeddedSphere_BoxSphere hs c σ
      rwa [Work.BoxShrink.Core.sphereSet_eq_BoxSphere]
    · intro i j hij
      exact absurd (Subsingleton.elim i j) hij
    · rw [tiltedLevelRemoved_eq_PBox_of_slab_le hle,
        Work.Topology.SphereSlicing.frontier_PBox hs c σ]
      ext x
      simp

/- ## The geometric input from the brick, and the residual in its final form -/

/-- **The geometric input `LevelSphereDecomposition` from the brick.**  At the levels where the wall
meets `PBox ∩ slabClosed` the frontier is the disjoint union of embedded spheres supplied by the
(proved) `Work.Drive.Mono.tiltedLevel_disjoint_spheres`; at the other levels it is one of the two
λ-independent surfaces (`levelSphereDecomposition_of_cases`). -/
theorem levelSphereDecomposition_of_levelFrontierGen {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} (hs : 0 < s) (hT : TiltData ψ s c σ u v h R ℓ exc lam0 lam1)
    (hcut : SlabCutsBox s c σ (inner ℝ v c + u) h v)
    (hgen : LevelFrontierGen s c σ u v h ℓ exc lam0 lam1) :
    LevelSphereDecomposition ψ s c σ u v h ℓ exc lam0 lam1 := by
  obtain ⟨-, hv1, hℓne, hℓv, -, hh, -, -, -, -, -⟩ := hT
  have hv0 : v ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hv1
    exact absurd hv1.symm (by norm_num)
  refine levelSphereDecomposition_of_cases hs hh hv0 hcut ?_
  intro lam hlam hne hmeet
  obtain ⟨he, hvx, hse⟩ := hgen lam hlam hne
  exact tiltedLevel_disjoint_spheres s c σ u v h ℓ lam hv1 hh hℓv hℓne he hvx hse

/-- **The inputs of the residual, in their final form**: the data conditions of the design, the
genericity of the level frontier (`LevelFrontierGen`, which with the *proved*
`Work.Drive.Mono.tiltedLevel_disjoint_spheres` yields the geometric input), the level count and
clause 4 at the exceptional levels. -/
def TraceDataInputsB (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ) (p q : ℕ)
    (K : Knot) : Prop :=
  TiltData ψ s c σ u v h R ℓ exc lam0 lam1 ∧
  JunctionGenC ψ s c σ u v h ℓ exc lam0 lam1 ∧
  (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → z ∈ Submission.PBox s c σ →
    |inner ℝ v z - (inner ℝ v c + u)| = h →
    ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0) ∧
  LevelFrontierGen s c σ u v h ℓ exc lam0 lam1 ∧
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
    Set.encard (Set.range K.curve ∩
      frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞)) ∧
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∈ (exc : Set ℝ) →
    NoJumpBelowAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam)

/-- **The inputs `TraceDataInputsS` from the final inputs**: the geometric input
`LevelSphereDecomposition` is derived from `LevelFrontierGen` and the proved brick. -/
theorem traceDataInputsS_of_inputsB {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} {p q : ℕ} {K : Knot} (hs : 0 < s)
    (hcut : SlabCutsBox s c σ (inner ℝ v c + u) h v)
    (hI : TraceDataInputsB ψ s c σ u v h R ℓ exc lam0 lam1 p q K) :
    TraceDataInputsS ψ s c σ u v h R ℓ exc lam0 lam1 p q K :=
  ⟨hI.1, hI.2.1, hI.2.2.1,
    levelSphereDecomposition_of_levelFrontierGen hs hI.1 hcut hI.2.2.2.1,
    hI.2.2.2.2.1, hI.2.2.2.2.2⟩

/-- **The residual in its final form**: `TiltedTraceDataWExists` follows as soon as at every crux
configuration there are data satisfying `TraceDataInputsB`.  Compared with
`Work.Drive.Mono.TiltedTraceDataWExists_of_inputsS` the geometric hypothesis about the level frontier
is replaced by the *explicit* genericity `LevelFrontierGen`, which together with the proved
`Work.Drive.Mono.tiltedLevel_disjoint_spheres` produces it. -/
theorem TiltedTraceDataWExists_of_inputsB
    (H : ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
      (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (hd : 0 ≤ d),
      Work.Sweep.IsDistortionBound K d →
      Set.range K.curve = Set.range
        (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
          (Work.CoreTopology.standardCurve p q)).γ →
      Submission.countConst * d < (Nat.min p q : ℝ) →
      Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ) →
      ∀ (r : ℝ) (hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
        Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ →
        ∀ (s : ℝ) (hrs : r < s) (hs : s < (1 + Submission.eps) * r),
          Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
              {y : R3 | Submission.boxNorm c σ y = s} →
          ∀ (u : ℝ) (hu : |u| < Submission.eps * r),
            ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
                Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
              ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
            ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
                K.curve t ∈ Submission.PBox s c σ ∧
                (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
              ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
            ∃ (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
              TraceDataInputsB ψ s c σ u v h R ℓ exc lam0 lam1 p q K ∧
                SlabCutsBox s c σ (inner ℝ v c + u) h v) :
    Work.Drive.Mono.TiltedTraceDataWExists := by
  refine TiltedTraceDataWExists_of_inputsS ?_
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  obtain ⟨v, h, R, ℓ, lam0, lam1, exc, hI, hcut⟩ :=
    H p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  exact ⟨v, h, R, ℓ, lam0, lam1, exc, traceDataInputsS_of_inputsB (lt_trans hr hrs) hcut hI⟩

/-! ## The box-sphere part of the trace at the wall level (session H381-s25)

The box-sphere part of the level's trace is `Γ ∩ ({|⟪v,·⟫-(⟪v,c⟫+u)| ≥ h} ∪ {ℓ ≥ lam})`
(`Work.Drive.Mono.mem_frontier_tiltedLevelRemoved_of_boxSphere_of_edgeFree` gives the first
alternative, `..._of_slab_lt` the second at levels strictly below the wall, and
`Work.Drive.Mono.mem_frontier_tiltedLevelRemoved_of_boxSphere_imp` the converse).  The case
`|⟪v,·⟫-(⟪v,c⟫+u)| < h` *and* `ℓ z = lam` — a box-sphere point of the surface *inside* the slab at
the wall level — is missing from that list: it is a trace point as well, and it is exactly the case
of the "equator" obstruction (`Work.Drive.Mono.not_hboxsph_of_coord_eq`), i.e. of a knot point of
the box sphere whose flat height is the cutting height `u`.  At such a point the no-grazing
hypothesis of the level count is unsatisfiable for *every* datum, so the level count is not
available there; the lemma below records, nevertheless, that the point is a trace point of the level
`ℓ z` — the sharp form in which the obstruction is visible on the trace itself (rather than only on
the `hboxsph` conjunct).

The only geometric input is an *inward* direction of the box at `z` (the points `z + t·w`, `t ∈
(0,1)`, stay in the open box) along which the slab height does not change (`⟪v,w⟫ = 0`) and `ℓ`
strictly increases: the points `z + t·w` are then in the removed set of the level `lam = ℓ z`
(they are in the open box and have `ℓ > lam`), so `z` is in the closure of the removed set, while
`z ∉ interior` because `z` is on the box sphere. -/

/-- **A box-sphere point on the wall at the level `lam` is on the trace of that level.** -/
theorem mem_frontier_tiltedLevelRemoved_of_boxSphere_of_wall {s u h lam : ℝ} {c v z : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ}
    (hdesc : ∃ w : R3, (∀ t : ℝ, 0 < t → t < 1 → z + t • w ∈ Submission.PBox s c σ) ∧
      inner ℝ v w = 0 ∧ 0 < ℓ w)
    (hzsph : Submission.boxNorm c σ z = s)
    (hzwall : ℓ z = lam) :
    z ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) := by
  obtain ⟨w, hwin, hwv, hwℓ⟩ := hdesc
  have hzclR : z ∈ closure (Submission.PBox s c σ \
      (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y < lam})) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hden : 0 < 2 * (‖w‖ + 1) := by positivity
    set t : ℝ := min (ε / (2 * (‖w‖ + 1))) (1 / 2) with ht
    have htpos : 0 < t := by
      rw [ht]; exact lt_min (by positivity) (by norm_num)
    have ht1 : t < 1 := by
      rw [ht]; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have htε : t * ‖w‖ < ε := by
      have h2 : t ≤ ε / (2 * (‖w‖ + 1)) := by rw [ht]; exact min_le_left _ _
      have h3 : ε / (2 * (‖w‖ + 1)) * ‖w‖ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
        nlinarith [norm_nonneg w, hε]
      calc t * ‖w‖ ≤ ε / (2 * (‖w‖ + 1)) * ‖w‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg w)
        _ < ε := h3
    refine ⟨z + t • w, ⟨hwin t htpos ht1, ?_⟩, ?_⟩
    · rintro ⟨-, hlt⟩
      have hℓt : ℓ (z + t • w) = lam + t * ℓ w := by
        rw [map_add, map_smul, smul_eq_mul, hzwall]
      have hgt : lam < ℓ (z + t • w) := by
        rw [hℓt]; nlinarith [mul_pos htpos hwℓ]
      exact absurd hlt (not_lt.mpr (le_of_lt hgt))
    · rw [dist_eq_norm, show z - (z + t • w) = -(t • w) by abel, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_pos htpos]
      exact htε
  refine ⟨hzclR, fun hint => ?_⟩
  rw [tiltedLevelRemoved, Set.sdiff_eq, interior_inter,
    (Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq, interior_compl] at hint
  have hbox : z ∈ Submission.PBox s c σ := hint.1
  rw [Submission.mem_PBox_iff, hzsph] at hbox
  exact absurd hbox (lt_irrefl s)

/-- **The equator point of the knot is on the trace of its own level.**  If a point `K t₀` of the
knot lies on the box sphere of the level's box and its flat height is the cutting height
(`(K t₀) (σ 2) = c (σ 2) + u`), then — for *every* datum, once an inward-and-`ℓ`-increasing
direction of the box at the point is supplied — the point lies on the trace of the level
`lam = ℓ (K t₀)`.  This is the trace-level form of `Work.Drive.Mono.not_hboxsph_of_coord_eq`: it is
why the level count at the cutting levels of such points cannot be obtained from the box-sphere
count. -/
theorem knot_mem_trace_of_equator {P : Work.CoreTopology.ParamTorus} {K : Knot} {s u : ℝ}
    {c v : R3} {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {t₀ : ℝ}
    (hcar : K.curve t₀ ∈ P.carrier)
    (hdesc : ∃ w : R3, (∀ t : ℝ, 0 < t → t < 1 → K.curve t₀ + t • w ∈ Submission.PBox s c σ) ∧
      inner ℝ v w = 0 ∧ 0 < ℓ w)
    (hsph : Submission.boxNorm c σ (K.curve t₀) = s) :
    K.curve t₀ ∈ P.carrier ∩
      frontier (tiltedLevelRemoved s c σ u v h ℓ (ℓ (K.curve t₀))) :=
  ⟨hcar, mem_frontier_tiltedLevelRemoved_of_boxSphere_of_wall
    (s := s) (u := u) (h := h) (lam := ℓ (K.curve t₀)) (c := c) (v := v) (σ := σ) (ℓ := ℓ)
    hdesc hsph rfl⟩

/-- **A box-sphere point strictly inside the slab and strictly above the wall is on the trace.**
If `z` is on the box sphere (`boxNorm c σ z = s`, `0 < s`), strictly inside the closed slab
(`|⟪v,z⟫ - (⟪v,c⟫+u)| < h`) and strictly above the wall (`lam < ℓ z`), then `z` is on the trace of
the level `lam`.  This is the remaining easy case of the box-sphere part of the trace: every box
point close enough to `z` keeps `|⟪v,·⟫ - (⟪v,c⟫+u)| < h` and `ℓ > lam`, hence lies in the removed
set, while `z` itself is not an interior point of the removed set because it is not in the open box.
No genericity whatsoever is used. -/
theorem mem_frontier_tiltedLevelRemoved_of_boxSphere_of_above_wall {s u h lam : ℝ} {c v z : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} (hs : 0 < s)
    (hzsph : Submission.boxNorm c σ z = s)
    (hzslab : |inner ℝ v z - (inner ℝ v c + u)| < h)
    (hzlt : lam < ℓ z) :
    z ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) := by
  set F : ℝ := h - |inner ℝ v z - (inner ℝ v c + u)| with hF
  set G : ℝ := ℓ z - lam with hG
  have hpos1 : 0 < F := by rw [hF]; linarith
  have hpos2 : 0 < G := by rw [hG]; linarith
  have hzclP : z ∈ closure (Submission.PBox s c σ) := by
    refine frontier_subset_closure ?_
    rw [Work.Topology.SphereSlicing.frontier_PBox hs c σ]
    exact (Work.Topology.SphereSlicing.mem_BoxSphere).mpr hzsph
  have hzclR : z ∈ closure (Submission.PBox s c σ \
      (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y < lam})) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    set δ : ℝ := min (min ε 1) (min (F / (4 * (‖v‖ + 1))) (G / (4 * (‖ℓ‖ + 1)))) with hδ
    have hδpos : 0 < δ := by
      rw [hδ]
      exact lt_min (lt_min hε zero_lt_one) (lt_min (by positivity) (by positivity))
    have hδ_eps : δ ≤ ε := by
      rw [hδ]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    have hδ_1 : δ ≤ F / (4 * (‖v‖ + 1)) := by
      rw [hδ]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hδ_2 : δ ≤ G / (4 * (‖ℓ‖ + 1)) := by
      rw [hδ]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    obtain ⟨y, hyP, hydist⟩ := Metric.mem_closure_iff.mp hzclP δ hδpos
    have hyd : ‖y - z‖ < δ := by
      rw [dist_eq_norm] at hydist; simpa [norm_sub_rev] using hydist
    have hvδ : ‖v‖ * ‖y - z‖ < F / 2 := by
      have h1 : ‖v‖ * ‖y - z‖ ≤ ‖v‖ * δ :=
        mul_le_mul_of_nonneg_left (le_of_lt hyd) (norm_nonneg v)
      have h2 : ‖v‖ * δ ≤ ‖v‖ * (F / (4 * (‖v‖ + 1))) :=
        mul_le_mul_of_nonneg_left hδ_1 (norm_nonneg v)
      have h3 : ‖v‖ * (F / (4 * (‖v‖ + 1))) ≤ F / 4 := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity : (0:ℝ) < 4 * (‖v‖ + 1))]
        nlinarith [hpos1, norm_nonneg v]
      linarith
    have hlδ : ‖ℓ‖ * ‖y - z‖ < G / 2 := by
      have h1 : ‖ℓ‖ * ‖y - z‖ ≤ ‖ℓ‖ * δ :=
        mul_le_mul_of_nonneg_left (le_of_lt hyd) (norm_nonneg ℓ)
      have h2 : ‖ℓ‖ * δ ≤ ‖ℓ‖ * (G / (4 * (‖ℓ‖ + 1))) :=
        mul_le_mul_of_nonneg_left hδ_2 (norm_nonneg ℓ)
      have h3 : ‖ℓ‖ * (G / (4 * (‖ℓ‖ + 1))) ≤ G / 4 := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity : (0:ℝ) < 4 * (‖ℓ‖ + 1))]
        nlinarith [hpos2, norm_nonneg ℓ]
      linarith
    have hfy : |inner ℝ v y - (inner ℝ v c + u)| < h := by
      have hsplit : inner ℝ v y - (inner ℝ v c + u)
          = (inner ℝ v z - (inner ℝ v c + u)) + inner ℝ v (y - z) := by
        rw [inner_sub_right]; ring
      have hb : |inner ℝ v (y - z)| ≤ ‖v‖ * ‖y - z‖ := abs_real_inner_le_norm _ _
      have hbase : |inner ℝ v z - (inner ℝ v c + u)| + ‖v‖ * ‖y - z‖
          < |inner ℝ v z - (inner ℝ v c + u)| + F / 2 := by linarith
      have hF' : |inner ℝ v z - (inner ℝ v c + u)| + F / 2 < h := by
        rw [hF] at hbase ⊢; linarith
      rw [hsplit]
      calc |(inner ℝ v z - (inner ℝ v c + u)) + inner ℝ v (y - z)|
          ≤ |inner ℝ v z - (inner ℝ v c + u)| + |inner ℝ v (y - z)| := abs_add_le _ _
        _ ≤ |inner ℝ v z - (inner ℝ v c + u)| + ‖v‖ * ‖y - z‖ := by linarith
        _ < h := lt_trans hbase hF'
    have hly : lam < ℓ y := by
      have hsplit : ℓ y = ℓ z + ℓ (y - z) := by rw [map_sub]; ring
      have hb : -‖ℓ‖ * ‖y - z‖ ≤ ℓ (y - z) := by
        have h2 : |ℓ (y - z)| ≤ ‖ℓ‖ * ‖y - z‖ := by
          simpa [Real.norm_eq_abs] using ℓ.le_opNorm (y - z)
        linarith [neg_abs_le (ℓ (y - z))]
      have : G / 2 < ℓ y - lam := by
        rw [hsplit, hG] at *
        linarith
      linarith [hpos2]
    refine ⟨y, ⟨hyP, fun hc => absurd hc.2 (not_lt.mpr (le_of_lt hly))⟩,
      by simpa [dist_eq_norm, norm_sub_rev] using lt_of_lt_of_le hyd hδ_eps⟩
  refine ⟨hzclR, fun hint => ?_⟩
  rw [tiltedLevelRemoved, Set.sdiff_eq, interior_inter,
    (Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq, interior_compl] at hint
  have hbox : z ∈ Submission.PBox s c σ := hint.1
  rw [Submission.mem_PBox_iff, hzsph] at hbox
  exact absurd hbox (lt_irrefl s)


end

end Work.Drive.Mono
