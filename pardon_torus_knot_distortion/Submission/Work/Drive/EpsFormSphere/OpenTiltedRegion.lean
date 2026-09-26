import Mathlib
import Submission.Work.Drive.EpsForm.sweepThrough
import Submission.Work.Topology.SphereSlicing.isOpen_PBox

/-!
# The *open* region of the tilted sweep

The residual `Work.Drive.TiltedSweepExists` (in `Drive/pardon_of_cleansW_sphere.lean`) sweeps the
surface by the family of *open* regions

  `openTiltedSweepRegion P s c σ u v h ℓ lam = P.carrier ∩ (PBox s c σ \ (tiltedSlabClosed a v h ∩
    {y | ℓ y ≤ lam}))`,

with `a = ⟪v,c⟫ + u`.  This module holds the definition and the elementary facts about it, so that
the geometric lemmas about the sweep (the trace slicing, the span constancy between transverse
levels, the dichotomy) can be stated in other modules that import this one.

Why the region must be *open* in the carrier: Pardon's dichotomy — "a region of the surface whose
frontier is a family of pairwise disjoint simple inessential curves has winding span `⊥` or `⊤`"
(`Work.Drive.EpsFormSphere.windingSpan_bot_or_top_of_trace_inessential`, from the peel
`Work.BoxShrink.PinchOff.windingSpan_bot_or_top_of_inessential_boundary`) — takes the two pieces of
the surface cut out by the trace to be **open** in the carrier.  The region of the sweep with the
1-dimensional wall trace `{ℓ = lam} ∩ tiltedSlabClosed` kept in it (`tiltedSweepRegion`, i.e.
`Work.Drive.EpsForm.sweepRegion … (tiltedSlabClosed a v h)`) is *not* open there, so the dichotomy does not
apply to it; removing the wall too (equivalently: taking the interior, or removing the *closed*
wall) gives an open region with exactly the same frontier in the carrier and the same two
endpoints.
-/

namespace Work.Drive.EpsFormSphere

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- **The *open* region of the tilted sweep at the level `lam`**: the box region of the surface with
the *closed* part of the tilted slab in front of the level removed,

  `openTiltedSweepRegion … lam = carrier ∩ (PBox \ (tiltedSlabClosed ∩ {ℓ ≤ lam}))`.

Unlike `tiltedSweepRegion` — which contains the 1-dimensional wall trace
`carrier ∩ PBox ∩ tiltedSlabClosed ∩ {ℓ = lam}` and is therefore **not** open in the carrier — this
region *is* open in the carrier (`isOpenInCarrier_openTiltedSweepRegion`).  That is exactly what
Pardon's dichotomy (the `hone` field below) requires: the composing lemma
`Work.Drive.EpsFormSphere.windingSpan_bot_or_top_of_trace_inessential` takes **both** pieces of the
surface cut out by the trace to be open in the carrier.  The two regions have the same frontier in
the carrier, hence the same trace, and the same two endpoints:

* for `lam` below the `ℓ`-range of the box, `openTiltedSweepRegion … lam = boxRegion`
  (`openTiltedSweepRegion_eq_boxRegion`) — so the `start` field of the sweep is free;
* for `lam` above it, `openTiltedSweepRegion … lam = boxRegion \ tiltedSlabClosed`
  (`openTiltedSweepRegion_eq_sdiff`) — so the `finish` field is free as well. -/
def openTiltedSweepRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Set R3 :=
  P.carrier ∩ (Submission.PBox s c σ \
    (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y ≤ lam}))

/-- The open region of the tilted sweep is open in the carrier: the box is open and the closed part
of the tilted slab is closed. -/
theorem isOpenInCarrier_openTiltedSweepRegion {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} :
    Work.SurgeryInvariance.IsOpenInCarrier P
      (openTiltedSweepRegion P s c σ u v h ℓ lam) := by
  rw [Work.SurgeryInvariance.IsOpenInCarrier]
  have hbox : IsOpen (Submission.PBox s c σ) := Work.Topology.SphereSlicing.isOpen_PBox s c σ
  have hclosed : IsClosed (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
      {y : R3 | ℓ y ≤ lam}) :=
    (Work.Drive.EpsForm.isClosed_tiltedSlabClosed _ _ _).inter
      (isClosed_Iic.preimage ℓ.continuous)
  have hset : (Subtype.val ⁻¹' openTiltedSweepRegion P s c σ u v h ℓ lam : Set P.carrier) =
      Subtype.val ⁻¹' (Submission.PBox s c σ \
        (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
          {y : R3 | ℓ y ≤ lam})) := by
    ext x
    exact ⟨fun hx => hx.2, fun hx => ⟨x.2, hx⟩⟩
  rw [hset]
  exact (hbox.sdiff hclosed).preimage continuous_subtype_val

/-- The open region of the tilted sweep is contained in the (closed-wall) region `tiltedSweepRegion`:
only the 1-dimensional trace `{ℓ = lam} ∩ tiltedSlabClosed` is dropped. -/
theorem openTiltedSweepRegion_subset_tiltedSweepRegion {P : Work.CoreTopology.ParamTorus}
    {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    {lam : ℝ} :
    openTiltedSweepRegion P s c σ u v h ℓ lam ⊆
      Work.Drive.EpsForm.sweepRegion P s c σ
        (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ℓ lam := by
  rintro y ⟨hyc, hyb, hyrem⟩
  rw [Work.Drive.EpsForm.mem_sweepRegion]
  refine ⟨hyc, hyb, fun hW => ?_⟩
  by_contra hlt
  exact hyrem ⟨hW, le_of_lt (not_le.mp hlt)⟩

/-- **The start of the tilted sweep is free**: below the `ℓ`-range of the box the open region is the
whole box region. -/
theorem openTiltedSweepRegion_eq_boxRegion {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    (hlow : ∀ y ∈ Submission.PBox s c σ, lam < ℓ y) :
    openTiltedSweepRegion P s c σ u v h ℓ lam = Work.BoxShrink.Core.boxRegion P s c σ := by
  ext y
  constructor
  · rintro ⟨hyc, hyb, -⟩
    exact ⟨hyc, hyb⟩
  · rintro ⟨hyc, hyb⟩
    exact ⟨hyc, hyb, by rintro ⟨-, hle⟩; exact absurd (hlow y hyb) (not_lt.mpr hle)⟩

/-- **The end of the tilted sweep is free**: above the `ℓ`-range of the box the open region is the
box region with the *closed* tilted slab removed. -/
theorem openTiltedSweepRegion_eq_sdiff {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    (hhigh : ∀ y ∈ Submission.PBox s c σ, ℓ y < lam) :
    openTiltedSweepRegion P s c σ u v h ℓ lam = Work.BoxShrink.Core.boxRegion P s c σ \
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h := by
  ext y
  constructor
  · rintro ⟨hyc, hyb, hyrem⟩
    exact ⟨⟨hyc, hyb⟩, fun hslab => hyrem ⟨hslab, le_of_lt (hhigh y hyb)⟩⟩
  · rintro ⟨⟨hyc, hyb⟩, hnot⟩
    exact ⟨hyc, hyb, fun hmem => hnot hmem.1⟩


/-- **The trace of a level of the tilted sweep is a family of pairwise disjoint simple closed
curves** — the conclusion of the slicing input (item (b) of the sweep design) at one level `lam`,
and the hypothesis under which the span of the sweep is constant on a stretch and under which
Pardon's dichotomy applies.  The curves are the trace of the frontier of the level region, kept in
the `< lam` spelling in which the count
(`Work.Drive.EpsFormSphere.encard_frontier_tiltedSweptBall_lt_min`) and the in-flight slicing lemma
`Work.Drive.EpsFormSphere.ae_trace_circles_tiltedSweptBall` are stated; the frontier of the open
region is the same set (the two regions differ by the wall, which lies in the frontier of both). -/
def NiceTraceAt (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (a : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Prop :=
  ∃ (n : ℕ) (cs : Fin n → Work.CoreTopology.ClosedCurve P),
    (∀ i, Work.CoreTopology.IsSimple P (cs i)) ∧
    (∀ i j : Fin n, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ)) ∧
    (∀ (i : Fin n) (t : ℝ), (cs i).γ t ∈ frontier (Submission.PBox s c σ \
      (Work.Drive.EpsForm.tiltedSlabClosed a v h ∩ {y : R3 | ℓ y < lam}))) ∧
    (∀ y ∈ P.carrier, y ∈ frontier (Submission.PBox s c σ \
      (Work.Drive.EpsForm.tiltedSlabClosed a v h ∩ {y : R3 | ℓ y < lam})) →
      ∃ (i : Fin n) (t : ℝ), (cs i).γ t = y)

/-- `NiceTraceAt` holds at every level of the interval `[μ, ν]`. -/
def NiceTraceOn (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (a : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (μ ν : ℝ) : Prop :=
  ∀ lam ∈ Set.Icc μ ν, NiceTraceAt P s c σ a v h ℓ lam

end

end Work.Drive.EpsFormSphere
