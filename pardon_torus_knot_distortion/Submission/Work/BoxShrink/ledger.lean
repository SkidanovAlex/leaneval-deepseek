import Mathlib
import Submission.Work.BoxShrink.cruxAE
import Submission.Work.PlaneSlice.AeClean
import Submission.Work.BoxShrink.PinchOff.KeyRefuted

/-!
# The ledger: the classical inputs of the challenge

`Submission.lean` has exactly one `sorry`, for `Work.BoxShrink.ClassicalInputs`, the structure below.
It carries **two** fields, each a classical theorem of geometric topology (or Pardon's own Lemma 3)
for which Mathlib has no formalization.  Everything else of the development is proved, sorry-free and
axiom-free (only `propext`, `Classical.choice`, `Quot.sound`).

## 1. `pushThrough` — Pardon's cut-and-paste at the standard torus

`Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard` is Pardon's cut-and-paste
in the local `SliceDisc` vocabulary: *Alexander's theorem for an embedded `2`-sphere in `ℝ³` together
with isotopy extension*.  Its consequence
`Work.BoxShrink.CleansDiscsAll = ∀ ψ, Work.InnermostDisk.CleansDiscs (mapHomeomorph ψ)` — Pardon's
second innermost argument for the tori of the challenge, the form the reduction consumes — follows by
pure bookkeeping (`Work.BoxShrink.cleansDiscsAll_of_pushThrough`, in
`Submission/Work/BoxShrink/cruxAE.lean`): it is sent to
`Work.Topology.SphereSlicing.CleanOneCurve standard`
(`Work.Topology.Classical.cleanOneCurve_of_pushThroughInnermost`), transported along an ambient
homeomorphism (`Work.Topology.SphereSlicing.cleanOneCurve_map_homeomorph_iff`), and read as
`Work.InnermostDisk.CleansDiscs (mapHomeomorph ψ)`
(`Work.Topology.SphereSlicing.cleansDiscs_of_cleanOneCurve`).  From it the almost-everywhere cleaning
of the plane slices follows as well (`Work.PlaneSlice.aePlaneCleaned_of_pushThrough`).

The *slicing* half of the classical topology is **not** assumed: Jordan–Schoenflies on the round
sphere is **proved** in `Work.Smooth.SphereJordan` (from the planar Jordan–Schoenflies theorem, itself
proved in `Work.Smooth.Schoenflies`), and so is the almost-everywhere general position of the box-norm
level sets (`Work.BoxShrink.AeSlicedAll`, `Work.Smooth.OneManifold`).

## 2. `bubble` — Pardon's Lemma 3, in the counted form his proof delivers

`Work.BoxShrink.Pinch.CountingHalf` is **Pardon's Lemma 3 with the counting of his proof**.  His
Lemma 3 (Annals 174 (2011), Lemma 3; LaTeX in `tex/torusdist.tex`, § "Double bubbles with few
intersections with β") carries the hypothesis `|S ∩ β| + 2|D ∩ β| < I(F,β)`, and the counting is
used: it feeds his Lemma 2 (`mustbeinessential`), which is what shows that **every intermediate
sphere** `S_t` of the pinching family meets `F` in inessential curves only; the persistence lemma
(`spherefamily`) needs that at every `t`, not merely at the two endpoints.  The crux's two counts plus
`countConst · d < min p q` supply exactly Pardon's inequality, since
`10(1+ε)/ε·d + 2·5(1+ε)/ε·d = 75d + 75d = 150d = countConst·d < min p q = I(F,β)`.
`cruxCore_of_countingHalf` (below) turns it directly into the crux, with no auxiliary input at the
cutting disc.

### REFUTED statements — do not use them

The *uncounted* forms of the same conclusion are all **FALSE**, with machine-checked proofs in
`Submission/Work/BoxShrink/PinchOff/`:

* `Work.BoxShrink.PinchOff.not_smoothHalfS : ¬ Work.BoxShrink.Pinch.SmoothHalfS`
  (`KeyRefuted.lean`), at the "tangent configuration" of the standard torus: the box-sphere trace and
  the slice trace are both inessential while the box region carries an essential loop and neither half
  does;
* `Work.BoxShrink.PinchOff.not_bubbleHalf_tangent`, `not_pushOffHalf`,
  `not_key`, `not_pardonPinchInput`;
* consequently `Work.BoxShrink.Pinch.SmoothHalf*`, `Work.BoxShrink.Bubble.SmoothHalf`,
  `Work.BoxShrink.Bubble.PushOffHalf`, `Work.BoxShrink.Bubble.PardonPinchInput`,
  `Work.BoxShrink.Pinch.Key`, `Work.BoxShrink.Pinch.PinchNoJump`,
  `Work.BoxShrink.PinchOff.KeyTameClosed`, `Work.BoxShrink.PinchOff.DropCase` (the last three are
  equivalent spellings of the abstract residual), and `Work.PinchLemma3.SliceWall` — which implies
  `SmoothHalfS` (`Work.PinchLemma3.smoothHalfS_of_sliceWall`) — are all false, and so are the
  unrestricted dichotomy statements `Work.PinchTransport.SphereInessentialDichotomy` and
  `Work.Dichotomy.DichotomyAll` (they imply `SmoothHalfS`); the *span* and *loop-transport* forms of
  the conclusion are false too (`Work.PinchTransport.not_spanAt_of_sphereInessential`,
  `not_transportAt_of_sphereInessential`, `Work.PinchOff.not_dropCase`).  An earlier version of this
  ledger carried `BubbleDatum = CountingHalf ∨ SmoothHalfS` and an almost-everywhere route through
  `SmoothHalfS`; both have been removed, because that disjunct is refuted.
* **The *local* forms of the cut-and-paste are FALSE** (machine-checked, `Submission/Work/PushOff3D/`):
  `Work.PushOff3D.not_localPushOff : ¬ Work.Alexander3D.LocalPushOff` — the collar-local push-off with
  the support restricted to the collar of `γ`, refuted at a *rescaled paraboloid* whose every
  hypothesis holds (the two sheets accumulating at a fixed vertex of the collar) — and
  `Work.PushOff3D.not_localCollarPushOff : ¬ Work.PushOff3D.LocalCollarPushOff`, the same with the
  support restriction dropped and the innermost clause demanded only inside the collar.  The reusaable
  obstruction is `Work.PushOff3D.pinning_no_push` (two preconnected sheets on opposite sides of the
  surface, pinned by fixed points of the homeomorphism, with a common accumulation point).  The
  "shrink the collar" route is impossible as well
  (`Work.PushOff3D.range_subset_of_inter_closure_subset`,
  `Work.PushOff3D.not_boundedInCollar_of_boundary_free`).  Consequently
  `Work.Alexander3D.pinchedSurgery_of : InessentialCurveCollar → LocalPushOff → PinchedSurgery` is
  vacuous, and the local push-off is NOT an exit point.  The *repair* which survives is the
  **global** statement `Work.PushOff3D.CorrectedPushOff`, which is `PinchedSurgery` with a collar
  (and which is realised in the very configuration that refutes the local form:
  `Work.PushOff3D.configuration_corrected_realised`).

* **`Work.Topology.Classical.AlexanderSphereTheorem` is FALSE as stated** (it quantifies over *all*
  embedded spheres, and the Alexander horned sphere bounds no region homeomorphic to the closed ball:
  the bounded complement of a wild sphere is not simply connected).  It may therefore never be proved,
  and every reduction which *uses* it is only usable for a **tame (locally flat) sphere**: check
  `Work.Bicollar.sphereBoundsBall_of_alexander_and_brouwer` (and the ledger's `Sphere` route) against
  the sphere actually needed by the cut-and-paste, namely the pinching sphere
  `β(𝔻) ∪ Σ_surf(𝔻)`, which is *not* known to be locally flat.  The tameness-free statement to aim at
  is `Work.Collar3D.SphereBoundsBall` itself (Jordan–Brouwer separation: an embedded `2`-sphere is the
  frontier of a compact region with nonempty interior) — that one is true for wild spheres as well.

* Also vacuous or false, for the same family of reasons: `Work.Smooth.PushThrough3D.PinchedSurgeryInput`
  (`Work.Collar3D.CutAndPaste.not_pinchedSurgeryInput`), and hence
  `Work.Smooth.SphereJordan.cleansDiscsAll_field_of_standard_props_and_pinched`,
  `Work.Smooth.PushThrough3D.cleansDiscsAll_of_planar_pinched`.

### Exit points: what to prove, and how it discharges the ledger

A future agent who proves **any** of the following immediately discharges the ledger: each is
connected to `Work.BoxShrink.ClassicalInputs` by a *proved* implication in the workspace.

**For the first field (`pushThrough`).**

* `Work.Collar3D.PinchedSurgery` — Pardon's cut-and-paste as a single `Prop` about `ℝ³` alone (with
  `F` locally flat; that hypothesis is essential).  Gives `PushThroughInnermost standard`
  (`Work.Collar3D.pushThroughInnermost_standard_of_pinchedSurgery`), hence `CleansDiscsAll`; the whole
  challenge follows from `Work.Collar3D.pardon_torus_knot_distortion_of_pinchedSurgery`.
* `Work.PushOff3D.CorrectedPushOff` — the *global* push-off with a collar (`⟺`
  `Work.Collar3D.PinchedSurgery` in the configurations of the argument, by
  `Work.PushOff3D.corrected_of_pinchedSurgery` / `corrected_of_localPushOff`); with the bicollar
  theorem for the *inessential* curve (`Work.Alexander3D.InessentialCurveCollar`) it gives the
  ledger's first field (`Work.PushOff3D.cleansDiscsAll_of_inessentialCurveCollar_of_corrected`).
  The *local* forms of the same step are refuted (see above), so the global form is the only one left
  on this route; its content is Alexander's theorem for the pinching sphere plus isotopy extension.
* `Work.PushOff3D.HasShearDatum c e Fix` — a *sufficient*, elementary form of the same content: a
  compactly supported fiberwise move of the collar `S¹ × ℝ × ℝ` which clears the disc's interior part
  and fixes `Fix` (`Work.PushOff3D.pushOff_of_shearDatum`).  It is **constructed** when the disc's
  part in the collar is compactly contained and the fixed set avoids the shear's box
  (`Work.PushOff3D.hasShearDatum_of_bounded`, `Work.PushOff3D.globalPushOff_of_bounded`); it contains
  no three-dimensional topology.  `Work.PushOff3D.correctedPushOff_of_hasShearDatum` turns a datum
  for every configuration into `CorrectedPushOff`.
* `Work.Topology.Classical.CutsAlongSubdisc Work.CoreTopology.standard` — the surgery half alone,
  since the Jordan-separation half `Work.Classical3D.innermostCurveExists` is **proved**; combine with
  `Work.Topology.Classical.pushThroughInnermost_of_innermostCurveExists_of_cutsAlongSubdisc`.
* `Work.Classical3D.SurfaceCutAndPaste` / `SurfaceCutAndPasteAt` — the same surgery in the pure `ℝ³`
  vocabulary of the sibling chapter (`Work.Classical3D`); gives the first field through
  `Work.Classical3D.cleansDiscsAll_of_surfaceCutAndPaste`.

The two classical theorems into which the global step now decomposes are named in the workspace and
are the frontier of this field:
* `Work.Collar3D.SphereBoundsBall` — *an embedded `2`-sphere in `ℝ³` is the frontier of a compact
  region with nonempty interior* (the consumed form of Alexander's theorem; Jordan–Brouwer separation
  for a sphere), from which `Work.Collar3D.separates_of_boundsBall` is **proved**;
* `Work.Collar3D.IsotopyExtension` — Edwards–Kirby, the extension of a compactly supported ambient
  isotopy of a locally flat closed set (the chart-supported case is **proved**,
  `Work.Collar3D.ambientIsotopyOfChart`).

**For the second field (`bubble`), all in the counted vocabulary (the uncounted forms are refuted).**

* `Work.BoxShrink.Pinch.CountingHalf` itself;
* `Work.PinchCounted.CountedPinch`, `CountedStep2`, `CountedPinchSweep`, `CountedSpanPushOff`,
  `CountedDim`, `CountedCollarPushOff`, `PardonLemma3`, `PinchInputCounting` — each gives
  `CountingHalf` (`Work.PinchCounted.Ladder`, `countingHalf_of_*`);
* `Work.PinchFamily.PinchTransport` — the counted loop-transport form; gives `CountingHalf`
  (it is equivalent to `CountedPinch` in the non-degenerate case).
  (Beware: the *unrestricted* transport and span forms are false — see above — so only the counted
  statements may be used.)

None of these has been proved yet.  Everything in the *other* direction (from the ledger to the
challenge) is proved, sorry-free and axiom-free.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink

noncomputable section

/-- **The double-bubble core from Pardon's counted Lemma 3.**

`Work.BoxShrink.Pinch.CountingHalf` carries, besides the two inessentiality hypotheses (which the
crux derives from its counts and Pardon's Lemma 2), the whole counting data of the crux; it is
therefore exactly Pardon's Lemma 3 instantiated at the configurations the crux produces, and it gives
the conclusion `Work.BoxShrink.Bubble.BubbleHalf` of the double bubble directly. -/
theorem cruxCore_of_countingHalf (h : Pinch.CountingHalf) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q := by
  intro p q
  unfold Work.BoxShrink.CruxCore
  intro hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  set P := Work.Smooth.Morse.torus ψ with hP
  have hb : Work.BoxShrink.Bubble.BubbleHalf P s c σ u :=
    h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  have hbox' : P.ContainsEssentialLoop (Core.boxRegion P s c σ) :=
    Core.containsEssentialLoop_boxRegion_of_hasEssBox (P := P) (c := c) (σ := σ)
      (le_of_lt hrs) hbox
  rcases hb hbox' with hup | hlo
  · exact Or.inr ((Core.containsEssentialLoop_upperRegion_iff P s c σ u).mp hup)
  · exact Or.inl ((Core.containsEssentialLoop_lowerRegion_iff P s c σ u).mp hlo)

/-- **The shape of the ledger's second field.**

`Work.BoxShrink.BubbleDatum := Pinch.CountingHalf ∨ Pinch.SmoothHalfS` is the shape in which the
sibling chapters state (and construct) the double-bubble datum.  Its second disjunct is **refuted**
(`Work.BoxShrink.PinchOff.not_smoothHalfS`), so the disjunction is *equivalent* to its first
disjunct:

`Work.BoxShrink.bubbleDatum_iff_countingHalf`.

The shape is kept (rather than replacing `BubbleDatum` by `Pinch.CountingHalf`) so that the delivered
chapters that construct `BubbleDatum` — `Submission/Work/Dichotomy/`, `Submission/Work/BoxShrink/PinchOff/Ledger.lean`
— continue to build.  Only the first disjunct may be used to discharge the ledger. -/
def BubbleDatum : Prop :=
  Work.BoxShrink.Pinch.CountingHalf ∨ Work.BoxShrink.Pinch.SmoothHalfS

/-- The counted form coerces into `BubbleDatum` (as its first disjunct). -/
instance : Coe Work.BoxShrink.Pinch.CountingHalf BubbleDatum := ⟨Or.inl⟩

/-- `BubbleDatum` is equivalent to Pardon's counted Lemma 3, because its second disjunct is
refuted. -/
theorem bubbleDatum_iff_countingHalf : BubbleDatum ↔ Work.BoxShrink.Pinch.CountingHalf :=
  ⟨fun h => h.elim id (fun hs => absurd hs Work.BoxShrink.PinchOff.not_smoothHalfS), Or.inl⟩

/-- **Pardon's shrinking step from Pardon's counted Lemma 3.** -/
theorem boxShrink_of_countingHalf (hcl : CleansDiscsAll) (hb : Pinch.CountingHalf) :
    ∀ p q : ℕ, Submission.BoxShrinkStatement p q :=
  Work.BoxShrink.boxShrink_of_crux fun p q =>
    ⟨hcl, cruxCore_of_countingHalf hb p q,
      Work.Smooth.OneManifold.aeSlicedAll_of_planeHypothesis
        Work.Smooth.Schoenflies.planeHypothesis⟩

/-- **Pardon's shrinking step from the double-bubble datum**, in the form in which the sibling
chapters (`Submission/Work/Dichotomy/`, `Submission/Work/Collar3D/`) call it: the cut-and-paste
supplied in its *consumed* form `CleansDiscsAll`. -/
theorem boxShrink_of_bubbleDatum (hcl : CleansDiscsAll) (hb : BubbleDatum) :
    ∀ p q : ℕ, Submission.BoxShrinkStatement p q :=
  boxShrink_of_countingHalf hcl (bubbleDatum_iff_countingHalf.mp hb)

/-- **The challenge from the cut-and-paste in its consumed form and the double-bubble datum.** -/
theorem pardon_torus_knot_distortion_of_cleansDiscsAll (hcl : CleansDiscsAll) (hb : BubbleDatum) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  fun p q hp hq hc K hclass =>
    Submission.theorem_of_core
      (Submission.CoreStatement_of_boxShrink (boxShrink_of_bubbleDatum hcl hb))
      p q hp hq hc K hclass

/-- A classical cut-and-paste statement — `Work.Topology.Classical.PushThroughInnermost standard`
(Alexander's theorem for an embedded `2`-sphere in `ℝ³` plus isotopy extension, in the local
`SliceDisc` vocabulary) — coerces to the form the reduction consumes,
`Work.BoxShrink.CleansDiscsAll`, by `Work.BoxShrink.cleansDiscsAll_of_pushThrough`.  The coercion
lets both spellings be passed to `ClassicalInputs` below. -/
instance : Coe (Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard)
    CleansDiscsAll :=
  ⟨cleansDiscsAll_of_pushThrough⟩

/-- **The classical inputs of the challenge.**  Each field is a classical theorem of geometric
topology (or Pardon's own Lemma 3) for which Mathlib has no formalization: Pardon's cut-and-paste at
the surface, and Pardon's double bubble *with the counting of his proof* (the uncounted forms are
refuted — see the module docstring). -/
structure ClassicalInputs : Prop where
  /-- Pardon's cut-and-paste at the surface: Alexander's theorem for an embedded `2`-sphere in `ℝ³`
  plus isotopy extension, carried in the form the reduction consumes,
  `Work.BoxShrink.CleansDiscsAll = ∀ ψ, Work.InnermostDisk.CleansDiscs (mapHomeomorph ψ)`.  A term
  of the stronger local form `Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard`
  is accepted here by the coercion instance above. -/
  pushThrough : CleansDiscsAll
  /-- Pardon's Lemma 3 (the double bubble), in the `BubbleDatum` shape; only its first disjunct
  (`Work.BoxShrink.Pinch.CountingHalf`, the counted form) is usable, the second being refuted
  (`Work.BoxShrink.bubbleDatum_iff_countingHalf`). -/
  bubble : BubbleDatum

/-- **Pardon's theorem, from the classical inputs.** -/
theorem pardon_torus_knot_distortion_of_classicalInputs (h : ClassicalInputs) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  fun p q hp hq hc K hclass =>
    Submission.theorem_of_core
      (Submission.CoreStatement_of_boxShrink
        (boxShrink_of_countingHalf h.pushThrough
          (bubbleDatum_iff_countingHalf.mp h.bubble)))
      p q hp hq hc K hclass

end

end Work.BoxShrink
