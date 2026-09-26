import Submission.Work.BoxShrink.Bubble.HalfDefs
import Submission.Work.BoxShrink.Bubble.Defs
import Submission.Work.BoxShrink.Bubble.Basic
import Submission.Work.BoxShrink.Bubble.Toolkit.regionEquivalent_iff_realizedWindings
import Submission.Work.BoxShrink.Bubble.Toolkit.regionEquivalent_union_zeroSpan
import Submission.Work.BoxShrink.Bubble.Toolkit.regionEquivalent_trans
import Submission.Work.BoxShrink.Bubble.Toolkit.regionEquivalent_of_surgeryStepZero
import Submission.Work.BoxShrink.Bubble.Toolkit.windingOf_eq_zero_of_span_bot
import Submission.Work.BoxShrink.Bubble.Sweep.regionEquivalent_endpoints
import Submission.Work.BoxShrink.Bubble.Sweep.exists_sweepLoops_of_surgeryStepZero
import Submission.Work.BoxShrink.Bubble.Sweep.exists_sweepLoops_trans
import Submission.Work.BoxShrink.Bubble.Flow.exists_curve_of_periodicFlow
import Submission.Work.BoxShrink.Bubble.Flow
import Submission.Work.BoxShrink.Bubble.PushModel
import Submission.Work.BoxShrink.Bubble.Obstruction.surgeryStepZero_eq_self_or_empty
import Submission.Work.BoxShrink.Bubble.Neck.bubbleSweep_of_neckComponent
import Submission.Work.BoxShrink.Bubble.Neck
import Submission.Work.BoxShrink.Bubble.Transport.slicePushOff_of_deformation
import Submission.Work.BoxShrink.Bubble.Reduce
import Submission.Work.BoxShrink.Bubble.Equivalence
import Submission.Work.BoxShrink.Bubble.Sharp
import Submission.Work.BoxShrink.Bubble.Instances
import Submission.Work.BoxShrink.Bubble.Obstruction
import Submission.Work.BoxShrink.Bubble.Integration
import Submission.Work.BoxShrink.Bubble.Restricted
import Submission.Work.BoxShrink.Bubble.Disc
import Submission.Work.BoxShrink.Bubble.DiscRoute
import Submission.Work.BoxShrink.Bubble.Pinch
import Submission.Work.BoxShrink.Bubble.OpenSlice
import Submission.Work.BoxShrink.Bubble.Smooth
import Submission.Work.BoxShrink.Bubble.Smooth.boxGauge
import Submission.Work.BoxShrink.Bubble.Smooth.GaugeFlow
import Submission.Work.BoxShrink.Bubble.Smooth.curveSard
import Submission.Work.BoxShrink.Bubble.Smooth.etaFlow
import Submission.Work.BoxShrink.Bubble.Smooth.criticalFreeWindow
import Submission.Work.BoxShrink.Bubble.Plane.Perturb
import Submission.Work.BoxShrink.Bubble.Plane.thinPath
import Submission.Work.BoxShrink.Bubble.Plane.finite_preimage
import Submission.Work.BoxShrink.Bubble.Plane.descent
import Submission.Work.BoxShrink.Bubble.Plane.FiniteSlice
import Submission.Work.BoxShrink.Bubble.Plane.PerturbCountable
import Submission.Work.BoxShrink.Bubble.Plane.countable_preimage
import Submission.Work.BoxShrink.Bubble.Plane.CountableSlice
import Submission.Work.BoxShrink.Bubble.standard_counterexample
import Submission.Work.BoxShrink.Bubble.cex_upperRegion_essential
import Submission.Work.BoxShrink.Bubble.cex_not_slicePushOffSpan
import Submission.Work.BoxShrink.Bubble.Refutation
import Submission.Work.BoxShrink.Bubble.Corrected
import Submission.Work.BoxShrink.Bubble.PardonLocalModel
import Submission.Work.BoxShrink.Bubble.cex_windingSpan_boxRegion_eq_top
import Submission.Work.BoxShrink.Bubble.Dichotomy
import Submission.Work.BoxShrink.Bubble.MigrationProbe
import Submission.Work.BoxShrink.Bubble.not_containsEssentialLoop_sphereSet_swap
import Submission.Work.BoxShrink.Bubble.meridian_mem_upperRegion_swap
import Submission.Work.BoxShrink.Bubble.meridian_mem_lowerRegion_swap
import Submission.Work.BoxShrink.Bubble.longitude_mem_lowerRegion_swap
import Submission.Work.BoxShrink.Bubble.SwapFamily
import Submission.Work.BoxShrink.Bubble.HalfInstances
import Submission.Work.BoxShrink.Bubble.PinchEndgame

/-!
# `Work.BoxShrink.Bubble` — Pardon's double bubble for the box/plane configuration

Entry point: `import Submission.Work.BoxShrink.Bubble.All`.  Namespace `Work.BoxShrink.Bubble`.
See `Submission/Work/BoxShrink/Bubble/README.md` for the full account.

## What this chapter is

The field `bubble` of `Work.BoxShrink.Core.BubbleInput` asks for Pardon's double bubble for the
box/plane configuration

`S = sphereSet c σ s = ∂PBox s c σ`,  `D = cutDisc s c σ u`,

i.e. for the `Work.SurgeryInvariance.SweepLoops`-family of regions pinching the sphere `S` along
the flat disc `D`, with endpoint regions `boxRegion P s c σ` (`= F ∩ int(S)`) and
`upperRegion P s c σ u ∪ lowerRegion P s c σ u` (`= F ∩ int(H₁) ∪ F ∩ int(H₂)`, the two halves of
the double bubble), for every configuration in which the two cuts carry no essential loop of `F`.

## The result

* `Work.BoxShrink.Bubble.SlicePushOff P s c σ u` — **the geometric input**, isolated: every winding
  vector realised by a loop of `F` inside the box is realised by a loop of `F` away from the
  slicing plane.  Equivalently, by
  `Work.BoxShrink.Bubble.pushOffDatum_iff_slicePushOff`, it is the loop-level datum
  `Work.BoxShrink.Core.DoubleBubbleDatum P s c σ u`
  (`RegionEquivalent P (boxRegion) (upperRegion ∪ lowerRegion)`), because the reverse transport is
  free (`upperRegion ∪ lowerRegion ⊆ boxRegion`).
* `Work.BoxShrink.Bubble.bubble_of_slicePushOff` and
  `Work.BoxShrink.Bubble.bubble_of_pushOffAll`: **Pardon's double bubble (the field `bubble`) from
  the input**, in the exact shape of the field
  (`∀ P s c σ u, ¬ P.ContainsEssentialLoop (sphereSet c σ s) →
     ¬ P.ContainsEssentialLoop (sliceRegion P s c σ u) → BubbleSweep P s c σ u`).
* `Work.BoxShrink.Bubble.containsEssentialLoop_half_of_slicePushOff`: the form the shrinking step
  consumes (Pardon's Lemma 3).
* `Work.BoxShrink.Bubble.slicePushOff_of_deformation` — the input from a one-parameter deformation
  of the surface carrying the region inside the box into the two half-regions (the "transport"
  form, matching `Work.Smooth.Morse.SublevelTransport`);
* `Work.BoxShrink.Bubble.SlicePushModel` and `Work.BoxShrink.Bubble.slicePushOff_of_pushModel` —
  **the input from its local model**: a deformation of `ℝ³` supported in an open neighbourhood `N`
  of the slice (i.e. `H r x = x` off `N`), preserving the surface and carrying `N` into the two
  half-regions, gives the input.  The points outside `N` need no care: a loop of the region which
  misses `N` misses the slice and hence already lies in the two half-regions.  This is Pardon's
  pinch as a *local* statement, and it is the form in which a sibling chapter on the collar
  structure of the slice can discharge the input
  (`Work.BoxShrink.Bubble.slicePushModel_of_empty_slice` is the degenerate instance);
* `Work.BoxShrink.Bubble.NeckComponent` + `Work.BoxShrink.Bubble.bubbleSweep_of_neckComponent`
  and `Work.BoxShrink.Bubble.bubble_of_neckAll` + `nonempty_neckComponent_of_span_bot` — **the family
  from Pardon's neck**: a piece of the region which is clopen in the region, contains the slice and
  carries no essential loop gives the two-step sweep
  `boxRegion → boxRegion ∖ C → upperRegion ∪ lowerRegion` with no loop transport at all.  (This
  covers exactly the configurations with disconnected region; for a connected region the neck is the
  whole region and the hypothesis degenerates to `span boxRegion = ⊥`, see the docstring.)
* `Work.BoxShrink.Bubble.Flow.exists_curve_of_periodicFlow` and
  `Work.BoxShrink.Bubble.slicePushOff_of_planeFlow` — **the input from a periodic flow of the
  parameter plane**: an equivariant continuous `Φ : ℝ → ℝ² → ℝ²` whose time-`1` map carries the
  preimage of `boxRegion` into the preimage of `upperRegion ∪ lowerRegion` gives the input (the
  curves are transported by the descended flow, the winding vector being unchanged because the flow
  commutes with the period lattice).  For the smooth surfaces of the challenge this is the form in
  which the gradient flow of the pull-back `pullback ψ (fun y => y (σ 2))` of the plane coordinate
  can be used;
* `Work.BoxShrink.Bubble.slicePushOff_of_empty_slice`,
  `Work.BoxShrink.Bubble.slicePushOff_of_span_bot`,
  `Work.BoxShrink.Bubble.slicePushOff_of_essential_avoids`,
  `Work.BoxShrink.Bubble.slicePushOff_of_meeting` — the proved cases of the input (the last one
  sharpens it: only the loops meeting the slice matter), and `bubble_of_empty_slice`,
  `bubble_of_zero_span` — the corresponding unconditional instances of Pardon's family;
* `Work.BoxShrink.Bubble.softMax`, `auxFun` and **`Work.BoxShrink.Bubble.slicePushOff_of_gaugeSard`**
  (`Smooth/GaugeFlow.lean`) — **the box folded into the level function**: with a `C²` gauge of the box
  (`B ≤ gauge ≤ B + δ`) and an under-approximating smooth maximum `softMax`, the auxiliary function
  `h = auxFun gauge c σ u s = softMax (gauge - s) (planeCoord)` satisfies
  `{h < -1/2} ∩ F ⊆ lowerRegion` and `boxRegion ⊆ {h < b}`; hence the flow of `h` transports every loop
  of `boxRegion` into `lowerRegion` with the same winding, and `SlicePushOff` — hence the field —
  follows from the single critical-value statement for `h|_F` (`smoothPushOff_of_sard`,
  `bubbleSweep_of_sard`).  No collar of the slice and no transversality of the plane is needed;
* **`Work.BoxShrink.Bubble.softMaxEta`, `auxFunEta` and `slicePushOff_of_curveSardEta`
  (`Smooth/etaFlow.lean`)** — the *variable-endpoint* last mile: the error-parametrised smooth maximum
  `softMaxEta η u v = (u+v)/2 + (√((u-v)²+η²) - η)/2` (`max u v - η/2 ≤ softMaxEta η u v ≤ max u v`,
  `C²` for `η ≠ 0`), the auxiliary function `auxFunEta η gauge c σ u s`, and the statement that **if
  for every closed curve of the surface inside `boxRegion` there are a gauge of the box, a level
  `a < 0` and a level `b > 0` with `b` above `auxFunEta (-2a)` on the curve and `[a, b]`
  critical-value-free for it, then `SlicePushOff` holds** (and `bubbleSweep_of_curveSardEta` gives the
  field).  Taking `η = -2a` makes the error `η/2 = -a` close the gap exactly, so that
  `{auxFunEta (-2a) < a}` is contained in `lowerRegion` — this is the corrected form of the
  fixed-endpoint auxiliary function of `GaugeFlow.lean`, whose interval `[-1/2, b]` was refuted by the
  counterexample documented there and in `PLAN.md`;
* `Work.BoxShrink.Bubble.Smooth.curveSard` (delegated, proved) — **the last-mile statement in the
  form the flow theorem actually consumes**: if for every closed curve of `F` inside `boxRegion` there
  is a `C²` function `hh`, a level `a < 0` and a level `b > 0` with `{hh < a} ⊆ upperRegion ∪
  lowerRegion`, `hh (γ t) < b` for all `t`, and `[a, b]` critical-value-free for `hh|_F`, then
  `SlicePushOff` holds.  Per `PLAN.md` the functions `hh` are the `auxFun`-family built from the gauge
  (`boxGauge`) and the under-approximating smooth maximum (`softMax`), and the critical-value
  statement is the single remaining analytic input;
* `Work.BoxShrink.Bubble.Smooth.boxGauge` (delegated) — **the smooth gauge of the box**: for every
  `ε > 0` there is `gauge : R3 → ℝ` of class `C²` with `boxNorm c σ ≤ gauge ≤ boxNorm c σ + ε`; this
  is the first ingredient of the recipe recorded in `PLAN.md` for closing the push-off from the flow
  of an *auxiliary* function that has the box built into it;
* `Work.BoxShrink.Bubble.slicePushOff_of_belowPlateau` and `…_of_abovePlateau` (`Smooth.lean`) —
  **the push-off, hence the field, for the smooth tori of the challenge from the flow of the plane
  coordinate**: `Work.Smooth.Morse.Flow.regularEquivalent_of_contDiff_two` (proved in the sibling
  chapter) transports every loop of `F ∩ {g < b}` to a loop of `F ∩ {g < a}` with the same winding
  vector, for `g = planeCoord c σ u` of class `C²` and `[a,b]` critical-value-free.  Hence, whenever
  the region inside the box is exactly a below-plateau (resp. above-plateau) of the plane coordinate
  over a critical-value-free interval containing `0` — `boxRegion ⊆ {g<b}` and
  `{g<b} ∩ F ⊆ boxRegion` — the flow's destination lies in the box, giving
  `Work.BoxShrink.Bubble.SlicePushOff` (indeed: loops in `lowerRegion`, resp. `upperRegion`), and
  `Work.BoxShrink.Bubble.bubbleSweep_of_belowPlateau` / `…_of_abovePlateau` give Pardon's family.
  This is the first place where the smooth flow machinery is used end to end; the two remaining
  obstructions for a general configuration are the *box-exit* of the flow (the destination of the
  plane-coordinate flow is a half-space trace, which a bounded box need not contain) and the
  transversality of the level `0`;
* `Work.BoxShrink.Bubble.SliceDiscData` + `Work.BoxShrink.Bubble.nonempty_neckComponent_of_sliceDisc`
  and `Work.BoxShrink.Bubble.bubbleSweep_of_sliceDiscData` — **the disc route to the input**: if an
  embedded disc of the surface contains the slice in its interior, lies in the region, and has open
  complement in the region, then the neck component is its interior (an embedded disc is open in the
  surface and carries no essential loop, `windingSpan_interior_discRegion`), so Pardon's family
  exists.  This is the *geometric* form of Pardon's pinch: the changed piece at the pinching
  parameter is the trace of a flat disc;
* `Work.BoxShrink.Bubble.surgeryStepZero_windingSpan_eq` — **a `2`-surgery never changes the winding
  span** (the span-level companion of
  `Work.BoxShrink.Bubble.Toolkit.regionEquivalent_of_surgeryStepZero`, which needs nonemptiness);
* `Work.BoxShrink.Bubble.surgeryStepZero_boxRegion_of_sliceOpen` and
  `Work.BoxShrink.Bubble.bubbleSweep_of_sliceOpen` — **the case in which the slice is open in the
  surface**: then the decomposition `boxRegion = (upper ∪ lower) ∪ sliceRegion` *is* a single
  `2`-surgery and Pardon's family exists with no further geometry.  This is exactly the sharp form of
  the obstruction: the whole content of the pinch is that the slice is *not* open in the surface for
  a generic configuration;
* `Work.BoxShrink.Bubble.PushOffInput` — the input globally (the hypothesis on which the field is
  delivered), `Work.BoxShrink.Bubble.bubbleFrom` — the field in the exact shape of the structure's
  field, and `Work.BoxShrink.Bubble.crux_of_pushOffAll` — Pardon's shrinking step
  (`Work.BoxShrink.CruxStatement`) from the input and the remaining inputs of the crux;
* `Work.BoxShrink.Bubble.boxRegion_subset_of_surgeryStepZero_allCases`,
  `Work.BoxShrink.Bubble.inter_removed_eq_empty`,
  `Work.BoxShrink.Bubble.exists_open_inter_subset_of_removed`,
  `Work.BoxShrink.Bubble.Obstruction.surgeryStepZero_eq_self_or_empty`,
  `Work.BoxShrink.Bubble.eq_empty_of_mem_removed`,
  `Work.BoxShrink.Bubble.eq_empty_of_slice_mem_removed` — **why the family cannot be built from
  `2`-surgeries alone**: a `SurgeryStepZero` changes a region by a piece which is clopen in the
  region (`exists_open_inter_subset_of_removed`), and on a *preconnected* region it is therefore
  either trivial or empties the region
  (`Obstruction.surgeryStepZero_eq_self_or_empty`); the slice is closed with empty interior, so no
  single `2`-surgery can remove a point of the slice from a connected region, and a `2`-surgery
  starting at the region inside the box and ending at a region containing both half-regions cannot
  have moved anything.

## The pieces of the picture

`Work.BoxShrink.Bubble.outsideRegion`, `…slab`, `…exteriorCollar`, `…neck`, `…pinchedRegion` (with
the algebra of `Basic.lean`), `…RealizedWindings`, `…HasOutsidePiece`, `…SliceLocallyTwoSided`,
and the loop-level forms `…PushOffDatum`, `…SlicePushOffSpan`.

## Closing the crux with the input only for the smooth tori

`Work.BoxShrink.Bubble.SmoothPushOff` is the input restricted to the surfaces of the challenge
(`P = ParamTorus.mapHomeomorph ψ.toHomeomorph`, `ψ : Submission.Diffeo`), and
`Work.BoxShrink.Bubble.RestrictedInput` is the corresponding restricted form of the field `bubble`.
`Work.BoxShrink.Bubble.cruxCore_of_smoothPushOff` and
`Work.BoxShrink.Bubble.crux_of_smoothPushOff` re-prove Pardon's double-bubble core and the whole
crux from that restricted datum (together with `BubbleInput.cleansInDisc`, `CleansDiscsAll`,
`AeSlicedAll`) — the verbatim replay of `Work.BoxShrink.Core.cruxCore_of_bubbleInput`, whose only
use of the field is at `P = ParamTorus.mapHomeomorph ψ.toHomeomorph`.  So the crux needs the input
**only for the smooth surfaces of the challenge**, where the parameter-plane flow
(`slicePushOff_of_planeFlow`) and the local model (`SlicePushModel`) are the available routes.

## THE FIELD IS FALSE — the counterexample

**`Work.BoxShrink.Core.BubbleInput.bubble` is not provable: it is false as stated.**  The counterexample
(`Work.BoxShrink.Bubble.standard_counterexample`, `standard_counterexample.lean`) is the standard torus
of revolution with `s = 5/2`, `c = 0`, `σ = Equiv.swap 1 2` (so the cut plane is `{y = 0}`) and `u = 0`:

* `¬ standard.ContainsEssentialLoop (sphereSet 0 (swap 1 2) (5/2))` (`hS` holds): the box misses two
  discs of the torus, and its boundary meets `F` in the two circles bounding them;
* the slice is **two arcs** (`p.1 ∈ {0, π}`, `p.2 ∈ (π/3, 5π/3)`), so
  `¬ standard.ContainsEssentialLoop (sliceRegion …)` (`hZ` holds);
* `(1,0) ∈ RealizedWindings boxRegion` (the longitude `{z = -1}` of radius `2` lies in the box) but
  `(1,0) ∉ RealizedWindings (upperRegion ∪ lowerRegion)` (every loop of a half-region stays on one
  side of `{y = 0}`, hence has vanishing first winding coordinate).

Hence `¬ SlicePushOff` (`cex_not_slicePushOff`), `¬ SlicePushOffSpan`
(`cex_not_slicePushOffSpan`) and — by `Work.BoxShrink.Bubble.bubbleSweep_nonempty_iff_slicePushOff` —
`¬ Nonempty (BubbleSweep standard (5/2) 0 (swap 1 2) 0)` (`cex_not_nonempty_bubbleSweep`).
`Refutation.lean` draws every consequence a caller needs:

* `Work.BoxShrink.Bubble.no_bubble_field` — **there is no term of the exact type of the field
  `BubbleInput.bubble`**;
* `Work.BoxShrink.Bubble.not_nonempty_bubbleInput` — `Work.BoxShrink.Core.BubbleInput` is **not
  inhabited**, so `Work.BoxShrink.Core.crux_of_bubbleInput` / `Work.BoxShrink.Core.crux` (and hence
  `Submission/Work/BoxShrink/assemble.lean`) can never be applied;
* `Work.BoxShrink.Bubble.not_nonempty_physicalBubbleInput` — the same for
  `Work.BoxShrink.Core.PhysicalBubbleInput`;
* `Work.BoxShrink.Bubble.not_smoothPushOff` and `not_nonempty_restrictedInput` — **the restricted
  interfaces of `Restricted.lean` are false too**: the counterexample is the standard torus, i.e. the
  image of itself under the identity diffeomorphism (`mapHomeomorph_idDiffeo_eq_standard`), so
  restricting the field to the smooth tori of the challenge does not help, and no amount of work on
  the analytic push-off (`Smooth/*`: the box gauge, the flow of `auxFun`, the Sard/critical-value
  statements) can repair it.

Diagnosis (Pardon, Lemma `spherefamily`): he applies the counting hypothesis to *every* intermediate
sphere `S_t`, and his local model is only "a single surgery changes
`dim im(H₁(F ∩ int S_t; ℚ) → H₁(F; ℚ))` by at most one" together with the dichotomy
`dim ∈ {0, 2g}`.  Our `Work.SurgeryInvariance.SweepLoops` local models
(`RegionEquivalent`, `SurgeryStepZero`) preserve the winding span *exactly*, which is strictly
stronger, and is what makes the conclusion false.  The hypotheses `hS`, `hZ` are only the endpoints
of Pardon's family; at an intermediate time the sphere must cut a *meridian* of the torus, which is
essential.

## The corrected interface

`Corrected.lean`:

* **`Work.BoxShrink.Bubble.BubbleHalf P s c σ u`** — Pardon's Lemma 3 conclusion at the loop level:
  `P.ContainsEssentialLoop (boxRegion …) → P.ContainsEssentialLoop (upperRegion …) ∨
  P.ContainsEssentialLoop (lowerRegion …)` — the exact statement the shrinking step consumes;
* **`Work.BoxShrink.Bubble.PushOffHalf`** and **`Work.BoxShrink.Bubble.SmoothHalf`** — the corrected
  field: `hS → hZ → BubbleHalf`, for all parametrised tori resp. for the smooth tori of the
  challenge;
* the corrected field is implied by every form of the old one
  (`bubbleHalf_of_bubbleSweep`, `bubbleHalf_of_slicePushOff`, `bubbleHalf_of_slicePushOffSpan`,
  `pushOffHalf_of_bubbleSweepAll`, `pushOffHalf_of_pushOffInput`, `smoothHalf_of_smoothPushOff`), so
  it is not refuted by the counterexample — and at the counterexample configuration it *holds*
  (`Work.BoxShrink.Bubble.bubbleHalf_cex`, from the meridian circle `{p.1 = π/2}` of winding `(0,1)`
  lying in `upperRegion`: `Work.BoxShrink.Bubble.cex_upperRegion_essential`);
* **the whole shrinking step with the corrected field**:
  `Work.BoxShrink.Bubble.cruxCore_of_pushOffHalf`, `crux_of_pushOffHalf`,
  `cruxCore_of_smoothHalf`, `crux_of_smoothHalf` — verbatim replays of
  `Work.BoxShrink.Core.cruxCore_of_bubbleInput`;
* **`Work.BoxShrink.Bubble.bubbleHalf_of_sweep`** — the corrected conclusion from the *library's own*
  vocabulary: a `Work.SurgeryInvariance.Sweep` from the box region to the two half-regions
  *together with the interior of an embedded disc* (`Work.SurgeryInvariance.Sweep.double_bubble`,
  Pardon's perturbed double bubble);
* **drop-in replacements for the caller's structure**: `Work.BoxShrink.Bubble.BubbleInputHalf`
  (the field's conclusion weakened from `BubbleSweep` to `BubbleHalf`) with
  `Work.BoxShrink.Bubble.crux_of_bubbleInputHalf`, and `Work.BoxShrink.Bubble.BubbleInputPardon`
  (the field replaced by Pardon's own `PinchDatum`) with
  `Work.BoxShrink.Bubble.crux_of_bubbleInputPardon`.

## Pardon's own local model (`PardonLocalModel.lean`)

The isolated input that a caller should supply instead of the field:

* `Work.BoxShrink.Bubble.SurgeryStepSmall` — Pardon's local move (the region gains or loses an open
  piece of the surface of winding span `≠ ⊤`, i.e. of dimension at most one);
* `Work.BoxShrink.Bubble.PardonDichotomy P X` — `WindingSpan P X = ⊥ ∨ WindingSpan P X = ⊤`
  (Pardon's equation (1));
* `Work.BoxShrink.Bubble.bot_iff_of_surgeryStepSmall` — with the dichotomy, a small step preserves
  the vanishing of the winding span (Pardon's argument: the dimension is `0` or `2g` and changes by
  at most one);
* `Work.BoxShrink.Bubble.SweepLoopsSmall` + `SweepLoopsSmall.bot_iff`,
  `SweepLoopsSmall.containsEssentialLoop_iff`, `SweepLoopsSmall.containsEssentialLoop_of_lt_one` —
  Pardon's Lemma `spherefamily` for the corrected local models, **for the parameters before the
  pinch** (the dichotomy is required only for `t < 1`: see `PinchEndgame.lean`);
* `Work.BoxShrink.Bubble.not_bot_of_surgeryStepSmall_of_top` and
  `Work.BoxShrink.Bubble.containsEssentialLoop_of_surgeryStepSmall` — the endgame step: a piece of
  dimension at most one cannot destroy the essential loop;
* **`Work.BoxShrink.Bubble.PinchDatum P s c σ u`** — the pinch datum of the box/plane configuration
  (Pardon's local models, the dichotomy at every parameter `t < 1`, the endpoint regions
  `boxRegion` and `upperRegion ∪ lowerRegion`, and the `pinch` endgame field: the essential loop of
  some pre-pinch region survives to the final region — Pardon's "the property of having a genus-`g`
  component is preserved under sufficiently small perturbations of the sphere"), with
  **`Work.BoxShrink.Bubble.bubbleHalf_of_pinchDatum`** (Pardon's Lemma 3) and the global
  `Work.BoxShrink.Bubble.PardonPinchInput` +
  `Work.BoxShrink.Bubble.pushOffHalf_of_pardonPinchInput`;
* consistency: a `Work.BoxShrink.Core.BubbleSweep` plus the dichotomy at the region gives a
  `PinchDatum` (`pinchDatum_of_bubbleSweep`), so the corrected input is strictly weaker than the old
  field.

### The corrected conclusion in every previously proved case (`HalfInstances.lean`)

`Work.BoxShrink.Bubble.bubbleHalf_of_not_hasEssBox`, `…_of_span_bot`, `…_of_empty_slice`,
`…_of_sliceOpen`, `…_of_finite_slice`, `…_of_countable_slice`, `…_of_discRoute`,
`…_of_neckComponent`, `…_of_belowPlateau`, `…_of_abovePlateau`: `BubbleHalf` in all the
configurations in which the chapter proves the old input, so the corrected interface is usable
immediately there (everything else follows from `bubbleHalf_of_slicePushOff` /
`bubbleHalf_of_bubbleSweep`).

`PinchEndgame.lean` proves that the restriction of the dichotomy to `t < 1` is *essential*: at the
counterexample configuration the region at the pinching parameter is `upperRegion ∪ lowerRegion`,
whose winding span is the line `ℚ·(0,1)` — neither `⊥` (it contains the meridian of winding `(0,1)`)
nor `⊤` (it misses `(1,0)`): `Work.BoxShrink.Bubble.cex_not_pardonDichotomy_union`.  A pinch datum
requiring the dichotomy at *every* parameter is refuted there; the endgame has to be
`PinchDatum.pinch`, exactly as in Pardon's proof (his last step is an inclusion argument, not the
dichotomy).

`MIGRATION.md` (same directory) is a ready-to-paste note for the files outside this directory that
still name the false field (`Core/Bubble/Defs.lean`, `Core/Crux.lean`, `assemble.lean`,
`inputs.lean`); the definitions it switches to live in `HalfDefs.lean`, whose imports are small
enough to be used there without a cycle, and `MigrationProbe.lean` typechecks the two patches (it
imports both `Core.Bubble.Defs` and `HalfDefs`, and replays the crux with the migrated
structures).

### The dichotomy API (`Dichotomy.lean`)

`Work.BoxShrink.Bubble.PardonDichotomy P X` (`WindingSpan P X = ⊥ ∨ WindingSpan P X = ⊤`) is the
only geometric hypothesis of `PinchDatum` beyond the shape of the family.  Its elementary closure
properties are proved in `Dichotomy.lean`: `pardonDichotomy_empty`, `pardonDichotomy_carrier`,
**`pardonDichotomy_union`** (a union of disjoint open pieces of the surface inherits the dichotomy,
`Span.union_eq_sup`), `pardonDichotomy_congr`,
`pardonDichotomy_of_subset_of_span_eq_top`, and the two instances for the box:
`pardonDichotomy_boxRegion_of_carrier_subset` (the box contains the whole surface — a configuration
where `hS` holds and the dichotomy is a theorem) and `pardonDichotomy_boxRegion_of_disjoint` (the
degenerate case).  At the counterexample configuration the dichotomy holds on the `⊤` side
(`cex_pardonDichotomy_boxRegion`, from `cex_windingSpan_boxRegion_eq_top`: the box region realises
both `(1,0)` — the longitude `{z = -1}` — and `(0,1)` — the meridian `{p.1 = π/2}`), while
`cex_not_slicePushOffSpan` bounds the union of the halves by `ℚ·(0,1)`: so the failure of the field
is exactly the failure of the *intermediate* spheres, not of the initial one.

What remains for a full proof of the corrected interface is thus exactly
`PardonPinchInput`: the construction of the pinching family together with Pardon's dichotomy at every
intermediate sphere.  The dichotomy is the surface-theoretic content of the counting hypothesis
(`Work.InnermostDisk`, `Work.BoxShrink.Core.Counting`); it is *not* a statement about winding spans
alone, and it is false for the local models of `SweepLoops` (the counterexample exhibits an
intermediate region — an annulus around a meridian — whose span is a line).  Everything else in the
chapter is proved, sorry-free and axiom-free.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

end Work.BoxShrink.Bubble
