import Mathlib
import Submission.Work.Drive.EpsForm.Defs
import Submission.Work.Drive.EpsFormSphere.Defs
import Submission.Work.Drive.not_exists_weakCompressingLoop_of_counts
import Submission.Work.BoxShrink.PinchOff.regionEquivalent_halves_of_tameSlice
import Submission.Work.InnermostDisk.Slicing
import Submission.Work.BoxShrink.PinchOff.windingSpan_bot_or_top_of_inessential_boundary
import Submission.Work.Step2.Solid
import Submission.Work.BoxShrink.Pinch.Level
import Submission.Work.Drive.EpsFormSphere.Sideways
import Submission.Work.Drive.EpsForm.span_const_of_sweep_axioms_of_finrank_jumps
import Submission.Work.Drive.EpsForm.not_cleansDiscsW_mapHomeomorph
import Submission.Work.Drive.EpsForm.exists_innermostDisc_essential_winding

/-!
# Pardon's Lemma 3 in the ε-form (region level): state of play

`Work.Drive.CountingHalfEps` (`EpsForm/Defs.lean`) is Pardon's `doublebubble2` conclusion at the
crux configurations: from the counted data of the crux, for every `ε > 0` an essential loop of the
surface lies within Euclidean distance `ε` of `upperRegion` or of `lowerRegion` (the traces on `F` of
the two halves of the box double bubble).  It is the residual consumed by
`Submission/Work/Drive/pardon_of_cleansW_region.lean` (`boxShrink_of_cleansW_eps`,
`pardon_of_cleansW_region_of_eps`).

## What is proved about it in this workspace

* **Relation to the exact form.**  The ε-form is *strictly weaker* than the exact counted form
  `Work.BoxShrink.Pinch.CountingHalf` / `Work.Drive.CountingHalfW`, whose conclusion
  (`Work.BoxShrink.Bubble.BubbleHalf`) demands the essential loop *inside* one of the two open
  half-regions: `Work.Drive.countingHalfEps_of_countingHalfW` (`EpsForm/Defs.lean`).  The hypotheses
  of the two statements are *verbatim* the same (in particular the weak cut-and-paste hypothesis
  `Work.Drive.CleansDiscsW`).
* **Relation to the other ε-forms.**  `CountingHalfEps` implies the solid form
  `CountingHalfEpsBody` (`countingHalfEpsBody_of_countingHalfEps`) and the sphere-level form
  `Work.Drive.EpsSphere.CountingHalfEpsSphere`; the *shifted* form
  `Work.Drive.EpsSphere.ThickHalfShifted` (`EpsFormSphere/Defs.lean`) is what the halving geometry of
  `Work.BoxShrink.halving` consumes, and it is implied by both ε-forms.
* **What the counting gives, in the weak vocabulary.**  Pardon's Lemma 2 in the W-disc vocabulary is
  complete:
  * `Work.Drive.not_exists_weakCompressingLoop_of_counts` (proved, this file's sibling): an essential
    simple loop of `F` lying in a low-count sphere and bounding a *continuous* disc whose open part
    misses `F` meets the knot in at least `min p q` points (the homological dichotomy
    `Work.CoreTopology.compressing_winding_dichotomy` replaces the embedded disc, and the
    intersection-number bounds for the meridian/longitude classes give the estimate);
  * `cleansingW_of_inputs` (below): the weak counterpart of
    `Work.InnermostDisk.cleansInSphere_of_inputs`, producing a simple essential curve of the sphere
    with a *continuous* disc from an innermost-disc input and the weak cut-and-paste at the
    innermost discs;
  * `sphereTrace_inessential_of_countsW` (below): the conclusion — the box-sphere trace carries no
    essential loop — from the crux's sphere count, the general position of the sphere
    (`SlicedSphere`) and the ε-form's own weak cut-and-paste hypothesis `CleansDiscsW`.  This is
    `Work.PinchCounted.sphereTrace_inessential_of_counts` with `CleansDiscs` weakened to
    `CleansDiscsW`, and it is the endpoint fact the ε-form's proof consumes.

## Why the ε-form is not discharged here

0. **What is still missing is Pardon's pinching family, and only that.**  With the endpoint
   inessentialities of the counting now available in the weak vocabulary (see above) and the span
   constancy of `Work.SurgeryInvariance.Sweep`, the ε-form would follow from the family
   `Work.BoxShrink.Pinch.PinchFamily` (`bubbleHalf_of_pinchFamily`, hence
   `Work.Drive.countingHalfEps_of_countingHalfW`); nothing else is missing.
1. **The pinch cannot be modelled by the library's surgery.**  A `2`-surgery of
   `Work.SurgeryInvariance.SurgeryShape`/`SurgeryShapeRaw` adds or removes a piece that is *clopen*
   in the region (`Work.BoxShrink.Pinch.Warning.surgeryStepSmall_grow_or_empty`,
   `Work.BoxShrink.Bubble.Obstruction.surgeryStepZero_eq_self_or_empty`), so a preconnected region
   cannot be shrunk to the two halves by it; Pardon's pinch shrinks the box region through a neck
   whose trace is not clopen.  Consequently the explicit family of `Work.Step2`
   (`pinchSolid`/`pinchRegion`) has the right endpoints but *not* the local models
   (`Work.Step2.not_isOpenInCarrier_neckPiece_of_accumulating`), and the sphere-level route
   (`Work.Drive.EpsSphere.PinchEps`, `SphereSweep`) has been withdrawn for the same reason
   (`EpsFormSphere/Defs.lean`).
2. **The remaining route keeps the degenerate step as an explicit endgame hypothesis.**
   `Work.BoxShrink.Pinch.PinchFamily` (with the field `endgame`) gives Pardon's exact conclusion
   (`bubbleHalf_of_pinchFamily`), but its `endgame` field *is* the pinch, so a proof of the ε-form
   through it assumes Pardon's Lemma 3 itself.  The conditional constructions of
   `Work.BoxShrink.Pinch.Construct` (`pinchFamilyOfSlicePushOff`, `pinchFamilyOfRegionEquivalent`)
   reduce the pinch to a transport/push-off datum, which is false without the counting
   (`Work.BoxShrink.PinchOff.not_transport`) and is the counted residual of `Work.PinchCounted` /
   `Work.PinchFamily`.
3. **The two inessentiality statements alone are insufficient (machine-checked).**  At the
   `RefuteDrop` configuration (`Work.BoxShrink.PinchOff.RefuteDrop`) both `TransverseSlice`,
   `TameClosedSlice` and the two inessentialities `hS`, `hZ` hold while `W(boxRegion) = ⊤` and
   `W(halves) = ⊥`; so the counting has to be spent at *every intermediate sphere of the pinch*,
   which is exactly the construction that is missing.

## A new lead for the arcs case: the *half-spheres* are clean

Pardon's Lemma 2 (`mustbeinessential`) is about *closed curves in a sphere*, and the crux's two
counts bound the intersections of `β` with the box sphere `∂PBox s c σ` (`≤ 75 d`) and with the flat
disc `D = cutDisc s c σ u` (`≤ 37.5 d`).  Applying it to the two *half-spheres* of the double
bubble --- `H₊ = closedUpperCap ∪ D` and `H₋ = closedLowerCap ∪ D` --- therefore gives **more** than
the two endpoint inessentialities `hS`, `hZ` which the chapter has been using:

* `|H₊ ∩ β| ≤ |closedUpperCap ∩ β| + |D ∩ β| ≤ 112.5 d < 150 d < min p q`, and likewise for `H₋`;
* hence (given a general-position slicing of `H₊` and the weak cut-and-paste `CleansDiscsW`, which
  is *proved*: `Work.Drive.cleansDiscsAllW`) **every closed curve of `F` whose image lies in `H₊` is
  inessential in `F`** --- and the same for `H₋`.  The general form of the counting step is
  `Work.Drive.EpsForm.trace_inessential_of_slicing_of_countsW` above.

This is exactly the "cleanliness of the pinching sphere" which Pardon's Lemma 1 consumes, but here
it is available *without* any one-parameter family: `H₊` and `H₋` are the two spheres at which the
pinch ends.  The intended use is the **peeling** lemma
`Work.BoxShrink.PinchOff.windingSpan_sdiff_biUnion_range_eq`: the components of `F ∩ H₊` are
pairwise disjoint simple inessential closed curves of `F`, and deleting them from a region does not
change its winding span.  Since `F ∩ (H₊ ∪ H₋) = F ∩ (∂PBox s c σ ∪ D)` and
`boxRegion ∖ (∂PBox ∪ D) = upperRegion ∪ lowerRegion`, the peeling would give directly

  `WindingSpan P (boxRegion P s c σ) ≤ WindingSpan P (upperRegion ∪ lowerRegion)`,

i.e. Pardon's counted Lemma 3 (`Work.SliceArcs.ArcSpan`), and hence this module's target.  What has
to be settled before this becomes a proof is *bookkeeping*: the peeling lemma requires the peeled
curves to be contained in the region they are peeled from, and the components of `F ∩ H₊` are not
(the Γ-parts run through `∂PBox ∖ PBox`).  Two ways to finish, both needing a genuine argument:

* peel the pieces of those components that lie inside the box --- i.e. the *arcs* of the slice,
  which are not closed curves --- after sliding each crossing along its arc to the arc's endpoint,
  where the Γ-circles (inessential by `hS`) supply the discs that let the crossing be pushed off;
* or peel from the ambient region `F ∩ PBox (s + δ)` (which contains the whole components) and
  control the extra shell `F ∩ (PBox (s + δ) ∖ closure (PBox s))`, where the *same* cleanliness
  argument applies to the shifted box and lets one pass to `δ → 0`.

The statements this reduces to are

* `halfSphereCountBound`: the crux's two counts give
  `Set.encard (Set.range K.curve ∩ H₊) < (Nat.min p q : ℕ∞)`;  and
* `halvesSpan_of_cleanHalfSpheres`: if `H₊` and `H₋` carry no essential curve of `F`, then
  `WindingSpan P (boxRegion P s c σ) ≤ WindingSpan P (upperRegion ∪ lowerRegion)`.

`halfSphereCountBound` and `footprintCountBound` below are the count half of this, and they are
**proved** (the `ℕ∞`-to-`ℝ≥0∞` arithmetic goes through `ENat.toENNReal_add` / `ENat.toENNReal_le`,
not the `NNReal` `ENNReal.coe_add` / `ENNReal.coe_le_coe`).  The argument was: split the parameter set
`{t ∈ Ico 0 2π | K.curve t ∈ H₊}` (the following paragraph records the original plan).  A historical note on
`ℕ∞`-arithmetic: split the parameter set `{t ∈ Ico 0 2π | K.curve t ∈ H₊}` into the box-sphere part
(`mem_sphereSet`) and the slice part (`mem_cutDisc`), bound the two parts by `hcountS`/`hcountU` after
normalising `10 (1+ε)/ε = 75` and `5 (1+ε)/ε = 75/2` (`Submission.eps = 2/13`), add them to
`112.5 d`, and apply `Work.BoxShrink.Core.encard_lt_of_coe_le_ofReal` with
`112.5 * d ≤ Submission.countConst * d = 150 d < min p q` and the parameter-to-range reduction
`encard (range K.curve ∩ S) ≤ encard {t ∈ Ico 0 (2π) | K.curve t ∈ S}` (periodicity of `K.curve`).
The only obstruction met was that the coercions `(x : ℕ∞) : ℝ≥0∞` are *not* `ENNReal.coe_add` /
`ENNReal.coe_le_coe` (those are the `NNReal` ones — `ENNReal.coe_add a` expected `NNReal`), so the
`ℕ∞`-addition and `ℕ∞`-monotonicity lemmas have to be looked up by name (the `ENat.toENNReal` API).

**Careful with the closed/open versions of `H±`** (found by a reviewer of the delegated lemma): with
the *open* cap `sphereSet ∩ upperHalf` and the *open* disc `cutDisc = PBox ∩ cutPlane`, the hypotheses
of the second lemma are strictly weaker than intended and the statement is FALSE: at
`P = Work.CoreTopology.standard`, `s = 5/2`, `c = 0`, `σ = swap 1 2`, `u = 0` the traces of both open
half-spheres are unions of open arcs (the gluing circle `∂(cutDisc) = sphereSet ∩ cutPlane` is in
neither), so `¬ ContainsEssentialLoop` holds for each while the conclusion fails
(`Work.BoxShrink.Bubble.cex_not_slicePushOffSpan`).  The correct datum is the *closed* cap
`sphereSet ∩ {y | c (σ 2) + u ≤ y (σ 2)}` together with `closure (cutDisc s c σ u)`; it is in that
form that the lemma is delegated (`Submission/Work/Drive/PinchArc/halvesSpan_of_cleanHalfSpheres`), and
that the counterexample is excluded (the loop arcing through the slice at `θ = 0` closed up by the
upper cap arc has winding `(0, 1)`).

**The slicing datum for `H±` is *not* free** (both reviewers of the would-be delegation
`Drive/PinchArc/upperHalfSphereSlicing` agreed, and it is therefore **not** delegated in that form):
`Work.BoxShrink.SlicedSphere (torus ψ) {y | boxNorm c σ y = s}` constrains only the box sphere, and
the half-sphere also contains the whole flat cutting disc.  A diffeomorphism can flatten a piece of
the torus onto an open subset of the cutting plane strictly inside the box while leaving the box
sphere's trace transverse (Sard), so `hS` holds while `SphereSlicing` of `H₊` fails outright
(`covers` cannot put a small loop in that open planar piece inside a finite curve family).  The
missing hypothesis is the general position of the *plane* (`CutDiscSliced` / `SlicedPlane`), which is
not derivable — the workspace refutes both its global and its almost-everywhere form
(`not_forall_transverseSlice`, `PlaneSlice.not_ae_transversePlane_pardonSlice`).  So the honest
residual of the assembly is the *pair* [general position of the cut disc] + [the peeling lemma]; the
composition of the counts with Lemma 2 at `S = H±` is already done, unconditionally, as
`trace_inessential_of_slicing_of_subset_footprint` above.

**How to spend the ε-slack on item 2 — *not* by moving the level `u`.**  The obvious reading of the
ε-form's slack ("perturb the cutting plane a little") does not work as a general route: moving `u` to
`u'` changes the *hypotheses* (the count `hcountU` is stated for the level `u`, and no averaging
recovers it at `u'` without redoing Pardon's sweep), and the transversality one would want at `u'` is
itself refuted in the workspace — `PlaneSlice.not_ae_transversePlane_pardonSlice` kills the
almost-everywhere form as well as the global one (`not_forall_transverseSlice`).  The faithful route
is the one Pardon actually takes in the proof of `doublebubble2`: perturb the **double bubble**
`(S, D)` — his `straighteninglemma` at each intersection with `β`, then general position — keeping
the count `|S ∩ β| + 2 |D ∩ β|` (`(fewint)`) and reading the conclusion in the `ε`-neighbourhood of
the *unperturbed* half-regions, since the perturbed halves are within `ε` of the original ones.  That
is a statement about a *perturbed disc* `D'` (with `F ∩ D'` sliced and `F ∩ H'±` clean), not about a
perturbed plane; the count at `D'` stays controlled because `D'` is a small perturbation of `D` and
the count is discrete (`|β ∩ D'| = |β ∩ D|` for a perturbation avoiding `β` transversally at the
critical instants).  This is the honest form of item 2 and the natural next delegation.

**The item-2 machinery already exists, in the sibling `Submission/Work/Drive/EpsForm/Sliced.lean`.**
That file carries the vocabulary this module's residual needs and should be read first by anyone
continuing here: `CutDiscSliced` (the planar general-position datum, `= SlicedPlane P (cutDisc …)`),
`CutDiscCleaned` (its *cleaning* form), the proved almost-everywhere cleaning
`ae_cutDiscCleaned_of_cleansDiscsAll`, the innermost/cleaning consequences at the flat disc
(`innermostDiscInput_cutDisc`, `cleansInSphereW_cutDisc`,
`not_containsEssentialLoop_sliceRegion_of_sliced`), the **shift lemmas** `abs_lt_boxSide_mul`,
`half_gap_pos`, `abs_add_shift_le'`, the **sweep statement** `exists_plane_level_datum` ("the plane
level can be chosen where the cut disc is cleaned"), and the *shifted-endpoint* residuals
`CruxCoreSliced` / `ShiftedEndpointSliced` / `CruxCoreCleaned` / `ShiftedEndpointCleaned` together
with `shiftedEndpoint_of_cruxCoreSliced`, `epsConclusion_mono` and
`epsConclusion_of_shiftedEndpoint(Cleaned)`.  So the ε-shift of the plane exists precisely as a
*shifted* statement (with the counts transported along the shift by `abs_add_shift_le'`), which is
why moving the level was refuted *unshifted*: the surviving form is the shifted one.  The natural
next step is therefore to wire this module's proved bricks — `halfSphereCountBound` and
`trace_inessential_of_slicing_of_subset_footprint` (cleanliness of any footprint-contained sliced
sphere), with the in-flight `halvesSpan_of_cleanHalfSpheres` — into `ShiftedEndpointCleaned` /
`CruxCoreCleaned` rather than to look for a new general-position theorem.

**The peeling route is REFUTED: cleanliness of the two end-spheres does *not* give the span
containment.**  The delegated lemma `Drive/PinchArc/halvesSpan_of_cleanHalfSpheres` was returned
FALSE by its prover, with a documented counterexample (`_explore/COUNTEREXAMPLE.md` there):
`P = standard`, `s = 1`, `c = (0,0,1)`, `σ` the 3-cycle `σ 0 = 2, σ 1 = 0, σ 2 = 1`, `u = 0` — then
`boxRegion` contains the full longitude `φ = 2.5` (winding `(1,0)`) while every closed curve of the
torus inside either half has winding `(0,0)`, so `W(boxRegion) ≤ W(halves)` **fails**; and at that
configuration the trace of `H₊` on the torus is a *single* closed curve of winding `(0,0)` (seven
arcs joined at five junctions), so both cleanliness hypotheses hold.  Consequently the route
"cleanliness of `H±` (from the counting, `trace_inessential_of_slicing_of_subset_footprint`) ⟹
peeling ⟹ `W(box) ≤ W(halves)`" is dead, and the counting cannot be spent at the two endpoint
spheres alone: it has to be spent at *every intermediate sphere of the pinching family*, exactly as
the ledger (`Submission/Work/BoxShrink/ledger.lean`) and `Work.PinchCounted` already state.  The
bricks proved here (`footprintCountBound`, `halfSphereCountBound`,
`trace_inessential_of_slicing_of_subset_footprint`, `containsEssentialLoop_upper_or_lower`,
`bubbleHalf_of_span_le_halves`) remain the right pieces — they are exactly what the *family* consumes
at each of its spheres — but the family itself is irreducible.

**The exact residual, and where each brick here plugs in.**  Reading `EpsForm/Sliced.lean` further: its
`CruxCoreSliced` is the crux's hypothesis list *plus* the planar general-position datum
`CutDiscSliced (torus ψ) s c σ u`, concluding the exact half-containment; and its
`ShiftedEndpointSliced` / `CruxCoreCleaned` / `ShiftedEndpointCleaned` are the ε-shifted and
disc-*cleaning* variants, the last of which (thanks to the proved a.e. statement
`ae_cutDiscCleaned_of_cleansDiscsAll` and the sweep statement `exists_plane_level_datum`) does **not**
assume the non-derivable `CutDiscSliced`.  So the honest residual of this module's target is
`ShiftedEndpointCleaned`, and the division of labour between this file and that one is:

* `ShiftedEndpointCleaned` (in `EpsForm/Sliced.lean`) ⟹ the ε-conclusion, via its
  `shiftedEndpointSliced_of_cleaned`, `epsConclusion_of_shiftedEndpointCleaned`, `epsConclusion_mono`;
* in the *other* direction, the bricks proved here are what a proof of that residual consumes:
  `footprintCountBound` + `trace_inessential_of_slicing_of_subset_footprint` at each sphere of the
  pinching family (cleanliness from the counts), `containsEssentialLoop_upper_or_lower` and
  `bubbleHalf_of_span_le_halves` to finish once the family's span constancy has been transported to
  the halves, and `encard_range_inter_le_param` for the parameter-to-intersection bookkeeping;
* the family itself (`Work.BoxShrink.Pinch.PinchFamily`, `Work.PinchCounted.*`) remains irreducible:
  the refuted peeling above shows the counting cannot be spent at the endpoint spheres alone, and
  `ShiftedEndpointCleaned` already carries the `CutDiscSliced`-free replacement for the plane datum.

**The first `2`-surgery obstruction is *already a proved dichotomy*, and the positive direction is
the assembly point for the bricks of this module.**  `Work.Step2` (both files sorry-free) contains:

* `Work.Step2.not_isOpenInCarrier_neckPiece_of_accumulating` — at a parameter where points of the
  surface inside the box accumulate at the critical level `|y (σ 2) - (c (σ 2) + u)| = r - 1`, the
  neck piece is **not** open in the carrier, so the nested family's change there is not a
  `SurgeryStepZero`;
* `Work.Step2.isOpenInCarrier_neckPiece_of_forall_ne` — conversely, if the surface meets no point of
  the box on that critical level (`hgen`), the neck piece **is** open;
* `Work.Step2.countedStep_pinchRegion_of_subset_sphere` — and then the counted step of the explicit
  family at `(t, r)` follows, from [the neck piece lies in a sphere `S`], [`CleansInSphere P S`],
  [`S ⊆ footprint s c σ u`], [Pardon's inequality `|S ∩ β| + 2 |D ∩ β| < I(F,β)`] and [openness].

So the first obstruction is not open work: it is a *dichotomy*, and the usable branch is exactly the
one the `ε`-slack can be spent to reach (perturb the disc so that the critical level is missed).  Note
where this module's bricks enter that existing theorem: `hclean : CleansInSphere P S` for a sphere `S`
containing the neck piece is supplied by `Work.InnermostDisk.SphereSlicing.innermostDiscInput_of_slicing`
together with `Work.Drive.CleansDiscsW` (the weak cut-and-paste, *proved* as
`Work.Drive.cleansDiscsAllW`), and the counting side — `hS ⊆ footprint` with Pardon's inequality — is
`footprintCountBound`/`halfSphereCountBound`; the dichotomy at every parameter is
`pardonDichotomy_of_slicing_of_subset_footprint`.  The remaining genuine work is therefore *not* the
neck openness, but (i) producing parameter pairs where `hgen` holds (the family's general position, on
the disc side already available in `EpsForm/Sliced.lean`) and (ii) the pinching parameter itself, which
the workspace isolates in `Work.BoxShrink.Pinch.PinchFamily.endgame`.

**The one mismatch to settle before wiring the socket.**  `Work.Step2.countedStep_pinchRegion_of_subset_sphere`
takes its cleaning hypothesis in the *strong* form `Work.InnermostDisk.CleansInSphere P S` (an
embedded bounding disc), whereas what is available for this module's configurations is the *weak*
form: `Work.Drive.CleansDiscsAllW` is proved, and the bricks here
(`trace_inessential_of_slicing_of_subset_footprint`, `not_exists_weakCompressingLoop_of_counts`) are
stated for *continuous* discs whose open part misses the surface.  So the socket to instantiate is
the weak analogue of that theorem — same hypotheses with `CleansInSphere` replaced by its weak
counterpart (obtained from a `SphereSlicing` of `S` via
`Work.InnermostDisk.SphereSlicing.innermostDiscInput_of_slicing` plus `CleansDiscsW`, cf.
`Work.Drive.cleansingW_of_inputs`) — and *that* is the delegation that carries the remaining work,
not a reproof of the neck geometry.  With `S` taken to be the intermediate pinching sphere `S_t`
(the neck piece is its trace-band, so `neckPiece ⊆ S_t` and `S_t ⊆ footprint` is Pardon's "by
construction"), the residue after the instantiation is exactly: (i) the slicing datum for `S_t`
(general position), (ii) `hgen` at every regular parameter pair, and (iii) the pinching parameter
(`Work.BoxShrink.Pinch.PinchFamily.endgame`).

A sanity check on the second: in the simplest shape (a single arc of the slice whose endpoints lie
on one Γ-circle, with the Γ-disc bounded by it), cleanliness forces `F = S²` by the Euler
characteristic count of the gluing of the disc bounded by the arc's companion circle, the other
companion disc and the Γ-disc, so a torus cannot present that shape --- consistent with cleanliness
being exactly what rules out the counterexample configurations
(`Work.BoxShrink.PinchOff.RefuteDrop`, `Work.SliceArcs.not_arcSpanBody_s18`).

-/

namespace Work.Drive.EpsForm

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal


/-! ## Pardon's Lemma 2 in the weak-disc vocabulary: the trace inessentiality

The counting enters Pardon's argument through the fact that the trace `F ∩ ∂PBox s c σ` carries no
essential loop.  The library proves this with the *strong* cut-and-paste input
(`Work.PinchCounted.sphereTrace_inessential_of_counts`, through
`Work.InnermostDisk.mustbeinessential_of_cleansInSphere`, which needs an *embedded* disc).  In the
vocabulary of this file the cut-and-paste hypothesis is the weak `Work.Drive.CleansDiscsW`, and the
replacement for the embedded disc is the *homological* argument of
`Work.Drive.not_exists_weakCompressingLoop_of_counts` (proved): a continuous disc whose open part
misses `F` has its (connected) interior in one component of `ℝ³ ∖ F`, so the winding vector of its
boundary is a multiple of the meridian or of the longitude, and the intersection-number bound for
those two classes gives back `|α ∩ β| ≥ min p q`.  What remains is Pardon's *first* innermost step
(`Work.InnermostDisk.SphereSlicing.innermostDiscInput_of_slicing`: the slicing of the sphere
provides an innermost curve, which is simple and essential as soon as the trace has an essential
loop), after which `CleansDiscsW` supplies the continuous disc for that curve.  This is the weak
counterpart of `cleansInSphere_of_inputs` (`Work.InnermostDisk.Reduction`). -/

/-- **Pardon's Lemma 2, first half, in the weak-disc vocabulary**: an innermost-disc input plus the
weak cut-and-paste at the innermost discs produce a *simple essential* curve of the sphere which
bounds a continuous disc whose open part misses `F`. -/
theorem cleansingW_of_inputs {P : Work.CoreTopology.ParamTorus} {S : Set R3}
    (hIn : Work.InnermostDisk.InnermostDiscInput P S)
    (hCl : ∀ D : Work.InnermostDisk.InnermostDisc P S, Work.Drive.BoundsDiskInComplementW P D.α) :
    ∀ α : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P α →
      (∀ t : ℝ, α t ∈ S) →
      ∃ α' : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsSimple P α' ∧
        Work.CoreTopology.IsEssential P α' ∧ Work.Drive.BoundsDiskInComplementW P α' ∧
        ∀ t : ℝ, α' t ∈ S := by
  intro α hα hαS
  obtain ⟨D⟩ := hIn ⟨α, hα, hαS⟩
  exact ⟨D.α, D.simple, D.essential, hCl D, D.mem⟩

/-- **The trace `F ∩ ∂PBox s c σ` carries no essential loop**, from the crux's sphere count, the
general position of the box sphere and the *weak* cut-and-paste input.  This is
`Work.PinchCounted.sphereTrace_inessential_of_counts` with `Work.InnermostDisk.CleansDiscs` replaced
by `Work.Drive.CleansDiscsW` — the hypothesis carried by the ε-form. -/
theorem sphereTrace_inessential_of_countsW
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hslice : Work.BoxShrink.SlicedSphere (Work.Smooth.Morse.torus ψ)
      {y : R3 | Submission.boxNorm c σ y = s})
    (hcl : Work.Drive.CleansDiscsW (Work.Smooth.Morse.torus ψ))
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d))) :
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) := by
  intro hcon
  have hIn : Work.InnermostDisk.InnermostDiscInput (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.sphereSet c σ s) :=
    Work.InnermostDisk.SphereSlicing.innermostDiscInput_of_slicing hslice.some
  obtain ⟨D⟩ := hIn hcon
  exact Work.Drive.not_exists_weakCompressingLoop_of_counts p q hp hq hc ψ K hd himg hsmall
    c σ hcount ⟨D.α, D.simple, D.essential, hcl _ D, D.mem⟩

/-! ## Pardon's Lemma 2 for an arbitrary slicing of a sphere

The two endpoint inessentialities of the counting (`hS` at the box sphere, `hZ` at the cutting disc)
are *instances* of Pardon's Lemma 2 (`mustbeinessential`) at the two spheres that bound the
configuration.  The argument below is the general statement: **any** sphere which is sliced by the
surface in general position and which meets the counted curve `β` in fewer than `I(F,β) = min p q`
points has inessential trace.  It is the piece of Pardon's Lemma 2 which the pinching family
consumes at *every intermediate sphere* `S_t` of his `2`-surgery (his count
`#(S_t ∩ β) ≤ #(S ∩ β) + 2#(D ∩ β)` supplies the hypothesis there), and it is stated here in the
weak-disc vocabulary so that it can be used with the weak cut-and-paste input `CleansDiscsW`.

Innermost input and cleaning are the first two steps (`SphereSlicing` plus `CleansDiscsW`), and the
third step is the counting: the innermost essential curve of the slicing is replaced by a simple
essential loop bounding a *continuous* disc whose open part misses the surface, which by
`Work.Drive.min_le_encard_inter_of_boundsDiskW` meets `β` at least `min p q` times, while it lies in
`S` and hence meets `β` no more often than `S` does. -/

/-! ## The count at the footprint (and hence at each half-sphere)

Pardon's Lemma 2 is applied below to the two *half-spheres* of the double bubble,
`H₊ = closedUpperCap ∪ cutDisc s c σ u` and `H₋ = closedLowerCap ∪ cutDisc s c σ u`.  Both are
subsets of the **footprint** `sphereSet c σ s ∪ cutDisc s c σ u`, so it suffices to bound the
intersections of the knot with the footprint: those split into the intersections with the box sphere
(`≤ 75 d` by `hcountS`) and with the flat disc (`≤ 37.5 d` by `hcountU`), i.e. at most `112.5 d`,
which is `< 150 d < min p q` by the crux's smallness hypothesis.  The same bound therefore holds for
each half-sphere (monotonicity of `Set.encard`), which is exactly the hypothesis of Pardon's Lemma 2
at `S = H±` (`Work.Drive.EpsForm.trace_inessential_of_slicing_of_countsW`). -/

/-- **The knot meets a set only through its parameters.**  For a set `S` of `ℝ³`, the intersections
of the knot curve with `S` are hit by parameters in the fundamental period `[0, 2π)`: this is the
reduction of the cardinality of `range K.curve ∩ S` to a cardinality of parameters, and it is the
step at which the two counts of the crux (which count *parameters*) are consumed. -/
theorem encard_range_inter_le_param (K : Knot) (S : Set R3) :
    Set.encard (Set.range K.curve ∩ S) ≤
      Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ S} := by
  refine le_trans (Set.encard_le_encard ?_) (Set.encard_image_le K.curve _)
  rintro y ⟨⟨t, rfl⟩, hyS⟩
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  set n : ℤ := ⌊t / (2 * Real.pi)⌋ with hn
  have hnle : (n : ℝ) ≤ t / (2 * Real.pi) := by rw [hn]; exact Int.floor_le _
  have hnlt : t / (2 * Real.pi) < (n : ℝ) + 1 := by rw [hn]; exact Int.lt_floor_add_one _
  have hle : 0 ≤ t - (n : ℝ) * (2 * Real.pi) := by
    have := (le_div_iff₀ hpos).mp hnle
    linarith
  have hlt : t - (n : ℝ) * (2 * Real.pi) < 2 * Real.pi := by
    have := (div_lt_iff₀ hpos).mp hnlt
    linarith
  have hper : Function.Periodic K.curve (2 * Real.pi) := K.periodic
  have hcurve : K.curve (t - (n : ℝ) * (2 * Real.pi)) = K.curve t :=
    hper.sub_int_mul_eq n
  exact ⟨t - (n : ℝ) * (2 * Real.pi), ⟨⟨hle, hlt⟩, by rw [hcurve]; exact hyS⟩, hcurve⟩

/-- **The knot meets the footprint of Pardon's double bubble in fewer than `min p q` points.**  If
the knot meets the boundary sphere `∂PBox s c σ` in at most `10 (1+ε)/ε · d` parameters and the flat
disc `cutDisc s c σ u` in at most `5 (1+ε)/ε · d` parameters, and `countConst · d < min p q`, then
the knot meets the footprint `sphereSet c σ s ∪ cutDisc s c σ u` in fewer than
`min p q = I(F, β)` points.  Since each of the two half-spheres of the double bubble is a subset of
the footprint, the same holds for each of them: this is exactly the hypothesis of Pardon's Lemma 2
at `S = H±` (`Work.Drive.EpsForm.trace_inessential_of_slicing_of_countsW`), the cleanliness of the
two spheres at which the pinch ends. -/
theorem footprintCountBound (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s : ℝ} (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (hcountS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
    (hcountU : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d))) :
    Set.encard (Set.range K.curve ∩ (Work.BoxShrink.Core.sphereSet c σ s ∪
      Work.BoxShrink.Core.cutDisc s c σ u)) < (Nat.min p q : ℕ∞) := by
  have h75 : 10 * (1 + Submission.eps) / Submission.eps * d = 75 * d := by
    rw [Submission.eps]; ring
  have h37 : 5 * (1 + Submission.eps) / Submission.eps * d = 75 / 2 * d := by
    rw [Submission.eps]; ring
  have h112 : (75 : ℝ) * d + 75 / 2 * d = 112.5 * d := by ring
  -- the parameter set of the footprint is the union of the two counted parameter sets
  have hset : {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      K.curve t ∈ (Work.BoxShrink.Core.sphereSet c σ s ∪
        Work.BoxShrink.Core.cutDisc s c σ u)}
      = {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          Submission.boxNorm c σ (K.curve t) = s}
        ∪ {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨ht, hy | hy⟩
      · exact Or.inl ⟨ht, Work.BoxShrink.Core.mem_sphereSet.mp hy⟩
      · exact Or.inr ⟨ht, (Work.BoxShrink.Core.mem_cutDisc.mp hy).1,
          (Work.BoxShrink.Core.mem_cutDisc.mp hy).2⟩
    · rintro (⟨ht, hy⟩ | ⟨ht, hb, hy⟩)
      · exact ⟨ht, Or.inl (Work.BoxShrink.Core.mem_sphereSet.mpr hy)⟩
      · exact ⟨ht, Or.inr (Work.BoxShrink.Core.mem_cutDisc.mpr ⟨hb, hy⟩)⟩
  have hA : (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      Submission.boxNorm c σ (K.curve t) = s}) : ENNReal) ≤ ENNReal.ofReal (75 * d) := by
    simpa [h75] using hcountS
  have hB : (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (75 / 2 * d) := by
    simpa [h37] using hcountU
  have hpar : (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      K.curve t ∈ (Work.BoxShrink.Core.sphereSet c σ s ∪
        Work.BoxShrink.Core.cutDisc s c σ u)}) : ENNReal) ≤ ENNReal.ofReal (112.5 * d) := by
    rw [hset]
    calc (↑(Set.encard ({t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}
            ∪ {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u})) : ENNReal)
        ≤ ↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}
            + Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}) := by
          rw [ENat.toENNReal_le]
          exact Set.encard_union_le _ _
      _ = (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            + ↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}) :=
          ENat.toENNReal_add _ _
      _ ≤ ENNReal.ofReal (75 * d) + ENNReal.ofReal (75 / 2 * d) := add_le_add hA hB
      _ = ENNReal.ofReal (112.5 * d) := by
          rw [← ENNReal.ofReal_add (mul_nonneg (by norm_num) hd)
            (mul_nonneg (by norm_num) hd), h112]
  have hmin : (112.5 : ℝ) * d < (Nat.min p q : ℝ) := by
    have hle : (112.5 : ℝ) * d ≤ Submission.countConst * d := by
      rw [Submission.countConst]
      nlinarith [hd]
    linarith
  refine lt_of_le_of_lt (encard_range_inter_le_param K _) ?_
  exact Work.BoxShrink.Core.encard_lt_of_coe_le_ofReal (n := Nat.min p q)
    (ne_of_gt (lt_min hp hq)) hpar hmin

/-- **The same count at each half-sphere of the double bubble.**  The upper half-sphere is
`(sphereSet c σ s ∩ upperHalf c σ u) ∪ cutDisc s c σ u` (the closed upper cap glued to the flat
disc), a subset of the footprint; the bound therefore follows from `footprintCountBound` by
monotonicity of `Set.encard`.  This is verbatim the hypothesis of Pardon's Lemma 2 at `S = H₊`
(`Work.Drive.EpsForm.trace_inessential_of_slicing_of_countsW`), i.e. the cleanliness of the sphere
at which the pinch ends. -/
theorem halfSphereCountBound (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s : ℝ} (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (hcountS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
    (hcountU : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d))) :
    Set.encard (Set.range K.curve ∩ ((Work.BoxShrink.Core.sphereSet c σ s ∩
      Work.BoxShrink.Core.upperHalf c σ u) ∪ Work.BoxShrink.Core.cutDisc s c σ u)) <
      (Nat.min p q : ℕ∞) := by
  refine lt_of_le_of_lt (Set.encard_le_encard ?_) (footprintCountBound p q hp hq K hd hsmall
    c σ u hcountS hcountU)
  intro x hx
  rcases hx with ⟨hxK, hxa | hxd⟩
  · exact ⟨hxK, Or.inl hxa.1⟩
  · exact ⟨hxK, Or.inr hxd⟩

/-! ## Wiring the peeling lemma into Pardon's conclusion

The step `W(boxRegion) ≤ W(upperRegion ∪ lowerRegion)` — the conclusion of the peeling of the two
clean half-spheres (`Work.Drive.PinchArc.halvesSpan_of_cleanHalfSpheres`) — combined with the crux's
`ContainsEssentialLoop (boxRegion)` gives Pardon's conclusion `Work.BoxShrink.Bubble.BubbleHalf`
directly, with no dichotomy at the halves: the two half-regions are disjoint and open in the surface,
so the transfer `Work.SurgeryInvariance.double_bubble_persistence_of_zero_span` (with the zero-span
piece `Z = ∅`) splits the essential loop of their union. -/

private theorem isOpenInCarrier_empty (P : Work.CoreTopology.ParamTorus) :
    Work.SurgeryInvariance.IsOpenInCarrier P (∅ : Set R3) := by
  rw [Work.SurgeryInvariance.IsOpenInCarrier]
  simp

private theorem windingSpan_empty (P : Work.CoreTopology.ParamTorus) :
    Work.SurgeryInvariance.WindingSpan P (∅ : Set R3) = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  rintro ⟨γ, -, hγ⟩
  exact hγ 0

/-- **An essential loop of the two half-regions lies in one of them.**  The halves are disjoint and
open in the surface, so with the zero-span piece `Z = ∅` Pardon's transfer
`Work.SurgeryInvariance.double_bubble_persistence_of_zero_span` splits an essential loop of their
union. -/
theorem containsEssentialLoop_upper_or_lower {P : Work.CoreTopology.ParamTorus}
    (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (h : P.ContainsEssentialLoop
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪ Work.BoxShrink.Core.lowerRegion P s c σ u)) :
    P.ContainsEssentialLoop (Work.BoxShrink.Core.upperRegion P s c σ u) ∨
      P.ContainsEssentialLoop (Work.BoxShrink.Core.lowerRegion P s c σ u) :=
  Work.SurgeryInvariance.double_bubble_persistence_of_zero_span
    (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
    (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)
    (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion P s c σ u)
    (isOpenInCarrier_empty P) (by simp) (windingSpan_empty P) (by simp) h

/-- **Pardon's Lemma 3 conclusion from the span containment `W(boxRegion) ≤ W(halves)`.**  This is
the last step of the assembly: the peeling of the two clean half-spheres gives the span containment,
and the crux gives `ContainsEssentialLoop (boxRegion)`; an essential loop of the box region is then
an essential loop of the halves, which splits. -/
theorem bubbleHalf_of_span_le_halves {P : Work.CoreTopology.ParamTorus}
    (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (h : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≤
      Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.upperRegion P s c σ u ∪ Work.BoxShrink.Core.lowerRegion P s c σ u)) :
    Work.BoxShrink.Bubble.BubbleHalf P s c σ u := by
  intro hbox
  have hne : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊥ :=
    (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr hbox
  have hne' : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u) ≠ ⊥ :=
    fun hbot => hne (le_bot_iff.mp (h.trans (le_of_eq hbot)))
  exact containsEssentialLoop_upper_or_lower s c σ u
    ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hne')

/-- **Pardon's Lemma 2 for an arbitrary slicing, weak-disc vocabulary.**  Let `S` be sliced by the
surface in general position (`Work.InnermostDisk.SphereSlicing`), suppose the weak cut-and-paste
`Work.Drive.CleansDiscsW` holds, and suppose `S` meets the knot `K` in fewer than `min p q` points.
Then no essential loop of the surface lies in `S`. -/
theorem trace_inessential_of_slicing_of_countsW
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    {S : Set R3} (hslice : Work.InnermostDisk.SphereSlicing (Work.Smooth.Morse.torus ψ) S)
    (hcl : Work.Drive.CleansDiscsW (Work.Smooth.Morse.torus ψ))
    (hcount : Set.encard (Set.range K.curve ∩ S) < (Nat.min p q : ℕ∞)) :
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop S := by
  intro hcon
  obtain ⟨D⟩ :=
    (Work.InnermostDisk.SphereSlicing.innermostDiscInput_of_slicing hslice) hcon
  have hle := Work.Drive.min_le_encard_inter_of_boundsDiskW p q hp hq hc ψ K himg
    D.simple D.essential (hcl S D)
  have hmono : Set.encard (Set.range D.α.γ ∩ Set.range K.curve) ≤
      Set.encard (Set.range K.curve ∩ S) := by
    apply Set.encard_le_encard
    rintro x ⟨⟨t, rfl⟩, hxK⟩
    exact ⟨hxK, D.mem t⟩
  exact absurd (lt_of_le_of_lt (le_trans hle hmono) hcount) (lt_irrefl _)

/-- **The count and Pardon's Lemma 2 compose: any sliced sphere inside the footprint is clean.**
If `S` is a subset of the footprint `sphereSet c σ s ∪ cutDisc s c σ u`, sliced by the surface in
general position, then the crux's two counts (via `footprintCountBound`) show that `S` meets the knot
in fewer than `min p q` points, and Pardon's Lemma 2
(`Work.Drive.EpsForm.trace_inessential_of_slicing_of_countsW`) makes every closed curve of `F` in `S`
inessential.  Both half-spheres `H± = closedUpperCap ∪ closure (cutDisc)` are subsets of the
footprint, so this is the cleanliness of the two spheres at which Pardon's pinch ends, in the form its
consumers (`Work.Drive.PinchArc.halvesSpan_of_cleanHalfSpheres`) use. -/
theorem trace_inessential_of_slicing_of_subset_footprint
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    {d : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s : ℝ} (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    {S : Set R3}
    (hsub : S ⊆ Work.BoxShrink.Core.sphereSet c σ s ∪ Work.BoxShrink.Core.cutDisc s c σ u)
    (hslice : Work.InnermostDisk.SphereSlicing (Work.Smooth.Morse.torus ψ) S)
    (hcl : Work.Drive.CleansDiscsW (Work.Smooth.Morse.torus ψ))
    (hcountS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
    (hcountU : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d))) :
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop S := by
  refine trace_inessential_of_slicing_of_countsW p q hp hq hc ψ K himg hslice hcl ?_
  refine lt_of_le_of_lt (Set.encard_le_encard ?_) (footprintCountBound p q hp hq K hd hsmall
    c σ u hcountS hcountU)
  rintro x ⟨hxK, hxS⟩
  exact ⟨hxK, hsub hxS⟩

/-- **Pardon's dichotomy at any sphere of the pinching family, from the counts.**  This is the
per-`S_t` brick: `Work.BoxShrink.Bubble.SweepLoopsSmall` (hence `Work.BoxShrink.Pinch.PinchFamily`)
requires `Work.BoxShrink.Bubble.PardonDichotomy` at every parameter, i.e. that the winding span of
the region of the sphere is `⊥` or `⊤`.  By the cleanliness proved above
(`trace_inessential_of_slicing_of_subset_footprint`) the trace of any footprint-contained sliced
sphere carries no essential loop, and then `Work.SurgeryInvariance.WindingSpan_eq_bot_iff` gives
`⊥`.  So the dichotomy is *automatic*, from the crux's two counts, at every sphere of Pardon's
`2`-surgery whose region lives over the footprint and is sliced in general position — which is
exactly Pardon's "by construction" for his family. -/
theorem pardonDichotomy_of_slicing_of_subset_footprint
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    {d : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s : ℝ} (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    {S : Set R3}
    (hsub : S ⊆ Work.BoxShrink.Core.sphereSet c σ s ∪ Work.BoxShrink.Core.cutDisc s c σ u)
    (hslice : Work.InnermostDisk.SphereSlicing (Work.Smooth.Morse.torus ψ) S)
    (hcl : Work.Drive.CleansDiscsW (Work.Smooth.Morse.torus ψ))
    (hcountS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
    (hcountU : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d))) :
    Work.BoxShrink.Bubble.PardonDichotomy (Work.Smooth.Morse.torus ψ) S :=
  Or.inl ((Work.SurgeryInvariance.WindingSpan_eq_bot_iff (Work.Smooth.Morse.torus ψ) S).mpr
    (trace_inessential_of_slicing_of_subset_footprint p q hp hq hc ψ K himg hd hsmall c σ u
      hsub hslice hcl hcountS hcountU))

/-- **The regular case of the pinching family: a region and the same region peeled along an
inessential circle are `RegionEquivalent`.**  This is the loop-level form of the peeling
(`Work.BoxShrink.PinchOff.regionEquivalent_sdiff_range_closedCurve`, where it is already proved):
every loop of `X` can be re-routed, with its winding vector, off the image of a simple curve `γ`
which is inessential in `P` and lies *inside* `X` (that, not merely the inessentiality, is the
hypothesis that makes the re-routing possible — inessentiality alone does not license re-routing
across a piece whose boundary meets the boundary of the region; see the counterexample recorded in
the module docstring).  It is the case of `Work.SurgeryInvariance.SweepLoops.regular` /
`Work.BoxShrink.Bubble.SweepLoopsSmall.regular` in which no surgery has taken place, and the case to
which the two exceptional models (`SurgeryStepZero`, `SurgeryStepSmall`) must be compared. -/
theorem regionEquivalent_sdiff_range {P : Work.CoreTopology.ParamTorus} {X : Set R3}
    (γ : Work.CoreTopology.ClosedCurve P)
    (hsimple : Work.CoreTopology.IsSimple P γ)
    (hiness : ¬ Work.CoreTopology.IsEssential P γ)
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hsub : ∀ t : ℝ, γ.γ t ∈ X) :
    Work.SurgeryInvariance.RegionEquivalent P X (X \ Set.range γ.γ) :=
  Work.BoxShrink.PinchOff.regionEquivalent_sdiff_range_closedCurve hsimple hiness hX hsub


/-! ## Pardon's equation (1): the dichotomy of a box-region from a clean sphere

Pardon's Lemma 1 rests on equation (1): if a sphere `S` is transverse to `F` and meets it in
*inessential* curves only, then the region `F ∩ int(S)` has `WindingSpan` either `⊥` or `⊤` (`0` or
`2g` in Pardon's dimension count).  The workspace proves the abstract form
(`Work.BoxShrink.PinchOff.windingSpan_bot_or_top_of_inessential_boundary`: the two open pieces of the
complement of a finite family of pairwise disjoint simple inessential curves have span `⊥` or `⊤`),
and the two *endpoint* instances `upperRegion_rank_zero_or_two` /
`lowerRegion_rank_zero_or_two`; what was missing is the instance at an **intermediate sphere** of a
sweep, which is what a prover of Pardon's pinching family needs as the `dichotomy` field of
`Work.BoxShrink.Bubble.SweepLoopsSmall` / `Work.BoxShrink.Pinch.PinchFamily`.

The module supplies it for a **box-level sphere**: the general position of the box sphere at the
level `s` (`Work.InnermostDisk.SphereSlicing`) and the inessentiality of its trace make the winding
span of the box region `⊥` or `⊤`.  Two hypotheses beyond the slicing are used, and both are exactly
the content of "the trace of the sphere is a finite union of simple closed curves": the *pointwise*
cover `P.carrier ∩ sphereSet ⊆ ⋃ᵢ range (c i)` (the loop-level field `SphereSlicing.covers` does not
give it: a point of the trace which is not on any listed component is not excluded), and the
inessentiality of the listed curves (which the crux's counting supplies through
`Work.Drive.EpsForm.trace_inessential_of_slicing_of_countsW`, whence
`pardonDichotomy_boxRegion_of_countsW`).

This is the piece of the pinch that the *counting* reaches unchanged: it holds at every level whose
box sphere is sliced and whose knot-count is below `min p q`, i.e. at every intermediate sphere of a
box sweep whose count is controlled by Pardon's `|S ∩ β| + 2|D ∩ β|`. -/

/-- **Pardon's equation (1) at a box level, in general position.**  If the trace of the box sphere
`{boxNorm = s}` is sliced by the surface, covers it pointwise, and carries no essential loop, then
the winding span of the box region is `⊥` or `⊤`.

The `NiceLevel`-flavoured instance of the same fact is
`Work.BoxShrink.PinchOff.niceLevel_boxRegion_rank_zero_or_two` (it consumes the level-set
classification `NiceLevel.circleUnion`, i.e. Pardon's general position of the box sphere as a
*datum*); the point of this copy is that its hypothesis is the slicing datum the crux actually
carries (`Work.BoxShrink.SlicedSphere` = a `Work.InnermostDisk.SphereSlicing`), at the price of the
explicit pointwise cover `hcov` — the one thing the slicing's loop-level field `covers` does not
supply. -/
theorem pardonDichotomy_boxRegion_of_slicing {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    (hs : 0 < s) {c : R3} {σ : Equiv.Perm (Fin 3)}
    (S : Work.InnermostDisk.SphereSlicing P (Work.BoxShrink.Core.sphereSet c σ s))
    (hcov : P.carrier ∩ Work.BoxShrink.Core.sphereSet c σ s ⊆ ⋃ i, Set.range (S.c i).γ)
    (hclean : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s)) :
    Work.BoxShrink.Bubble.PardonDichotomy P (Work.BoxShrink.Core.boxRegion P s c σ) := by
  set X : Set R3 := Work.BoxShrink.Core.boxRegion P s c σ with hXdef
  set Y : Set R3 := P.carrier \ closure (Submission.PBox s c σ) with hYdef
  have hcl : closure (Submission.PBox s c σ) = {y : R3 | Submission.boxNorm c σ y ≤ s} :=
    Work.Step2.closure_PBox_eq hs c σ
  have hX : Work.SurgeryInvariance.IsOpenInCarrier P X := by
    rw [hXdef, Work.BoxShrink.Core.boxRegion]
    exact Work.SurgeryInvariance.isOpenInCarrier_carrier_inter (P := P)
      (Work.Topology.SphereSlicing.isOpen_PBox s c σ)
  have hY : Work.SurgeryInvariance.IsOpenInCarrier P Y := by
    rw [Work.SurgeryInvariance.IsOpenInCarrier, hYdef]
    have hpre : (Subtype.val ⁻¹' (P.carrier \ closure (Submission.PBox s c σ)) : Set P.carrier)
        = (Subtype.val ⁻¹' (closure (Submission.PBox s c σ)) : Set P.carrier)ᶜ := by
      ext y
      simp
    rw [hpre]
    exact (isClosed_closure.preimage continuous_subtype_val).isOpen_compl
  have hXY : Disjoint X Y := by
    rw [Set.disjoint_left]
    intro z hzX hzY
    rw [hXdef, Work.BoxShrink.Core.boxRegion] at hzX
    exact hzY.2 (subset_closure hzX.2)
  have hcover : P.carrier \ (⋃ i, Set.range (S.c i).γ) = X ∪ Y := by
    refine Set.Subset.antisymm ?_ ?_
    · intro z hz
      rw [Set.mem_sdiff] at hz
      obtain ⟨hzcar, hznot⟩ := hz
      by_cases hzc : z ∈ closure (Submission.PBox s c σ)
      · left
        rw [hXdef, Work.BoxShrink.Core.boxRegion]
        refine ⟨hzcar, ?_⟩
        have hzle : Submission.boxNorm c σ z ≤ s := by
          have hmem : z ∈ ({y : R3 | Submission.boxNorm c σ y ≤ s} : Set R3) := by
            rw [← hcl]; exact hzc
          exact hmem
        have hzne : Submission.boxNorm c σ z ≠ s := fun hEq =>
          hznot (hcov ⟨hzcar, by rw [Work.BoxShrink.Core.mem_sphereSet]; exact hEq⟩)
        exact (Submission.mem_PBox_iff s c σ z).mpr (lt_of_le_of_ne hzle hzne)
      · right
        exact ⟨hzcar, hzc⟩
    · rintro z (hz | hz)
      · rw [hXdef, Work.BoxShrink.Core.boxRegion] at hz
        rw [Set.mem_sdiff]
        refine ⟨hz.1, ?_⟩
        intro hzmem
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzmem
        obtain ⟨t, ht⟩ := hi
        have hzsphere : z ∈ Work.BoxShrink.Core.sphereSet c σ s := by
          rw [← ht]; exact S.mem i t
        rw [Work.BoxShrink.Core.mem_sphereSet] at hzsphere
        have hzlt := (Submission.mem_PBox_iff s c σ z).mp hz.2
        rw [hzsphere] at hzlt
        exact lt_irrefl s hzlt
      · rw [hYdef] at hz
        rw [Set.mem_sdiff]
        refine ⟨hz.1, ?_⟩
        intro hzmem
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzmem
        obtain ⟨t, ht⟩ := hi
        have hzsphere : z ∈ Work.BoxShrink.Core.sphereSet c σ s := by
          rw [← ht]; exact S.mem i t
        rw [Work.BoxShrink.Core.mem_sphereSet] at hzsphere
        exact hz.2 (by rw [hcl]; exact le_of_eq hzsphere)
  have hsimple : ∀ i : S.ι, Work.CoreTopology.IsSimple P (S.c i) := S.simple
  have hess : ∀ i : S.ι, ¬ Work.CoreTopology.IsEssential P (S.c i) := fun i hi =>
    hclean ⟨S.c i, hi, S.mem i⟩
  set e : S.ι ≃ Fin (Fintype.card S.ι) := Fintype.equivFin S.ι with he
  set γ : Fin (Fintype.card S.ι) → Work.CoreTopology.ClosedCurve P :=
    fun j => S.c (e.symm j) with hγ
  have hγrange : (⋃ j : Fin (Fintype.card S.ι), Set.range (γ j).γ) =
      ⋃ i : S.ι, Set.range (S.c i).γ := by
    refine Set.Subset.antisymm ?_ ?_
    · refine Set.iUnion_subset fun j => ?_
      rw [hγ]
      exact Set.subset_iUnion (fun i : S.ι => Set.range (S.c i).γ) (e.symm j)
    · refine Set.iUnion_subset fun i => ?_
      rw [hγ]
      have h : Set.range (S.c (e.symm (e i))).γ ⊆
          ⋃ j : Fin (Fintype.card S.ι), Set.range (S.c (e.symm j)).γ :=
        Set.subset_iUnion (fun j : Fin (Fintype.card S.ι) =>
          Set.range (S.c (e.symm j)).γ) (e i)
      rwa [Equiv.symm_apply_apply] at h
  have hcover' : P.carrier \ (⋃ j : Fin (Fintype.card S.ι), Set.range (γ j).γ) = X ∪ Y := by
    rw [hγrange]; exact hcover
  exact Work.BoxShrink.PinchOff.windingSpan_bot_or_top_of_inessential_boundary
    (γ := γ) (fun j => hsimple (e.symm j)) (fun j => hess (e.symm j))
    (fun j k hjk => S.disjoint (e.symm.injective.ne hjk)) hX hY hXY hcover'

/-- **Pardon's equation (1) at a *counted* box level.**  The same dichotomy with the
inessentiality of the trace supplied by the crux's counting: at a level `s` whose box sphere is
sliced in general position and meets the knot `K` in fewer than `min p q` points, the winding span of
the box region is `⊥` or `⊤`.  This is the form in which a sweep of box-level regions can produce the
`dichotomy` field at every one of its intermediate spheres whose count is controlled by Pardon's
`|S ∩ β| + 2|D ∩ β|`. -/
theorem pardonDichotomy_boxRegion_of_countsW
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (S : Work.InnermostDisk.SphereSlicing (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.sphereSet c σ s))
    (hcov : (Work.Smooth.Morse.torus ψ).carrier ∩
      Work.BoxShrink.Core.sphereSet c σ s ⊆ ⋃ i, Set.range (S.c i).γ)
    (hcl : Work.Drive.CleansDiscsW (Work.Smooth.Morse.torus ψ))
    (hcount : Set.encard (Set.range K.curve ∩ Work.BoxShrink.Core.sphereSet c σ s) <
      (Nat.min p q : ℕ∞)) :
    Work.BoxShrink.Bubble.PardonDichotomy (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) :=
  pardonDichotomy_boxRegion_of_slicing hs S hcov
    (trace_inessential_of_slicing_of_countsW p q hp hq hc ψ K himg S hcl hcount)



/-! ## Pardon's equation (1), discharged

`Work.BoxShrink.Pinch.Equation1Input` is one of the two named inputs of the pinch chapter
(`Work.BoxShrink.Pinch.PinchSweep`'s `pinchLevels_of_box`: "the dichotomy of the family ... comes
from Pardon's equation (1) at each level").  It is **not** a genuine input: Pardon's equation (1)
follows from the general position of the level, which `Work.Smooth.Morse.NiceLevel` *contains* — its
field `circleUnion` is exactly the pointwise description of the level set as a finite disjoint union
of simple closed curves of the surface.  We record the proof here, in the weak vocabulary of this
module, because it is the dichotomy brick every prover of Pardon's pinch needs at the intermediate
spheres (see also `pardonDichotomy_boxRegion_of_slicing`, the box-sphere instance in the vocabulary of
`Work.InnermostDisk.SphereSlicing`).

The proof is pure point set: the region `F ∩ {g < t}` and the exterior of the closed region
`F ∩ {g ≤ t}` are two disjoint open pieces of the surface whose union is the complement of the level
set, and the level set is the union of the curves; the inessentiality of the curves is the
non-existence of an essential loop in the level set, and the abstract dichotomy
`Work.BoxShrink.PinchOff.windingSpan_bot_or_top_of_inessential_boundary` finishes. -/

/-- **Pardon's equation (1) at a nice level.**  If `g` is continuous, `t` is a nice level of `g|_F`
and the level set carries no essential loop of `F`, then the winding span of the sublevel region
`F ∩ {g < t}` is `⊥` or `⊤`: `dim im(H₁(F ∩ int S; ℚ) → H₁(F; ℚ))` is `0` or `2g`.

The same statement is already proved in the sibling chapter, with the same proof, as
`Work.BoxShrink.PinchOff.equation1Input_holds`; this copy is kept because it is the dichotomy brick
of *this* module's vocabulary (it is the second ingredient of every pinch proof that goes through
`Work.SurgeryInvariance.SweepLoops` with a `dichotomy` field). -/
theorem equation1Input_holds : Work.BoxShrink.Pinch.Equation1Input := by
  intro ψ g t hg hnice hclean
  obtain ⟨n, γ, hsimple, hdisj, hZeq⟩ := hnice.circleUnion
  set X : Set R3 := Work.Smooth.Morse.region ψ g t with hXdef
  set Y : Set R3 := (Work.Smooth.Morse.torus ψ).carrier \
    Work.Smooth.Morse.closedRegion ψ g t with hYdef
  have hXopen : Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ) X := by
    rw [hXdef, Work.Smooth.Morse.region]
    exact Work.SurgeryInvariance.isOpenInCarrier_carrier_inter (P := Work.Smooth.Morse.torus ψ)
      (isOpen_lt hg continuous_const)
  have hYopen : Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ) Y := by
    rw [Work.SurgeryInvariance.IsOpenInCarrier, hYdef]
    have hpre : (Subtype.val ⁻¹' ((Work.Smooth.Morse.torus ψ).carrier \
          Work.Smooth.Morse.closedRegion ψ g t) : Set (Work.Smooth.Morse.torus ψ).carrier)
        = Subtype.val ⁻¹' ({x : R3 | t < g x} : Set R3) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_setOf_eq,
        Work.Smooth.Morse.mem_closedRegion]
      constructor
      · rintro ⟨-, hnot⟩
        exact not_le.mp fun hle => hnot ⟨y.2, hle⟩
      · intro hgt
        exact ⟨y.2, fun h => absurd h.2 (not_le.mpr hgt)⟩
    rw [hpre]
    exact (isOpen_lt continuous_const hg).preimage continuous_subtype_val
  have hXY : Disjoint X Y := by
    rw [Set.disjoint_left]
    intro z hzX hzY
    rw [hXdef, Work.Smooth.Morse.mem_region] at hzX
    rw [hYdef, Set.mem_sdiff, Work.Smooth.Morse.mem_closedRegion] at hzY
    exact hzY.2 ⟨hzX.1, le_of_lt hzX.2⟩
  have hcover : (Work.Smooth.Morse.torus ψ).carrier \ (⋃ i, Set.range (γ i).γ) = X ∪ Y := by
    rw [← hZeq]
    refine Set.Subset.antisymm ?_ ?_
    · intro z hz
      rw [Set.mem_sdiff, Work.Smooth.Morse.mem_levelSet] at hz
      obtain ⟨hzcar, hzne⟩ := hz
      by_cases hlt : g z < t
      · left
        rw [hXdef, Work.Smooth.Morse.mem_region]; exact ⟨hzcar, hlt⟩
      · right
        rw [hYdef, Set.mem_sdiff, Work.Smooth.Morse.mem_closedRegion]
        refine ⟨hzcar, ?_⟩
        intro hle
        exact hzne ⟨hzcar, le_antisymm hle.2 (not_lt.mp hlt)⟩
    · rintro z (hz | hz)
      · rw [hXdef, Work.Smooth.Morse.mem_region] at hz
        rw [Set.mem_sdiff, Work.Smooth.Morse.mem_levelSet]
        exact ⟨hz.1, fun h => absurd h.2 (ne_of_lt hz.2)⟩
      · rw [hYdef, Set.mem_sdiff, Work.Smooth.Morse.mem_closedRegion] at hz
        rw [Set.mem_sdiff, Work.Smooth.Morse.mem_levelSet]
        exact ⟨hz.1, fun h => hz.2 ⟨h.1, le_of_eq h.2⟩⟩
  have hess : ∀ i : Fin n, ¬ Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) (γ i) := by
    intro i hi
    exact hclean ⟨γ i, hi, by
      intro s
      rw [hZeq]
      exact Set.mem_iUnion.mpr ⟨i, s, rfl⟩⟩
  exact Work.BoxShrink.PinchOff.windingSpan_bot_or_top_of_inessential_boundary
    hsimple hess hdisj hXopen hYopen hXY hcover


/-! ## The ε-form from the fleet's live residual: the sideways sweep

`Work.Drive.EpsSphere.SideSweepExists` is the project lead's reformulation of Pardon's pinching
family (the sideways sweep of a thin slab around the cutting plane), and it is the residual the
*solid* form of the ε-conclusion has already been assembled from
(`Submission/Work/Drive/EpsForm/countingHalfEpsBody_of_sideSweepExists.lean`).  This module records
that the *trace* form — this module's target `Work.Drive.CountingHalfEps`, the form the drive chain
`Submission/Work/Drive/pardon_of_cleansW_region.lean` consumes — follows from the *same* residual,
and that it does so *without* spending any `ε`-slack:

* the winding span is constant along the sweep (the sibling's
  `Work.Drive.EpsForm.span_const_of_sweep_axioms_of_finrank_jumps`: Pardon's dichotomy at the regular
  levels pins the rank to `0` or `2`, the rank changes by at most one across each critical value, so
  it cannot change at all);
* hence the end region `boxRegion ∖ slabZ` (where the whole slab has been removed) has the same span
  as the box region, which is non-`⊥` because the box region contains an essential loop
  (`HasEssBox`);
* so the end region contains an *essential loop* `γ`; every point of the end region has
  `D.h ≤ |y (σ 2) - (c (σ 2) + u)|` with `D.h > 0`, so `γ` lies in `upperRegion ∪ lowerRegion` —
  a *disjoint union of two open pieces of the carrier*, hence (connectedness of `ℝ`) `γ` lies in one
  of the two half-regions;
* a loop *inside* a half-region is within every `ε > 0` of it (`Metric.self_subset_thickening`), so
  the trace-form conclusion holds.

Consequently the trace form is *not* stronger than the fleet's residual in any way that the `ε`-slack
could not absorb: at every configuration satisfying the residual and the crux's counting data, both
forms hold, and the suspicion recorded in the sibling's note (that the trace form might be false at
`countConst = 150` while the solid form is true) is settled in the negative as far as the residual is
concerned — either the residual fails at that configuration, or the trace form holds there. -/

/-- **The trace-form ε-conclusion from the sideways sweep.**  `Work.Drive.EpsSphere.SideSweepExists`
(this workspace's live residual for Pardon's Lemma 3) gives this module's target
`Work.Drive.CountingHalfEps` — the loop within `ε` of a half-*region*, with no use of the `ε`-slack:
the loop produced by the sweep lies strictly on one side of the cutting plane. -/
theorem countingHalfEps_of_sideSweepExists (h : Work.Drive.EpsSphere.SideSweepExists) :
    Work.Drive.CountingHalfEps := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    ε hε
  set P : Work.CoreTopology.ParamTorus := Work.Smooth.Morse.torus ψ with hP
  obtain ⟨D⟩ := h p q hp hq hc ψ K d hd hbound himg hsmall (Work.Drive.cleansDiscsWd_of_W hcl) r hr c σ hbox s hrs hs hslice u hu hS hU
  -- the family of regions is nested, so the winding span is monotone along it
  have hmono : ∀ μ ν : ℝ, μ ≤ ν → Work.Drive.EpsSphere.sideRegion P s c σ u D.h D.ℓ ν ⊆
      Work.Drive.EpsSphere.sideRegion P s c σ u D.h D.ℓ μ := by
    intro μ ν hμν y hy
    rw [Work.Drive.EpsSphere.sideRegion, Work.Drive.EpsSphere.wallRegion] at hy ⊢
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_setOf_eq] at hy ⊢
    exact ⟨hy.1, hy.2.1, fun hlt => hy.2.2 ⟨hlt.1, lt_of_lt_of_le hlt.2 hμν⟩⟩
  -- the combinatorial sweep-constancy
  have hconst := Work.Drive.EpsForm.span_const_of_sweep_axioms_of_finrank_jumps P
    (fun lam => Work.Drive.EpsSphere.sideRegion P s c σ u D.h D.ℓ lam)
    D.lam0 D.lam1 D.exc D.hlt D.exc_mem hmono D.regular_span D.jump D.dichotomy
  -- the box region carries an essential loop, so the end region does too
  have hboxC : P.ContainsEssentialLoop (Work.BoxShrink.Core.boxRegion P s c σ) :=
    Work.BoxShrink.Core.containsEssentialLoop_boxRegion_of_hasEssBox (P := P) (c := c) (σ := σ)
      (le_of_lt hrs) hbox
  have hne : Work.SurgeryInvariance.WindingSpan P
      (Work.Drive.EpsSphere.sideRegion P s c σ u D.h D.ℓ D.lam1) ≠ ⊥ := by
    rw [← hconst, D.start]
    exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr hboxC
  obtain ⟨γ, hγess, hγmem⟩ := (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hne
  -- every point of the end region is strictly off the cutting plane, and inside the box
  have hsplit : ∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u := by
    intro t
    have hmem := hγmem t
    rw [D.finish, Work.BoxShrink.Core.boxRegion, Work.Drive.EpsSphere.slabZ] at hmem
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_setOf_eq] at hmem
    have hw : D.h ≤ |γ t (σ 2) - (c (σ 2) + u)| := le_of_not_gt hmem.2
    have hne0 : γ t (σ 2) - (c (σ 2) + u) ≠ 0 := by
      intro hzero
      rw [hzero, abs_zero] at hw
      exact absurd hw (not_le.mpr D.hpos)
    rcases lt_or_gt_of_ne hne0 with hlt | hgt
    · right
      rw [Work.BoxShrink.Core.mem_lowerRegion]
      exact ⟨hmem.1.1, hmem.1.2, by linarith⟩
    · left
      rw [Work.BoxShrink.Core.mem_upperRegion]
      exact ⟨hmem.1.1, hmem.1.2, by linarith⟩
  -- the two half-regions are disjoint open pieces, so the loop lies in one of them
  rcases Work.SurgeryInvariance.Span.curve_subset_of_union
      (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
      (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)
      (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion P s c σ u) γ hsplit with hup | hlo
  · exact Or.inr ⟨γ, hγess, fun t => Metric.self_subset_thickening hε _ (hup t)⟩
  · exact Or.inl ⟨γ, hγess, fun t => Metric.self_subset_thickening hε _ (hlo t)⟩


/-! ## STATUS (this session): the *solid* form is the honest reading of the residual

`Submission/Work/EpsW/NOTES_arcsCaseEps.md` (another agent, machine-checked configuration
`Work.BoxShrink.PinchOff.RefuteDrop/`) records that the **trace** form (`ThickHalf`, and therefore
this file's target `CountingHalfEps`) is *strictly stronger* than Pardon's `doublebubble2`, which
concludes that `F ∩ (B(ε) + int(H_i))` has a genus-`g` component — a loop within `ε` of the **solid**
half-box.  At the `RefuteDrop` geometry (where `ψ = dropDiffeo`, the plane is `{x = 0}`, the slice is
four arcs, the box-sphere trace and *both* half-sphere traces are inessential and the box region
carries an essential loop) the trace conclusion fails numerically, so *no* form of the residual that
spends the counting at the three endpoint spheres alone can be a proof of the trace form.  Whether
the trace form is false, or vacuously true because the counting hypotheses `150 d < min p q` cannot
be met at all, is *open* (it is equivalent to a statement about the best constant in the
Blair–Campisi–Taylor–Tomova distortion bound); the *solid* form, on the other hand, is exactly
Pardon's theorem and is what the drive chain can consume
(`Work.Drive.pardon_of_cleansW_region_of_epsBody`).

Consequently the residuals recorded in `EpsForm/countingHalfEps_of_arcOrPlaneHalf.lean` are arranged
in decreasing strength, and the recommended ones are the solid ones:

| residual | conclusion | status |
|---|---|---|
| `ArcEpsOff` | the trace form, off the plane's general position | *equivalent* to this file's target (the general-position branch is proved), so no gain; recorded for completeness |
| `ArcShiftedHalf` | an essential loop in a `δ`-shifted half-*region*, off general position | Pardon's conclusion in the trace spelling; gives `CountingHalfEpsBody` |
| `ArcBodyOff` | the solid `ε`-conclusion, off the plane's general position | **the recommended residual**: exactly Pardon off general position; gives `CountingHalfEpsBody` |
| `ArcBodyOffArcs` | the same, in the arcs case of `Work.SliceArcs` | weaker (one more hypothesis), the case the fleet attacks |

## Two more routes to the target: the fleet's live residual, and the honest shifted residual

`Submission/Work/Drive/EpsForm/countingHalfEps_of_arcOrPlaneHalf.lean` (this agent) proves two
further reductions, which supersede the sideways-sweep route of this file in the sense that their
residuals are the ones the rest of the workspace is actually attacking:

* `Work.Drive.EpsForm.halves_ne_bot_of_slicedPlane` (**proved**, unconditionally): at a
  configuration whose cutting plane is in general position (`TransverseSlice` and the slicing of the
  flat disc), the two half-regions carry an essential loop — Pardon's push-off at a *clean* plane,
  from the slicing datum, the crux's plane count and the weak cut-and-paste
  (`Work.Drive.EpsForm.not_containsEssentialLoop_sliceRegion_of_sliced`), through the proved
  `Work.BoxShrink.PinchOff.regionEquivalent_halves_of_tameSlice`;
* `Work.Drive.EpsForm.ArcOrPlaneHalf` — the *fleet's* live residual in the weak-disc vocabulary
  (`Work.SliceArcs.PointwiseRoute` / `Work.ArcCollar.PointwiseHalf` spoken with `CleansDiscsW`):
  at every crux configuration, either the arc structure of the slice together with an essential loop
  in the two half-regions, or the general position of the plane (in which case the conclusion is
  *proved* above).  `Work.Drive.EpsForm.countingHalfEps_of_arcOrPlaneHalf` gives this module's
  target from it, through `Work.Drive.CountingHalfW`; note that its arcs branch asks for the *exact*
  halving statement, which the audit of `Drive/countingHalfW_morse` reports to be strictly stronger
  than Pardon's `doublebubble2` — so the residual below is the *honest* one;
* `Work.Drive.EpsForm.ArcShiftedHalf` — the honest residual in the weak-disc vocabulary: only at the
  configurations at which the plane is **not** in general position is anything assumed, and then only
  the *shifted* conclusion (an essential loop in a `δ`-shifted half-region, for every admissible
  `δ`) — exactly the shape Pardon's perturbation of the pinching family produces, since his loop lies
  in the interior of a *perturbed* half and the perturbation may be taken smaller than `δ`.
  `Work.Drive.EpsForm.countingHalfEpsBody_of_arcShiftedHalf` gives the solid form
  (`Work.Drive.CountingHalfEpsBody`) from it, which is the form the drive chain can consume
  (`Work.Drive.pardon_of_cleansW_region_of_epsBody`).
-/

/-! ## The route to the target is closed: the legacy hypothesis is refuted

The target below carries the **legacy** cut-and-paste hypothesis `Work.Drive.CleansDiscsW`
(`Drive/Interfaces.lean`), the *unclaused* form: *every* `Work.InnermostDisk.InnermostDisc` datum
`(S, D)` of the surface, of any shape whatsoever, has a weak bounding disc for its boundary curve
`D.α`.  This hypothesis is **FALSE**:

* `Work.Drive.EpsForm.exists_innermostDisc_essential_winding` (proved, axiom-clean) exhibits an
  innermost-disc datum of the standard torus whose boundary curve has a lift of winding `(1,1)` —
  hence both winding components non-zero;
* `Work.Drive.compressing_winding_dichotomyW` (proved) says that a weak bounding disc of an
  essential curve forces one winding component of *every* lift to vanish;
* so that datum has no weak bounding disc, and `CleansDiscsW` fails at the standard torus, and —
  by `Work.Drive.EpsForm.not_cleansDiscsW_mapHomeomorph` — at every torus `torus ψ`.

Consequently **every statement whose hypotheses contain the legacy `CleansDiscsW` is vacuously
true**, and this includes this module's target, `Work.Drive.CountingHalfEps`, and (through the
ledger `Work.BoxShrink.ClassicalInputs`) the whole legacy architecture of the workspace.  The
report `Submission/Work/Drive/SESSION_NOTES_CleanDiscsWAll.md` and the sibling `EpsForm`
modules (`arcBodyOff_holds.lean`, `exists_innermostDisc_essential_winding.lean`,
`InterfacesD.lean`, `ArcBodyOffD.lean`) record the correction: the live input is the *claused*
`Work.Drive.CleansDiscsWd`, and the live form of Pardon's Lemma 3 is `Work.Drive.CountingHalfEpsD`.

**What this module contributes on top of the vacuity.**  Everything proved in this file *above*
this section — the reduction of the target to the residuals, the two inessentiality statements
`sphereTrace_inessential_of_countsW` / `trace_inessential_of_slicing_of_countsW` of Pardon's
Lemma 2 in the weak-disc vocabulary, the count bounds `footprintCountBound` / `halfSphereCountBound`,
the trace-form assembly from the sideways sweep (`countingHalfEps_of_sideSweepExists`), the
sideways-sweep routes — is *unconditionally* valid: none of it uses the legacy hypothesis except
where the hypothesis is an explicit argument.  The single genuinely new *theorem* of the session is
the plane branch of the pinch in `EpsForm/countingHalfEps_of_arcOrPlaneHalf.lean`
(`Work.Drive.EpsForm.halves_ne_bot_of_slicedPlane`): at a configuration whose cutting plane is in
general position, the two half-regions carry an essential loop of the surface — the tameness of the
slice, its inessentiality from the crux's plane count and Pardon's push-off, with the weak
cut-and-paste input.  That statement has a twin in the corrected vocabulary
(`Submission/Work/Drive/EpsForm/ArcBodyOffD.lean` and the sibling modules of that series), and it is
the piece of the pinching argument that survives the correction. -/

/-- **The legacy hypothesis fails at the standard torus.**  An innermost-disc datum whose boundary
curve has both winding components non-zero has no weak bounding disc, by the winding dichotomy
`Work.Drive.compressing_winding_dichotomyW`. -/
theorem not_cleansDiscsW_standard : ¬ Work.Drive.CleansDiscsW Work.CoreTopology.standard := by
  rintro hcl
  obtain ⟨S, D, ⟨L₁, h₁⟩, ⟨L₂, h₂⟩⟩ :=
    Work.Drive.EpsForm.exists_innermostDisc_essential_winding
  rcases Work.Drive.compressing_winding_dichotomyW D.α D.essential (hcl S D) with hd | hd
  · exact h₂ (hd L₂)
  · exact h₁ (hd L₁)

/-- **The ε-form: Pardon's `doublebubble2` conclusion at the crux configurations.**

The reduction to the exact counted form, the solid form and the sphere-level ε-form is in
`EpsForm/Defs.lean` and `EpsFormSphere/Defs.lean`; the residual content is Pardon's pinching family
(see the module docstring).  The proof below is the *vacuity* proof forced by the refutation of the
legacy cut-and-paste hypothesis — see the section above: at every crux configuration the hypothesis
`CleansDiscsW (torus ψ)` is false, since the refutation at the standard torus transports along the
ambient homeomorphism `ψ.toHomeomorph`.  The statement is therefore *true*, and it is *proved*, but
its content is empty; the live form of the lemma is `Work.Drive.CountingHalfEpsD`
(`Drive/InterfacesD.lean`). -/
theorem countingHalfEps_holds : Work.Drive.CountingHalfEps := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    ε hε
  exact absurd hcl (Work.Drive.EpsForm.not_cleansDiscsW_mapHomeomorph not_cleansDiscsW_standard
    ψ.toHomeomorph)

end Work.Drive.EpsForm
