import Submission.Work.PinchCounted.All
import Submission.Work.PinchFamily.All
import Submission.Work.BoxShrink.PinchOff.regionEquivalent_halves_of_tameSlice

/-!
# `Work.CountedPinch` — the counted residual of Pardon's Lemma 3, sharpened to one general-position datum

Entry point: `import Submission.Work.CountedPinch.All`.
Namespace `Work.CountedPinch`, directory `Submission/Work/CountedPinch/`.

## What this chapter is

The challenge `Submission.pardon_torus_knot_distortion` reduces, through the ledger
`Work.BoxShrink.ClassicalInputs`, to the single counted input
`Work.BoxShrink.Pinch.CountingHalf` — Pardon's Lemma 3 (`doublebubble`) at the configurations
the crux produces.  The preceding chapters reduced that input, step by step, to the residuals

* `Work.PinchCounted.CountedPinch` — "at every counted configuration there is a family of regions
  from the region inside the box to the two half-regions whose local move at every parameter is a
  `CountedStep`" (the *local* residual), and
* `Work.PinchFamily.PinchTransport` — "at every counted configuration every loop of the region
  inside the box is matched, with its winding vector, by a loop of the two half-regions" (the
  *push-off*), which is *equivalent* to the local residual in the non-degenerate case
  (`Work.PinchFamily.countedPinch_iff_pinchTransport_of_halvesEssential`),

and showed that everything else is proved: the counting bridge (Pardon's Lemma 2 at the
intermediate spheres), the endgame (`PardonLemma3 ⟹ CountingHalf ⟹ CruxCore ⟹ the challenge`),
the non-vacuity instances, and the refutations of the *uncounted* forms.

## The reduction of this chapter

This chapter isolates, inside the counted vocabulary, the **single general-position datum of the
cutting plane** and proves:

> `Work.CountedPinch.pinchTransport_of_countedSliceGood` :
> **if at every counted configuration the cutting plane meets the surface transversely along the
> slice, the slice is tame, and the slice carries no essential loop, then the push-off
> `Work.PinchFamily.PinchTransport` holds** — hence `Work.PinchCounted.CountedPinch`, hence
> `Work.BoxShrink.Pinch.CountingHalf`, hence the crux, the shrinking step and the challenge.

and, more importantly, it *derives* the two inessentiality hypotheses of that statement from the
counted data itself:

* `Work.CountedPinch.sliceTrace_inessential_of_slicedPlane` — at a counted configuration, if the
  flat disc of the plane is *sliced* by the surface (`Work.Smooth.Plane.SlicedPlane`, the planar
  analogue of the shell's `SlicedSphere`), then the slice carries **no essential loop**.  This is
  Pardon's Lemma 2 at the cutting disc: the slicing datum supplies the innermost disc
  (`Work.Smooth.Plane.innermostDiscInput_of_slicedPlane`), the cut-and-paste
  `CleansDiscs` is a hypothesis of the counted configuration, and the counting hypothesis
  (the number of parameters at which the knot meets the plane inside the box is
  `≤ 5(1+ε)/ε·d < I(F,β)`) contradicts a compressing loop inside the disc.  **This is where the
  counting is used**, and it is used exactly as Pardon uses it: to make the trace of the cutting
  surface inessential.
* `Work.CountedPinch.tameSlice_of_slicedPlane` — the same datum gives the tameness `TameSlice`
  (= `Work.Smooth.Plane.TransversePlane`) of the slice, with no further input.

So the residual of the counted chapter is

  `Work.CountedPinch.CountedSlicePlane` : **at every counted configuration, the cutting plane meets
  the surface transversely along the slice and the flat disc cut out of the box by the plane is
  sliced by the surface**,

a general-position statement about the *plane* of exactly the same shape as the `SlicedSphere`
hypothesis the counted configuration already carries for the *box sphere* (which the workspace
proves almost everywhere, `Work.Smooth.OneManifold.aeSlicedAll_of_planeHypothesis`).  In
particular **no** inessentiality, cleaning, coherence or counting input beyond what the counted
configuration already carries is needed: the two endpoint inessentiality facts of Pardon's Lemma 2
are *consequences* of the recorded hypotheses of this chapter
(`pinchTransport_of_countedSlicePlane`).

A second, counting-free route to the same conclusion is also recorded: if the slice is a finite
disjoint union of embedded arcs of the surface then its inessentiality is *free*
(`Work.CountedPinch.not_containsEssentialLoop_of_arcs`, from the workspace's
`Work.Smooth.Plane.Slicing.not_isEssential_of_range_subset_arc` and the connectedness of the image
of a closed curve), so `CountedSliceArcs` plus transversality gives the push-off with no counting
argument at all (`countedSliceGood_of_countedSliceArcs`).

## What is *not* claimed

The datum `CountedSlicePlane` is **not** proved here, and it cannot be assumed unconditionally on
all configurations: the workspace proves that the global transversality is *false*
(`Work.BoxShrink.PinchOff.not_forall_transverseSlice`, the tangent configuration of the standard
torus), and that even the almost-everywhere form of the planar general position fails for Pardon's
open box (`Work.PlaneSlice.not_ae_transversePlane_pardonSlice`).  The chapter records both, so that
the reader sees exactly where the remaining mathematics is: **Pardon's counting must supply the
general position of the cutting plane, and nothing else is missing.**
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.CountedPinch

noncomputable section

/-! ## The vocabulary of the configuration

The names below are the parent chapters' objects (definitionally), re-exported so that a caller
never has to reach past this chapter's interface. -/

/-- The surface of a parametrised torus, inside Pardon's box `PBox s c σ`. -/
abbrev box (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Set R3 :=
  Work.BoxShrink.Core.boxRegion P s c σ

/-- The two half-regions of the box, cut out by the plane `{y (σ 2) = c (σ 2) + u}`. -/
abbrev halves (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Set R3 :=
  Work.PinchCounted.PinchSweep.halves P s c σ u

/-- The **slice**: the trace of the cutting plane inside the box, `F ∩ PBox s c σ ∩ {y (σ 2) =
c (σ 2) + u}`.  Equivalently `F ∩ cutDisc s c σ u`. -/
abbrev slice (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Set R3 :=
  Work.BoxShrink.Core.sliceRegion P s c σ u

/-- The trace of the box sphere `∂PBox s c σ` on the surface. -/
abbrev sphereTrace (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) : Set R3 :=
  Work.BoxShrink.Core.sphereSet c σ s

/-- The flat disc cut out of the box by the cutting plane. -/
abbrev flatDisc (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  Work.BoxShrink.Core.cutDisc s c σ u

/-! ## The counted configurations, in two shells

`Work.PinchFamily.Residual Q` is the shell of the preceding chapters: the body `Q` sees the
parametrised torus `P`, the knot of the configuration as a closed curve `β` of `P`, and the box
data `s c σ u` — but not the diffeomorphism `ψ` of the configuration.  That is enough for all the
residuals about the *loop content* of regions.

The general-position data of the *cutting plane* (`Work.BoxShrink.Pinch.TransverseSlice`) is
stated with respect to the *ambient* coordinates in which the plane lives, i.e. in terms of `ψ`;
`CountedD` is the same shell with `ψ` visible in the body.  The two shells have the same binders,
so a residual in either is directly comparable with `CountedPinch` and `PinchTransport`. -/

/-- **The counted shell of the preceding chapters** (`Work.PinchFamily.Residual`, spelled here so
that the caller of this chapter sees one name): at every configuration carrying the counting data
of the crux — the knot data, the distortion bound `d` with `countConst · d < min p q = I(F,β)`, the
clean cut-and-paste `CleansDiscs`, the swept box with an essential loop, the sphere in general
position `SlicedSphere`, and the two intersection counts — the predicate `Q` holds. -/
abbrev Counted (Q : (P : Work.CoreTopology.ParamTorus) → Work.CoreTopology.ClosedCurve P →
    ℝ → R3 → Equiv.Perm (Fin 3) → ℝ → Prop) : Prop :=
  Work.PinchFamily.Residual Q

/-- **The counted shell with the diffeomorphism visible**: the same binders as
`Work.PinchFamily.Residual` (verbatim, so that the two shells are interchangeable through
`counted_of_countedD` / `countedD_of_counted`), with the body additionally receiving the
diffeomorphism `ψ` of the configuration (whose surface is `Work.Smooth.Morse.torus ψ`, the first
argument of the `Counted` shell) and the knot `K` and its distortion bound `d`. -/
def CountedD (Q : (ψ : Submission.Diffeo) →
    Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ) → Knot → ℝ → ℝ → R3 →
    Equiv.Perm (Fin 3) → ℝ → Prop) : Prop :=
  ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.InnermostDisk.CleansDiscs (Work.Smooth.Morse.torus ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (Work.Smooth.Morse.torus ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (Work.Smooth.Morse.torus ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          Q ψ (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
              (Work.CoreTopology.standardCurve p q)) K d s c σ u

/-- **A residual in the `ψ`-visible shell gives one in the `P`-shell**: it is enough that the
`P`-body holds at the surface of the configuration (`Work.Smooth.Morse.torus ψ`). -/
theorem Counted_of_countedD {Q : (ψ : Submission.Diffeo) →
    Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ) → Knot → ℝ → ℝ → R3 →
    Equiv.Perm (Fin 3) → ℝ → Prop}
    {Q' : (P : Work.CoreTopology.ParamTorus) → Work.CoreTopology.ClosedCurve P →
      ℝ → R3 → Equiv.Perm (Fin 3) → ℝ → Prop}
    (h : CountedD Q)
    (hQ : ∀ (ψ : Submission.Diffeo)
      (β : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ)) (K : Knot) (d : ℝ)
      (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Q ψ β K d s c σ u → Q' (Work.Smooth.Morse.torus ψ) β s c σ u) :
    Counted Q' :=
  fun p q hp hq hc ψ K d hd hb hi hs hcl r hr c σ hbox s hrs hs2 hslice u hu hS hU =>
    hQ ψ _ K d s c σ u
      (h p q hp hq hc ψ K d hd hb hi hs hcl r hr c σ hbox s hrs hs2 hslice u hu hS hU)

/-- **A residual in the `P`-shell gives one in the `ψ`-visible shell**, when the body does not
depend on `ψ` (as is the case for all the loop-content residuals). -/
theorem countedD_of_Counted {Q : (P : Work.CoreTopology.ParamTorus) → Work.CoreTopology.ClosedCurve P →
    ℝ → R3 → Equiv.Perm (Fin 3) → ℝ → Prop}
    (h : Counted Q) :
    CountedD fun ψ β _ _ s c σ u => Q (Work.Smooth.Morse.torus ψ) β s c σ u :=
  fun p q hp hq hc ψ K d hd hb hi hs hcl r hr c σ hbox s hrs hs2 hslice u hu hS hU =>
    h p q hp hq hc ψ K d hd hb hi hs hcl r hr c σ hbox s hrs hs2 hslice u hu hS hU

/-! ## The counted residual of the preceding chapter, and the push-off

These are the **targets** of the subproject: the theorem below
(`pinchTransport_of_countedSlicePlane`) proves the second, and through it the first, the ledger
input `Work.BoxShrink.Pinch.CountingHalf`, the crux `Work.BoxShrink.CruxCore` and the challenge,
from the single general-position datum of the cutting plane isolated in this chapter. -/

/-- **The local residual of Pardon's counted Lemma 3** (`Work.PinchCounted.CountedPinch`): at
every counted configuration there is a family of regions from the region inside the box to the two
half-regions together with an open piece of vanishing winding span, whose local move at every
parameter is a `CountedStep`. -/
abbrev CountedPinch : Prop := Work.PinchCounted.CountedPinch

/-- **Pardon's push-off at every counted configuration**
(`Work.PinchFamily.PinchTransport`): every closed curve of the surface inside the box region is
matched, with its winding vector, by a closed curve of the two half-regions. -/
abbrev PinchTransport : Prop := Work.PinchFamily.PinchTransport

theorem countedPinch_eq_counted_localFamilyBody :
    CountedPinch = Counted Work.PinchFamily.LocalFamilyBody := rfl

theorem pinchTransport_eq_counted_regionPushOff :
    PinchTransport = Counted fun P _ s c σ u => Work.PinchFamily.RegionPushOff P s c σ u := rfl

/-! ## The general position of the cutting plane -/

/-- **The general-position datum of the cutting plane, in its weakest form.**  At every counted
configuration:

* the plane `{y (σ 2) = c (σ 2) + u}` meets the surface transversely along the slice inside the box
  (`Work.BoxShrink.Pinch.TransverseSlice`);
* the flat disc `cutDisc s c σ u` cut out of the box by the plane is **sliced** by the surface
  (`Work.Smooth.Plane.SlicedPlane`) — the planar analogue of the `SlicedSphere` hypothesis which
  the counted configuration already carries for the box sphere.

The second of the two is a `Work.Smooth.Plane.PlaneSlicing` datum: the trace `F ∩ cutDisc` is
finitely many pairwise disjoint embedded circles and arcs, each circle bounds a disc inside the
flat disc, with the nesting (`rank`) and covering properties of the classical
"a plane in general position cuts a surface in finitely many circles and arcs" theorem.  It is
consumed in two ways: it gives the innermost-disc input at the flat disc
(`Work.Smooth.Plane.innermostDiscInput_of_slicedPlane`), whence the *inessentiality* of the slice
from the counting (`sliceTrace_inessential_of_slicedPlane`), and it gives the tameness
(`tameSlice_of_slicedPlane`). -/
def CountedSlicePlane : Prop :=
  CountedD fun ψ _β _K _d s c σ u =>
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u ∧
      Work.Smooth.Plane.SlicedPlane (Work.Smooth.Morse.torus ψ) (flatDisc s c σ u)

/-- **The general-position datum of the cutting plane, in the two hypotheses the transport
theorem consumes.**  At every counted configuration:

* the plane meets the surface transversely along the slice (`TransverseSlice`);
* the slice is tame (`TameSlice`, i.e. `Work.Smooth.Plane.TransversePlane` for the flat disc);
* the slice carries no essential loop of the surface.

This is exactly the hypothesis list of the workspace's capstone
`Work.BoxShrink.PinchOff.regionEquivalent_halves_of_tameSlice`, hence of the push-off
(`pinchTransport_of_countedSliceGood`).  It is *derived* from `CountedSlicePlane` inside the
counted vocabulary (`countedSliceGood_of_countedSlicePlane`), the counting being used for the
third item through Pardon's Lemma 2 at the flat disc. -/
def CountedSliceGood : Prop :=
  CountedD fun ψ _β _K _d s c σ u =>
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u ∧
      Work.BoxShrink.Pinch.TameSlice ψ s c σ u ∧
        ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop (slice (Work.Smooth.Morse.torus ψ) s c σ u)

/-- **The sharpest spelling of the residual of this chapter: the plane datum.**

At every counted configuration:

* the plane meets the surface transversely along the slice (`TransverseSlice`);
* the slice is tame (`TameSlice`, i.e. `Work.Smooth.Plane.TransversePlane` for the flat disc);
* **Pardon's planar innermost-disc step at the flat disc** holds (`Work.InnermostDisk.InnermostDiscInput`):
  every essential loop of the surface inside the flat disc can be replaced by a simple essential
  compressing one inside the flat disc.

This is a *weakening* of `CountedSlicePlane` (a planar slicing datum `SlicedPlane` gives the
tameness and the innermost disc, `countedPlaneInput_of_countedSlicePlane`), and it still gives the
whole chain (`pinchTransport_of_countedPlaneInput` etc. in `Routes.lean`): the counting turns the
innermost disc into the inessentiality of the slice (Pardon's Lemma 2 at the flat disc), and the
workspace's capstone turns the three items into Pardon's push-off.  The item (IN) is
*Pardon's own* planar input: the classical "a plane in general position cuts a surface in finitely
many circles and arcs, one of which is innermost". -/
def CountedPlaneInput : Prop :=
  CountedD fun ψ _β _K _d s c σ u =>
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u ∧
      Work.BoxShrink.Pinch.TameSlice ψ s c σ u ∧
        Work.InnermostDisk.InnermostDiscInput (Work.Smooth.Morse.torus ψ) (flatDisc s c σ u)

/-- **The same datum in its *uniform* spelling**: the planar innermost-disc input is asked for
every convex planar region of the surface in general position
(`Work.Smooth.Plane.PlaneInnermostTransverseInput`), and the flat disc is convex planar
(`Work.BoxShrink.Pinch.isConvexPlanar_cutDisc`), so this implies `CountedPlaneInput`
(`countedPlaneInput_of_countedPlaneInputUniform`).

This is the spelling in which the workspace's planar chapter carries the input: for the standard
torus it is produced by the classical slicing input `PlaneSliceInput` and the planar
Jordan–Schoenflies theorem (`Work.Smooth.Plane.planeInnermostTransverseInput_of_planeSliceInput`). -/
def CountedPlaneInputUniform : Prop :=
  CountedD fun ψ _β _K _d s c σ u =>
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u ∧
      Work.BoxShrink.Pinch.TameSlice ψ s c σ u ∧
        Work.Smooth.Plane.PlaneInnermostTransverseInput (Work.Smooth.Morse.torus ψ)

/-- **The transversality of the cutting plane alone** (the first half of `CountedSlicePlane`), as a
residual of its own: it is the part of the general position that the workspace *refutes* for
configurations in general (`Work.BoxShrink.PinchOff.not_forall_transverseSlice`) and that the
counting is therefore required to supply. -/
def CountedSliceCrossing : Prop :=
  CountedD fun ψ _β _K _d s c σ u => Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u

/-- **The slice is a finite disjoint union of embedded arcs of the surface, closed at the ends.**

The *closure* of the slice is covered by finitely many pairwise disjoint embedded arcs whose images
lie in that closure.  This is the honest structure of the trace of a cutting plane: since Pardon's
box is open, a component of the trace which meets the box sphere runs *off* the box there, so its
endpoints are not in the slice; the compact arcs of this datum are the closures of the components,
with their endpoints on the sphere trace `∂PBox s c σ`, and their interiors in the slice.

It is this datum which gives, with no counting at all,

* the inessentiality of the slice (`no_essential_of_sliceArcsBody`, through the connectedness of
  the image of a closed curve and
  `Work.Smooth.Plane.Slicing.not_isEssential_of_range_subset_arc`), and
* the honest tameness `Work.BoxShrink.PinchOff.TameClosedSlice`
  (`tameClosedSlice_of_sliceArcsBody`).

**Warning (the reason for the shape of the definition).**  The *naive* version of this datum — the
arcs required to lie *in the slice* rather than in its closure — is what `SliceCompactArcsBody`
below records, and it is unusable: a finite union of compact arcs is compact, so it forces the slice
to be compact, i.e. to consist of circles only, while a genuine trace (whose components leave the
open box) is not compact.  The sibling chapter proves the same for its `SliceArcsOnly`
(`Work.BoxShrink.PinchOff.not_sliceArcsOnly_of_not_isCompact`); `Routes.lean`/`Arcs.lean` record
the corresponding refutation in the vocabulary of this chapter. -/
def SliceArcsBody (P : Work.CoreTopology.ParamTorus) (_β : Work.CoreTopology.ClosedCurve P)
    (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  ∃ (n : ℕ) (a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3)),
    (∀ j : Fin n, Function.Injective (a j)) ∧
      (∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval),
        a j x ∈ closure (slice P s c σ u)) ∧
      (Pairwise fun j j' : Fin n => Disjoint (Set.range (a j)) (Set.range (a j'))) ∧
      (closure (slice P s c σ u) ⊆ ⋃ j, Set.range (a j))

theorem sliceArcsBody_def {P : Work.CoreTopology.ParamTorus} {β : Work.CoreTopology.ClosedCurve P}
    {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    SliceArcsBody P β s c σ u ↔
      ∃ (n : ℕ) (a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3)),
        (∀ j : Fin n, Function.Injective (a j)) ∧
          (∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval),
            a j x ∈ closure (slice P s c σ u)) ∧
          (Pairwise fun j j' : Fin n => Disjoint (Set.range (a j)) (Set.range (a j'))) ∧
          (closure (slice P s c σ u) ⊆ ⋃ j, Set.range (a j)) := Iff.rfl

/-- **The naive, unusable form of the arcs datum** (recorded so that the reason for the shape of
`SliceArcsBody` is machine-checked): the slice is covered by finitely many pairwise disjoint
embedded arcs *lying in the slice*.

Since `ArcInterval = [0,1]` is compact, each image is compact, so a finite family of them exhibits
the slice as a compact set (`isCompact_slice_of_sliceCompactArcsBody`); for a genuine arc of the
trace — both of whose endpoints lie on the box sphere, which the open box excludes — this is
impossible (`not_sliceCompactArcsBody_of_not_isCompact`).  The datum is therefore *not* a residual
to reduce to. -/
def SliceCompactArcsBody (P : Work.CoreTopology.ParamTorus) (_β : Work.CoreTopology.ClosedCurve P)
    (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  ∃ (n : ℕ) (a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3)),
    (∀ j : Fin n, Function.Injective (a j)) ∧
      (∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval), a j x ∈ P.carrier) ∧
      (∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval), a j x ∈ flatDisc s c σ u) ∧
      (Pairwise fun j j' : Fin n => Disjoint (Set.range (a j)) (Set.range (a j'))) ∧
      (slice P s c σ u ⊆ ⋃ j, Set.range (a j))

theorem sliceCompactArcsBody_def {P : Work.CoreTopology.ParamTorus}
    {β : Work.CoreTopology.ClosedCurve P}
    {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    SliceCompactArcsBody P β s c σ u ↔
      ∃ (n : ℕ) (a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3)),
        (∀ j : Fin n, Function.Injective (a j)) ∧
          (∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval), a j x ∈ P.carrier) ∧
          (∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval), a j x ∈ flatDisc s c σ u) ∧
          (Pairwise fun j j' : Fin n => Disjoint (Set.range (a j)) (Set.range (a j'))) ∧
          (slice P s c σ u ⊆ ⋃ j, Set.range (a j)) := Iff.rfl

/-- **The arcs residual**: at every counted configuration the closure of the slice is a finite
disjoint union of embedded arcs of the surface (the honest structure of the trace of the cutting
plane).  Together with the transversality of the plane and the global general position of the
loops it gives Pardon's Lemma 3 in the counted form
(`countingHalf_of_countedSliceArcs`) with **no counting argument for the slice at all**: the
sphere count, the general position of the box sphere and the cut-and-paste of the counted
configuration supply the inessentiality of the *sphere* trace, and the arc structure supplies that
of the slice. -/
def CountedSliceArcs : Prop := Counted SliceArcsBody

/-! ## The counted restriction of the sibling chapter's drop case

The sibling chapter `Work.BoxShrink.PinchOff` names two residuals: the *drop case* `DropCase` (if
the box sphere, the slice and the two half-regions all carry no essential loop, then the box region
is at most one-dimensional) and its equivalent form `KeyTameClosed`.  **Both are refuted** in that
chapter: `Work.BoxShrink.PinchOff.RefuteDrop.not_dropCase : ¬ DropCase` and
`…not_keyTameClosed : ¬ KeyTameClosed`, at the explicit configuration `dropDiffeo, dropS, dropC,
dropCyc, dropU`, where all five hypotheses hold and the box region has rank `2`
(`RefuteDrop/Main.lean`).  So the *unrestricted* drop datum is not a live residual.

Nothing in that refutation is a counted configuration of the crux: it carries no knot, no distortion
bound and no intersection counts.  The **counted restriction** of the drop datum — asked only at the
configurations of the counting shell — is therefore not refuted by it, and it is the residual this
chapter uses for the non-compact case of the trace (the arcs route of `Arcs.lean`): Pardon's
dimension bound is exactly the content the counting is meant to make true, as the refutation of the
unrestricted form confirms. -/

/-- **The drop datum of the sibling chapter, at a single configuration.**  This is the body of
`Work.BoxShrink.PinchOff.DropCase`, read at fixed `(ψ, s, c, σ, u)`. -/
def DropBody (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
      Work.BoxShrink.PinchOff.TameClosedSlice ψ s c σ u →
    ¬ (Work.BoxShrink.PinchOff.surface ψ).ContainsEssentialLoop
        (Work.BoxShrink.PinchOff.SphereTrace s c σ) →
    ¬ (Work.BoxShrink.PinchOff.surface ψ).ContainsEssentialLoop
        (Work.BoxShrink.PinchOff.Sigma ψ s c σ u) →
    Work.SurgeryInvariance.WindingSpan (Work.BoxShrink.PinchOff.surface ψ)
        (Work.BoxShrink.PinchOff.Halves ψ s c σ u) = ⊥ →
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.BoxShrink.PinchOff.surface ψ)
        (Work.BoxShrink.PinchOff.Omega ψ s c σ)) ≤ 1

/-- **The counted restriction of the drop case**: Pardon's dimension bound at the counted
configurations of the crux.  The unrestricted form is refuted in the sibling chapter
(`Work.BoxShrink.PinchOff.RefuteDrop.not_dropCase`); the restriction to the counted configurations is
the residual of the arcs route (`countingHalf_of_countedSliceArcs_countedDrop`). -/
def CountedDrop : Prop := CountedD fun ψ _β _K _d s c σ u => DropBody ψ s c σ u

theorem dropBody_def {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    DropBody ψ s c σ u ↔
      (Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
          Work.BoxShrink.PinchOff.TameClosedSlice ψ s c σ u →
        ¬ (Work.BoxShrink.PinchOff.surface ψ).ContainsEssentialLoop
            (Work.BoxShrink.PinchOff.SphereTrace s c σ) →
        ¬ (Work.BoxShrink.PinchOff.surface ψ).ContainsEssentialLoop
            (Work.BoxShrink.PinchOff.Sigma ψ s c σ u) →
        Work.SurgeryInvariance.WindingSpan (Work.BoxShrink.PinchOff.surface ψ)
            (Work.BoxShrink.PinchOff.Halves ψ s c σ u) = ⊥ →
        Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.BoxShrink.PinchOff.surface ψ)
            (Work.BoxShrink.PinchOff.Omega ψ s c σ)) ≤ 1) := Iff.rfl

/-! ## Elementary set algebra of the configuration -/

/-- The slice is the complement of the two half-regions in the box region. -/
theorem slice_eq_box_sdiff_halves (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    slice P s c σ u = box P s c σ \ halves P s c σ u := by
  ext y
  constructor
  · intro hy
    obtain ⟨hyc, hyb, hyu⟩ := Work.BoxShrink.Core.mem_sliceRegion.mp hy
    refine ⟨Work.BoxShrink.Core.mem_boxRegion.mpr ⟨hyc, hyb⟩, ?_⟩
    rintro (hh | hh)
    · exact absurd (Work.BoxShrink.Core.mem_upperRegion.mp hh).2.2 (not_lt.mpr (le_of_eq hyu))
    · exact absurd (Work.BoxShrink.Core.mem_lowerRegion.mp hh).2.2 (not_lt.mpr (ge_of_eq hyu))
  · rintro ⟨hy, hh⟩
    obtain ⟨hyc, hyb⟩ := Work.BoxShrink.Core.mem_boxRegion.mp hy
    have hne : y (σ 2) = c (σ 2) + u := by
      by_contra hcon
      rcases lt_or_gt_of_ne hcon with hlt | hgt
      · exact hh (Set.mem_union_right _ (Work.BoxShrink.Core.mem_lowerRegion.mpr ⟨hyc, hyb, hlt⟩))
      · exact hh (Set.mem_union_left _ (Work.BoxShrink.Core.mem_upperRegion.mpr ⟨hyc, hyb, hgt⟩))
    exact Work.BoxShrink.Core.mem_sliceRegion.mpr ⟨hyc, hyb, hne⟩

/-- The box region is the union of the slice and the two half-regions. -/
theorem box_eq_halves_union_slice (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    box P s c σ = halves P s c σ u ∪ slice P s c σ u :=
  Work.BoxShrink.Core.boxRegion_eq_union P s c σ u

/-- The slice is the trace of the flat disc with the surface. -/
theorem slice_eq_inter_flatDisc (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    slice P s c σ u = P.carrier ∩ flatDisc s c σ u :=
  Work.BoxShrink.Core.sliceRegion_eq_carrier_inter_cutDisc P s c σ u

end

end Work.CountedPinch
