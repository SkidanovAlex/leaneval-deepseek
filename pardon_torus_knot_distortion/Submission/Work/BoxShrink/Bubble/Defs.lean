import Submission.Work.BoxShrink.Core.Bubble.Instances

/-!
# `Work.BoxShrink.Bubble` — Pardon's double bubble for the box/plane configuration

This is the vocabulary of the chapter proving the field `bubble` of
`Work.BoxShrink.Core.BubbleInput`: **Pardon's double bubble** for the pair

  `(S, D)`,  `S = ∂PBox s c σ = sphereSet c σ s`,  `D = cutDisc s c σ u`,

whose two halves bound the two half-bodies `H₁, H₂` with

  `F ∩ int(H₁) = upperRegion P s c σ u`,  `F ∩ int(H₂) = lowerRegion P s c σ u`.

The chapter's main theorem is `Work.BoxShrink.Bubble.bubble_of_slicePushOff`: Pardon's double
bubble for every configuration in which the loop content of the region inside the sphere can be
transported off the slicing plane (`SlicePushOff`), which is the single geometric statement the
construction consumes; the statement is isolated, named and documented, and the concrete cases in
which it is *proved* here are collected in `Instances.lean`.

## The picture

`boxRegion P s c σ = F ∩ PBox s c σ` is the region inside the sphere, and cutting it by the
slicing plane gives

  `boxRegion = (upperRegion ∪ lowerRegion) ∪ sliceRegion`

with the slice `sliceRegion = F ∩ D` **closed** in the surface.  Pardon's family of spheres
pinches `S` along `D`: as the collar of `S` around `∂D` is replaced by the two sheets of `D`,
the region `F ∩ int(S_t)` loses the trace of the neck of the pinch, an **open** piece of `F`
(whose boundary curve lies on the sphere `S_t` and is therefore inessential, by the count
hypothesis).  The loop-level content of the family is exactly `SweepLoops`, and the two endpoints
are forced:

* at time `0` the family is `boxRegion` (`F ∩ int(S) = F ∩ PBox`);
* at time `1` it is `upperRegion ∪ lowerRegion` (the two halves of the double bubble).

This file sets up:

* the pieces of the picture: `outsideRegion` (the trace of the exterior of the box),
  `slab` (the slab around the cutting plane), `exteriorCollar` (the trace of the exterior of the
  box inside the slab), `neck` (the slice together with the exterior collar) and `pinchedRegion`
  (the region inside the box together with the exterior collar);
* `RealizedWindings P X` — the set of winding vectors realised by loops of `F` inside `X`;
* `SlicePushOff P s c σ u` — **the geometric input of the construction**: every winding vector
  realised inside the box is realised away from the slicing plane;
* `PushOffDatum P s c σ u` — the same input in the loop-level form
  `RegionEquivalent P (boxRegion) (upperRegion ∪ lowerRegion)`;
* `HasOutsidePiece P s c σ` — the existence of a piece of the surface outside the box whose
  winding span vanishes (the "poke-out" used to make the closed slice open; it is *not* consumed by
  the reduction, because `Work.BoxShrink.Bubble.Obstruction`
  (`exists_open_inter_subset_of_removed`, `Obstruction.surgeryStepZero_eq_self_or_empty`) shows that
  no single `SurgeryStepZero` can remove the slice from a connected region in any case).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The pieces of the picture -/

/-- The **trace of the exterior of the box** on the surface: `F ∖ PBox s c σ`. -/
def outsideRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) : Set R3 :=
  P.carrier ∩ {y : R3 | y ∉ Submission.PBox s c σ}

/-- The **slab of half-width `δ`** around the cutting plane
`{y | y (σ 2) = c (σ 2) + u}`. -/
def slab (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (δ : ℝ) : Set R3 :=
  {y : R3 | |y (σ 2) - (c (σ 2) + u)| < δ}

/-- The **exterior collar**: the part of the surface outside the box, in the slab.  This is the
piece of `F` that Pardon's pinch may add to or remove from the region: it lies outside the box
and near the slicing plane, i.e. just beyond the circle `∂D` where the pinching sphere meets the
surface. -/
def exteriorCollar (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (δ : ℝ) : Set R3 :=
  outsideRegion P s c σ ∩ slab c σ u δ

/-- The **neck** of the pinch: the slice together with the exterior collar. -/
def neck (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (δ : ℝ) : Set R3 :=
  Work.BoxShrink.Core.sliceRegion P s c σ u ∪ exteriorCollar P s c σ u δ

/-- The **pinched region**: the region inside the box, together with the exterior collar.  This
is the intermediate region of the sweep: it is open in the surface, it contains `boxRegion`, and
removing the exterior collar from it returns `boxRegion`, while removing the neck (the slice
together with the exterior collar) returns `upperRegion ∪ lowerRegion`. -/
def pinchedRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (δ : ℝ) : Set R3 :=
  Work.BoxShrink.Core.boxRegion P s c σ ∪ exteriorCollar P s c σ u δ

@[simp] theorem mem_outsideRegion {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {y : R3} :
    y ∈ outsideRegion P s c σ ↔ y ∈ P.carrier ∧ y ∉ Submission.PBox s c σ := Iff.rfl

@[simp] theorem mem_slab {c : R3} {σ : Equiv.Perm (Fin 3)} {u δ : ℝ} {y : R3} :
    y ∈ slab c σ u δ ↔ |y (σ 2) - (c (σ 2) + u)| < δ := Iff.rfl

@[simp] theorem mem_exteriorCollar {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u δ : ℝ}
    {y : R3} :
    y ∈ exteriorCollar P s c σ u δ ↔
      y ∈ P.carrier ∧ y ∉ Submission.PBox s c σ ∧ |y (σ 2) - (c (σ 2) + u)| < δ := by
  simp only [exteriorCollar, Set.mem_inter_iff, mem_outsideRegion, mem_slab, and_assoc]

@[simp] theorem mem_neck {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u δ : ℝ} {y : R3} :
    y ∈ neck P s c σ u δ ↔
      (y ∈ P.carrier ∧ y ∈ Submission.PBox s c σ ∧ y (σ 2) = c (σ 2) + u) ∨
        (y ∈ P.carrier ∧ y ∉ Submission.PBox s c σ ∧ |y (σ 2) - (c (σ 2) + u)| < δ) := by
  simp only [neck, Set.mem_union, Work.BoxShrink.Core.mem_sliceRegion, mem_exteriorCollar]

@[simp] theorem mem_pinchedRegion {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u δ : ℝ}
    {y : R3} :
    y ∈ pinchedRegion P s c σ u δ ↔
      (y ∈ P.carrier ∧ y ∈ Submission.PBox s c σ) ∨
        (y ∈ P.carrier ∧ y ∉ Submission.PBox s c σ ∧ |y (σ 2) - (c (σ 2) + u)| < δ) := by
  simp only [pinchedRegion, Set.mem_union, Work.BoxShrink.Core.mem_boxRegion,
    mem_exteriorCollar]

/-! ## Realised winding vectors -/

/-- **The winding vectors realised by loops of the surface inside `X`**: the set of
`Work.SurgeryInvariance.windingOf P γ` for the closed curves `γ` of `F` whose image lies in `X`.

This is the "curve-level" content of the region `X`: `Work.SurgeryInvariance.WindingSpan P X` is
its `ℚ`-span, so vanishing windings are the same information for the two, but the realisation of
a *single* winding vector is what a `RegionEquivalent` transport needs. -/
def RealizedWindings (P : Work.CoreTopology.ParamTorus) (X : Set R3) : Set (ℤ × ℤ) :=
  {k | ∃ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ X) ∧
    Work.SurgeryInvariance.windingOf P γ = k}

theorem mem_realizedWindings {X : Set R3} {k : ℤ × ℤ} :
    k ∈ RealizedWindings P X ↔
      ∃ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ X) ∧
        Work.SurgeryInvariance.windingOf P γ = k := Iff.rfl

/-- The winding vectors realised in a subregion are realised in any larger region. -/
theorem RealizedWindings_mono {X Y : Set R3} (h : X ⊆ Y) :
    RealizedWindings P X ⊆ RealizedWindings P Y :=
  fun _ ⟨γ, hγ, hk⟩ => ⟨γ, fun t => h (hγ t), hk⟩

/-! ## The geometric input of the construction -/

/-- **The geometric input of Pardon's double bubble.**  Every winding vector realised by a loop
of the surface inside the box is realised by a loop of the surface *away from the slicing plane*,
i.e. in `upperRegion ∪ lowerRegion = boxRegion ∖ sliceRegion`.

Geometrically: the slice is the trace of the flat disc on the surface, and the hypothesis
`¬ P.ContainsEssentialLoop (sliceRegion P s c σ u)` (Pardon's plane count) says that the slice
carries no essential loop; the loops of the region inside the box can then be deformed off the
slice.  This is the push-off which the pinching family performs — it is the single geometric
statement the construction consumes, and it is *not* a consequence of the vanishing of the winding
spans (see the README: the analogous assertion with the closed slice replaced by an arbitrary
closed subset of the surface is false, e.g. for an annulus split into an open arc and its closed
complement).

**WARNING (stretch 17).**  `SlicePushOff` is **FALSE** in general: it fails at the standard torus of
revolution with `s = 5/2`, `c = 0`, `σ = Equiv.swap 1 2`, `u = 0`
(`Work.BoxShrink.Bubble.cex_not_slicePushOff`), where both `hS` and `hZ` hold.  The same holds for
`Work.BoxShrink.Bubble.PushOffInput` and `SlicePushOffSpan`; see
`Work.BoxShrink.Bubble.no_bubble_field` and the README, and use the corrected interfaces
`Work.BoxShrink.Bubble.BubbleHalf` / `PushOffHalf` / `SmoothHalf` (`Corrected.lean`) or Pardon's
own input `Work.BoxShrink.Bubble.PardonPinchInput` (`PardonLocalModel.lean`). -/
def SlicePushOff (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Prop :=
  RealizedWindings P (Work.BoxShrink.Core.boxRegion P s c σ) ⊆
    RealizedWindings P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪ Work.BoxShrink.Core.lowerRegion P s c σ u)

/-- **The input, globally**: the push-off for every box/plane configuration whose slicing plane
carries no essential loop of the surface.  This is the hypothesis in which the field `bubble` of
`Work.BoxShrink.Core.BubbleInput` is delivered here
(`Work.BoxShrink.Bubble.bubble_of_pushOffAll`,
`Work.BoxShrink.Bubble.bubbleFrom`). -/
def PushOffInput : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
    SlicePushOff P s c σ u

/-- **A neck component of the pinch**: a piece `C` of the region inside the box which

* contains the slice (`sliceRegion ⊆ C`),
* lies in the region (`C ⊆ boxRegion`),
* is *open and closed in the region* (`C` is open in the surface and `boxRegion ∖ C` is open in the
  surface — equivalently, `C` is clopen in the subspace `boxRegion`, which is what a `2`-surgery can
  add or remove, see `Obstruction.lean`),
* carries no essential loop (`WindingSpan P C = ⊥`).

This is the shape of Pardon's pinch: the collar of the slice around which the sphere family pinches,
cut out of the region along curves lying on the pinching sphere.  Exhibiting such a neck gives the
double bubble with no loop transport at all (`Work.BoxShrink.Bubble.bubbleSweep_of_neckComponent`):
the two-step family `boxRegion → boxRegion ∖ C → upperRegion ∪ lowerRegion` consists of two
`2`-surgeries, the removed pieces being `C` and `C ∩ (upperRegion ∪ lowerRegion)`, both of vanishing
winding span.

Because `C` must be clopen in the region, this route covers exactly the configurations in which the
region inside the box is *disconnected* with the slice lying in a zero-span component (if the region
is connected and the slice is nonempty then `C` is the whole region and the hypothesis forces
`WindingSpan P boxRegion = ⊥`).  For a connected region the family must contain a genuine
`RegionEquivalent` transport — the push-off `Work.BoxShrink.Bubble.SlicePushOff` — because by
`Work.BoxShrink.Bubble.Obstruction.surgeryStepZero_eq_self_or_empty` no `2`-surgery can remove a
point of the slice from a preconnected region. -/
structure NeckComponent (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) where
  /-- the neck -/
  C : Set R3
  /-- it lies in the region inside the box -/
  subset : C ⊆ Work.BoxShrink.Core.boxRegion P s c σ
  /-- it contains the slice -/
  slice_subset : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ C
  /-- it is open in the surface -/
  open' : Work.SurgeryInvariance.IsOpenInCarrier P C
  /-- it is closed in the region: the complement in the region is open in the surface -/
  closed' : Work.SurgeryInvariance.IsOpenInCarrier P
    (Work.BoxShrink.Core.boxRegion P s c σ \ C)
  /-- it carries no essential loop -/
  span : Work.SurgeryInvariance.WindingSpan P C = ⊥

/-- The region with the neck removed. -/
def neckRemoved {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {u : ℝ} (N : NeckComponent P s c σ u) : Set R3 :=
  Work.BoxShrink.Core.boxRegion P s c σ \ N.C

/-- **The same input in the loop-level (`RegionEquivalent`) form**: the region inside the sphere
and the union of the two half-regions carry the same loops with the same winding vectors.  This is
the conclusion of Pardon's `spherefamily`/`doublebubble` at the level of loops, and it is
`Work.BoxShrink.Core.DoubleBubbleDatum`. -/
def PushOffDatum (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Prop :=
  Work.BoxShrink.Core.DoubleBubbleDatum P s c σ u

/-- The **span-level content** of the input: the winding span of the region inside the sphere is
contained in that of the union of the two halves.  (The reverse containment is automatic, since
`upperRegion ∪ lowerRegion ⊆ boxRegion`; both together are what the persistence argument of
`Work.BoxShrink.Core.containsEssentialLoop_half_of_bubbleSweep` uses.) -/
def SlicePushOffSpan (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≤
    Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪ Work.BoxShrink.Core.lowerRegion P s c σ u)

/-- **The existence of a piece of the surface outside the box with vanishing winding span** (the
"poke-out" of the pinch): an open piece of `F` disjoint from the box whose loops are all
inessential.  Since the slice is *closed* in the surface, the region after the pinch can only be
reached from a region containing a neighbourhood of the slice if the neighbourhood has such a
piece to spread into; `Work.BoxShrink.Bubble.bubbleSweep_of_outsidePiece` shows that with such a
piece the construction of the sweep is complete. -/
def HasOutsidePiece (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) : Prop :=
  ∃ Z : Set R3, Work.SurgeryInvariance.IsOpenInCarrier P Z ∧
    Disjoint Z (Submission.PBox s c σ) ∧ Work.SurgeryInvariance.WindingSpan P Z = ⊥

/-- **Local two-sidedness of the surface at a point of the slicing plane**: every open
neighbourhood (in the surface) of a point of the slice meets `upperRegion ∪ lowerRegion`.

This is the statement that the surface `F` is locally `2`-dimensional at a point of the trace of
the slicing plane, and that the coordinate `y ↦ y (σ 2)` is locally non-constant there: a point of
`F ∩ {y (σ 2) = c (σ 2) + u}` has points of `F` with `y (σ 2) ≠ c (σ 2) + u` arbitrarily close to
it.  It is recorded as a hypothesis because a `Work.CoreTopology.ParamTorus` is only assumed to be
a *continuous* parametrisation (`ParamTorus` has no injectivity of the derivative). -/
def SliceLocallyTwoSided (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  ∀ x ∈ Work.BoxShrink.Core.sliceRegion P s c σ u, ∀ U : Set R3,
    Work.SurgeryInvariance.IsOpenInCarrier P U → x ∈ U →
      ∃ y ∈ U, y ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∨
        y ∈ Work.BoxShrink.Core.lowerRegion P s c σ u

end

end Work.BoxShrink.Bubble
