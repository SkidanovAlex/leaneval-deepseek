import Mathlib
import Submission.Work.Smooth.Plane.Defs

/-!
# The planar slicing of a convex planar region by the surface

This file is the planar counterpart of `Work.InnermostDisk.Slicing`: it sets up the datum in which
the *planar* innermost-disc argument of Pardon's shrink step is phrased — the analogue of
`Work.InnermostDisk.SphereSlicing` for a convex planar region `D` instead of a sphere `S`.

Let `F = P.carrier` be the surface of a parametrised torus and let `D ⊆ ℝ³` be a **convex planar
region** (`Work.Smooth.Plane.IsConvexPlanar`), for instance the slice
`PardonSlice s c σ u = PBox s c σ ∩ {y | y (σ 2) = c (σ 2) + u}` of Pardon's box.  If the plane
is in general position with respect to `F`, then `F ∩ D` is a compact `1`-dimensional submanifold
with boundary of `F`: finitely many pairwise disjoint **simple closed curves** of `F` (the closed
components) and finitely many pairwise disjoint **embedded arcs** of `F` (whose endpoints lie on
the boundary of `D`), and these cover `F ∩ D`.

The datum of the planar slicing is exactly this finite family, together with:

* the disc inside `D` that each **closed** component bounds (`disc`), which exists by the
  *planar Jordan–Schoenflies theorem in its convexity form*
  (`Work.Smooth.Plane.exists_spanningDisc_of_convex_planar`): a simple closed curve in a convex
  planar region bounds an embedded disc contained in that region;
* the nesting of those discs, witnessed by a rank function (`rank`, `inside`), exactly as in the
  spherical case: of two disjoint Jordan curves in a plane region, one lies inside the disc of the
  other.

The two *consequences* of the datum which the innermost argument needs are proved, not assumed, in
`Work.Smooth.Plane.SlicingReduce` (the fields `inside_subset` and `covers`, the latter using that a
loop of `F` lying in an arc of `F` is inessential, `Work.Smooth.Plane.not_isEssential_of_range_subset_arc`).

## Main definitions

* `ArcInterval` — the closed unit interval, the model of the arcs of `F ∩ D`;
* `PlaneSliceData P D` — the classical facts about the slicing of `D` by `F` (transversality,
  Jordan–Schoenflies, nesting);
* `PlaneSlicing P D` — the full slicing datum, with the covering property;
* `TransversePlane P D` — general position of the convex planar region with respect to `F`;
* `PlaneSliceInput P` — the classical slicing input: every convex planar region in general position
  admits a slicing datum;
* `SlicedPlane P D` — the planar analogue of `Work.BoxShrink.SlicedSphere`: `D` is sliced by `F`.

## Main results (this file)

* `PlaneSlicing.exists_component_of_isEssential` — an essential loop of `F` inside `D` lies on one
  of the closed components of the slicing;
* `PlaneSlicing.exists_min_essential` — some closed component is essential, and among the essential
  ones there is one of minimal rank;
* `PlaneSlicing.innermostDiscOfMinRank` — the innermost datum it produces: an `InnermostDisc`
  (`Work.InnermostDisk.InnermostDisc`) whose disc lies in `D`;
* `PlaneSlicing.innermostDiscInput_of_slicing` — Pardon's first innermost step for the planar
  region `D`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Plane

noncomputable section

/-! ## The classical facts: the slicing datum -/

/-- **A slicing datum of the convex planar region `D` by the surface `F = P.carrier`.**

This is the part of `PlaneSlicing P D` which is genuinely classical: `F ∩ D` is a finite disjoint
union of simple closed curves `c i` and embedded arcs `a j` of `F`, and every point of `F ∩ D`
lies on one of them (`covers_pt`); each closed component bounds an embedded disc inside `D`
(`disc`) whose interior is open in `D` (`open_interior`, the Jordan separation statement proper);
and the discs of the closed components are nested, witnessed by a rank function (`rank`,
`inside`). -/
structure PlaneSliceData (P : Work.CoreTopology.ParamTorus) (D : Set R3) where
  /-- the index type of the closed components of `F ∩ D` -/
  ι : Type
  /-- finitely many of them -/
  fintype : Fintype ι
  /-- the closed components -/
  c : ι → Work.CoreTopology.ClosedCurve P
  /-- each closed component is an embedded loop -/
  simple : ∀ i : ι, Work.CoreTopology.IsSimple P (c i)
  /-- distinct closed components are disjoint -/
  disjoint : Pairwise fun i j : ι => Disjoint (Set.range (c i).γ) (Set.range (c j).γ)
  /-- they lie in `D` -/
  mem : ∀ i : ι, ∀ t : ℝ, (c i).γ t ∈ D
  /-- the disc inside `D` bounded by a closed component -/
  disc : ι → C(Work.InnermostDisk.Disc, R3)
  /-- the disc is embedded -/
  disc_inj : ∀ i : ι, Function.Injective (disc i)
  /-- its boundary is the closed component -/
  disc_boundary : ∀ i : ι, ∀ θ : ℝ,
    disc i (Work.CoreTopology.circlePoint θ) = (c i).γ θ
  /-- the disc lies in `D` -/
  disc_mem : ∀ i : ι, ∀ z : Work.InnermostDisk.Disc, disc i z ∈ D
  /-- **Jordan separation**: the interior of the disc is open in `D` -/
  open_interior : ∀ i : ι,
    IsOpen {x : D | ∃ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 ∧ disc i z = (x : R3)}
  /-- **the arcs do not enter the discs**: the interior of the disc of a closed component meets the
  surface only along the closed components.

  This is classical for a *plane* slice of a surface, and it is where the convexity of `D` enters:
  the plane `Π` of the slice meets the (closed) surface `F` in a compact `1`-manifold without
  boundary, i.e. in finitely many pairwise disjoint circles of `F` (transversality); the closed
  components `c i` of `F ∩ D` are the circles contained in `D`, and the arcs are the parts of the
  remaining circles.  Two disjoint circles of `Π` bound either nested or disjoint discs, so a circle
  `C` which meets the interior of the disc of `c i` is contained in the inside region of `c i`;
  that region lies in `D` (this is the convexity form of Jordan–Schoenflies,
  `Work.Smooth.Plane.exists_spanningDisc_of_convex_planar`), so `C ⊆ D` and `C` is a closed
  component, i.e. one of the `c j`. -/
  covers_interior : ∀ i : ι, ∀ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 →
    disc i z ∈ P.carrier → ∃ j : ι, disc i z ∈ Set.range (c j).γ
  /-- the index type of the arcs of `F ∩ D` -/
  κ : Type
  /-- finitely many of them -/
  fintypeκ : Fintype κ
  /-- the arcs -/
  a : κ → C(ArcInterval, R3)
  /-- each arc is embedded -/
  a_inj : ∀ j : κ, Function.Injective (a j)
  /-- the arcs lie in `D` -/
  a_mem : ∀ j : κ, ∀ s : ArcInterval, a j s ∈ D
  /-- the arcs lie on the surface -/
  a_surface : ∀ j : κ, ∀ s : ArcInterval, a j s ∈ P.carrier
  /-- distinct arcs are disjoint -/
  a_disjoint : Pairwise fun j j' : κ => Disjoint (Set.range (a j)) (Set.range (a j'))
  /-- arcs and closed components are disjoint -/
  a_disjoint_c : ∀ j : κ, ∀ i : ι, Disjoint (Set.range (a j)) (Set.range (c i).γ)
  /-- every point of `F ∩ D` lies on a closed component or on an arc -/
  covers_pt : ∀ x : R3, x ∈ D → x ∈ P.carrier →
    (∃ i : ι, x ∈ Set.range (c i).γ) ∨ (∃ j : κ, x ∈ Set.range (a j))
  /-- the nesting rank of the closed components -/
  rank : ι → ℕ
  /-- a closed component meeting the interior of the disc of another has smaller rank -/
  inside : ∀ i j : ι, (∃ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 ∧
      disc i z ∈ Set.range (c j).γ) → rank j < rank i

attribute [instance] PlaneSliceData.fintype PlaneSliceData.fintypeκ

/-- **A slicing of the convex planar region `D` by the surface `F = P.carrier`**: the planar
analogue of `Work.InnermostDisk.SphereSlicing`.

The components of `F ∩ D` are finitely many pairwise disjoint simple closed curves `c i` and arcs
`a j` of `F`, each closed component bounds a disc inside `D` (`disc`), the family is nested
(`rank`, `inside`), and the family *covers* every loop of `F` contained in `D` (`covers`): a loop of
`F` inside `D` lies on one closed component or on one arc.  The two consequences
`inside_subset` (a closed component meeting the interior of the disc of another is contained in it)
and `covers_interior` (the interior of a disc meets `F` only along the closed components) are also
part of the datum, as in the spherical case. -/
structure PlaneSlicing (P : Work.CoreTopology.ParamTorus) (D : Set R3) where
  /-- the index type of the closed components of `F ∩ D` -/
  ι : Type
  /-- finitely many of them -/
  fintype : Fintype ι
  /-- the closed components -/
  c : ι → Work.CoreTopology.ClosedCurve P
  /-- each closed component is an embedded loop -/
  simple : ∀ i : ι, Work.CoreTopology.IsSimple P (c i)
  /-- distinct closed components are disjoint -/
  disjoint : Pairwise fun i j : ι => Disjoint (Set.range (c i).γ) (Set.range (c j).γ)
  /-- they lie in `D` -/
  mem : ∀ i : ι, ∀ t : ℝ, (c i).γ t ∈ D
  /-- the disc inside `D` bounded by a closed component -/
  disc : ι → C(Work.InnermostDisk.Disc, R3)
  /-- the disc is embedded -/
  disc_inj : ∀ i : ι, Function.Injective (disc i)
  /-- its boundary is the closed component -/
  disc_boundary : ∀ i : ι, ∀ θ : ℝ,
    disc i (Work.CoreTopology.circlePoint θ) = (c i).γ θ
  /-- the disc lies in `D` -/
  disc_mem : ∀ i : ι, ∀ z : Work.InnermostDisk.Disc, disc i z ∈ D
  /-- the nesting rank of the closed components -/
  rank : ι → ℕ
  /-- a closed component meeting the interior of the disc of another has smaller rank -/
  inside : ∀ i j : ι, (∃ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 ∧
      disc i z ∈ Set.range (c j).γ) → rank j < rank i
  /-- a closed component meeting the interior of the disc of another is contained in it -/
  inside_subset : ∀ i j : ι, (∃ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 ∧
      disc i z ∈ Set.range (c j).γ) → Set.range (c j).γ ⊆ Set.range (disc i)
  /-- the interior of a disc meets `F` only along the closed components -/
  covers_interior : ∀ i : ι, ∀ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 →
    disc i z ∈ P.carrier → ∃ j : ι, disc i z ∈ Set.range (c j).γ
  /-- the index type of the arcs of `F ∩ D` -/
  κ : Type
  /-- finitely many of them -/
  fintypeκ : Fintype κ
  /-- the arcs -/
  a : κ → C(ArcInterval, R3)
  /-- each arc is embedded -/
  a_inj : ∀ j : κ, Function.Injective (a j)
  /-- the arcs lie in `D` -/
  a_mem : ∀ j : κ, ∀ s : ArcInterval, a j s ∈ D
  /-- the arcs lie on the surface -/
  a_surface : ∀ j : κ, ∀ s : ArcInterval, a j s ∈ P.carrier
  /-- distinct arcs are disjoint -/
  a_disjoint : Pairwise fun j j' : κ => Disjoint (Set.range (a j)) (Set.range (a j'))
  /-- arcs and closed components are disjoint -/
  a_disjoint_c : ∀ j : κ, ∀ i : ι, Disjoint (Set.range (a j)) (Set.range (c i).γ)
  /-- **the covering property**: every loop of `F` inside `D` lies on a closed component or on
  an arc -/
  covers : ∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ.γ t ∈ D) →
    (∃ i : ι, Set.range γ.γ ⊆ Set.range (c i).γ) ∨ (∃ j : κ, Set.range γ.γ ⊆ Set.range (a j))

attribute [instance] PlaneSlicing.fintype PlaneSlicing.fintypeκ

/-! ## General position and the slicing input -/

/-- **General position of the convex planar region `D` with respect to the surface `F`**: the
intersection `F ∩ D` is the disjoint union of finitely many simple closed curves and embedded arcs
of `F`, each point of `F ∩ D` lying on one of them.

This is the planar analogue of `Work.Topology.SphereSlicing.TransverseSphere`: it is a hypothesis
on `D` (a plane in general position), not a consequence of convexity, and it cannot be dropped. -/
def TransversePlane (P : Work.CoreTopology.ParamTorus) (D : Set R3) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → Work.CoreTopology.ClosedCurve P) (κ : Type)
    (_ : Fintype κ) (a : κ → C(ArcInterval, R3)),
    (∀ i : ι, Work.CoreTopology.IsSimple P (c i)) ∧
    (Pairwise fun i j : ι => Disjoint (Set.range (c i).γ) (Set.range (c j).γ)) ∧
    (∀ i : ι, ∀ t : ℝ, (c i).γ t ∈ D) ∧
    (∀ j : κ, Function.Injective (a j)) ∧
    (∀ j : κ, ∀ s : ArcInterval, a j s ∈ D) ∧
    (∀ j : κ, ∀ s : ArcInterval, a j s ∈ P.carrier) ∧
    (Pairwise fun j j' : κ => Disjoint (Set.range (a j)) (Set.range (a j'))) ∧
    (∀ j : κ, ∀ i : ι, Disjoint (Set.range (a j)) (Set.range (c i).γ)) ∧
    (∀ x : R3, x ∈ D → x ∈ P.carrier →
      (∃ i : ι, x ∈ Set.range (c i).γ) ∨ (∃ j : κ, x ∈ Set.range (a j)))

/-- A slicing datum is in particular a transversality witness. -/
theorem transversePlane_of_sliceData {P : Work.CoreTopology.ParamTorus} {D : Set R3}
    (h : PlaneSliceData P D) : TransversePlane P D :=
  ⟨h.ι, h.fintype, h.c, h.κ, h.fintypeκ, h.a, h.simple, h.disjoint, h.mem, h.a_inj, h.a_mem,
    h.a_surface, h.a_disjoint, h.a_disjoint_c, h.covers_pt⟩

/-- **The slicing input**: every convex planar region in general position with respect to `F`
admits a slicing datum.

This is the classical content of "a plane in general position cuts a surface in finitely many
circles and arcs": the transversality (`TransversePlane`), the planar Jordan–Schoenflies theorem in
its convexity form (`Work.Smooth.Plane.exists_spanningDisc_of_convex_planar`) and the nesting of
finitely many disjoint Jordan curves in a plane region. -/
def PlaneSliceInput (P : Work.CoreTopology.ParamTorus) : Prop :=
  ∀ D : Set R3, IsConvexPlanar D → TransversePlane P D → Nonempty (PlaneSliceData P D)

/-- **The planar analogue of `Work.BoxShrink.SlicedSphere`**: the convex planar region `D` is
sliced by the surface `F = P.carrier`.  This is the general-position input consumed by
`Work.Smooth.Plane.Cleaning` and `Work.Smooth.Plane.Consequence`. -/
def SlicedPlane (P : Work.CoreTopology.ParamTorus) (D : Set R3) : Prop :=
  Nonempty (PlaneSlicing P D)

end

end Work.Smooth.Plane
