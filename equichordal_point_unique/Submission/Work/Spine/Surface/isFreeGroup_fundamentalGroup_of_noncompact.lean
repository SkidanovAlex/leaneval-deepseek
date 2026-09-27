import Mathlib
import Submission.Work.Topology.Surface.arcs_cw_inline
import Submission.Commons.AlgebraicTopology.FundamentalGroup.freeGroup_of_oneDimCWComplex
import Submission.Commons.Topology.CWComplex.exists_cwComplex_univ_of_isClosed_subspace

/-!
# The fundamental group of a connected non-compact Riemann surface is free

Johannsson/Stallings: the fundamental group of a connected non-compact Riemann surface is free.
This is the deliverable of the subproject `Work.Spine` (the topological input of Hubbard
Theorem 1.1.2).  Known routes and traps are recorded in `Submission/Work/Spine/DESIGN.md`.

## What this file contains

* `SpineDatum X` — the geometric input, in the sharpest form used by the project: a *wild graph*
  `S ⊆ X` presented by a locally finite family of injective arcs meeting pairwise in common
  endpoints (equivalently, by `Commons.Topology.Plane.*`'s locally finite families of segments in
  the plane case, cf. `Work/Topology/Surface/spine_subgraph_closed_of_isOpen.lean` and its
  `IsWallSpine`).  Together with a homotopy equivalence `X ≃ₕ ↥S`, this datum produces a genuine
  CW structure on *all* of the witness `↥S` with no cells of dimension `≥ 2`
  (`SpineDatum.exists_cwComplex`).
* `isFreeGroup_fundamentalGroup_of_spineDatum` — **the assembly**: a space with such a spine has
  free fundamental group.  This is where the whole algebraic topology of the project is consumed
  (`Commons.AlgebraicTopology.FundamentalGroup.freeGroup_of_oneDimCWComplex`).
* `exists_spineDatum_homotopyEquiv_of_noncompact` — **the geometric obligation** (Johansson /
  Stallings): a connected, second countable, non-compact Riemann surface has such a spine.  This
  is the single remaining gap of the subproject; it is stated here in the form in which the
  reduction chain of `Work/Topology/Surface/*` and `Commons/Topology/Plane/*` delivers it
  ("the spine of the surface is a subfamily of the walls of its cell decomposition").
* `isFreeGroup_fundamentalGroup_of_noncompact` — the target, derived from the two.

WARNING (traps already discovered, do not fall into them):
* `Commons.Topology.Surface.exists_homotopyEquiv_oneDimCWComplex_of_noncompact` and
  `Work.Spine.exists_homotopyEquiv_oneDimCWComplex_of_noncompact` (the file Spine.lean) are stated
  with a CW structure on `Set.univ` of a witness, but the vacuously-satisfiable variants with a CW
  structure on an arbitrary closed subspace `C` (e.g. `C = ∅`) must not be used.
* The *strong deformation retraction* form is FALSE for a locally finite graph spine: see the
  refutation in `DESIGN.md`.  In particular `Commons.Topology.Homotopy.exists_sdr_of_locallyFinite_closed_cover_folds`
  and `deformationRetract_of_chamber_folds` (whose folds fix the spine) cannot produce the spine.
  Accordingly the datum below asks only for a **homotopy equivalence** `X ≃ₕ ↥S` (the classical
  theorem), not for a collapse; the existing consumers of a collapse (the chamber engines) are to
  be used only with genuinely one-sided ("cusped") pieces.
* The "U-shape" polyomino spines `Work.Spine.Plane.spine U hU n` are NOT nested in `n`
  (`spine_mono` is false: the open top edge of a deeper cell below a coarse cell deletes part of
  the coarse spine); do not attempt to use them as a nested sequence without changing the
  exhaustion.
-/

open Set
open scoped Topology

namespace Work.Spine.Surface

universe u

/-- **A spine datum for `X`**: a "wild graph" `S ⊆ X` (a locally finite family of injective arcs
meeting pairwise in common endpoints) that is a homotopy model of `X`.

The arcs may accumulate at points *not* in `X` (the ends of `X`, or the boundary of a plane
domain); that is exactly what the lemma `D.lf` allows and why no *locally finite* spine exists in
general. -/
structure SpineDatum (X : Type u) [TopologicalSpace X] where
  /-- the index type of the arcs -/
  ι : Type u
  /-- the arcs -/
  γ : ι → C(Set.Icc (0:ℝ) 1, X)
  /-- the arcs are embedded -/
  inj : ∀ i, Function.Injective (γ i)
  /-- the family of arcs is locally finite -/
  lf : LocallyFinite (fun i => Set.range (γ i))
  /-- two distinct arcs meet only in common endpoints -/
  inter : ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) ⊆
    ({(γ i) 0, (γ i) 1} : Set X) ∩ ({(γ j) 0, (γ j) 1} : Set X)

namespace SpineDatum

variable {X : Type u} [TopologicalSpace X]

/-- The underlying set of the spine. -/
def carrier (D : SpineDatum X) : Set X := ⋃ i, Set.range (D.γ i)

lemma mem_carrier (D : SpineDatum X) {y : X} :
    y ∈ D.carrier ↔ ∃ i, y ∈ Set.range (D.γ i) := Set.mem_iUnion

end SpineDatum


/-! ## State of the art (read before continuing this file)

The *assembly* above is complete and sorry-free: **the whole difficulty of the target theorem is the
geometric obligation `exists_spineDatum_homotopyEquiv_of_noncompact`**.

### What is already proved elsewhere in the workspace (use it, do not redo it)

* `Commons.Topology.Surface.exists_locallyFinite_disk_tiling` — every connected second countable
  Riemann surface is the union of a *locally finite* family of closed discs with pairwise disjoint
  interiors (a "disc tiling"), each disc being the image of a chart disc
  (`Commons.Topology.Surface.exists_star_cover` supplies the underlying star-shaped pieces).
* `Commons.Topology.Plane.*` — the complete *planar* cell machinery: the dyadic cells, the maximal
  cells (`Commons.Topology.Plane.maximal_dyadicCells_locallyFinite`,
  `Commons.Topology.Plane.maxCell_interior_disjoint`), the locally finite segment families and
  their CW structure (`Commons.Topology.Plane.cwComplex_of_locallyFinite_segments_isOpen`), the
  polyomino collapses (`Commons.Topology.Plane.dyadicPolyomino_deformationRetract`), the three
  "cusp" folds of the plane design (`exists_fold_halfStrip`, `exists_fold_clamp_to_vertical_walls`,
  `exists_fold_slide_to_vertical_wall`, `exists_fold_corner_to_floor_wall`), and the reduction of
  the planar spine theorem to the *selection problem*
  `Commons.Topology.Surface.exists_wallSpine` inside
  `Submission/Work/Topology/Surface/spine_subgraph_closed_of_isOpen.lean` (23 000 lines, exactly
  one `sorry`, the selection problem).  The planar crux is: *choose a subfamily of the walls of the
  maximal-cell decomposition whose union is a homotopy model of the domain.*
* `Submission/Work/Topology/Surface/exists_deformationRetract_oneDimCW_of_noncompact.lean` — the
  *general* surface analogue: the whole assembly from a "band (cusp) decomposition" of `X`
  (`exists_deformationRetract_oneDimCW_of_band_decomposition`, proved) to a collapse of `X` onto a
  one-dimensional CW subgraph; its single remaining obligation is
  `exists_bandDecomposition_of_noncompact` (also unproved).
* `Submission.Work.Topology.Surface.arcs_cw_inline` — the CW structure on a locally finite family
  of embedded arcs meeting pairwise in common endpoints (used by the assembly above), i.e. the
  "arc form" of the spine which is the form in which the planar machinery
  (`..._of_locallyFinite_segments_isOpen`) and the general band machinery deliver their spines.

### Traps (both re-derived here)

* A *closed* cover of `X` by pieces (a tiling by discs) can never be folded piecewise onto the
  union of the walls: every boundary point of a piece lies in another piece, hence in the spine,
  so the fold of a disc piece would be a retraction of the disc onto its boundary circle, which is
  impossible (Brouwer).  Equivalently: a fold of a piece `K` onto `S ∩ K` fixing `S ∩ K` forces
  `H₂(K, S ∩ K) = 0`; for a disc with its full boundary fixed this group is `ℤ`.
* Consequently the pieces of any usable cover must be *one-sided*: each must reach an end of `X`
  (a "cusp"), which is why the cusp/band formulations (`A i ≅ C i × J i`, `J i ∋ 0`) are the ones
  the workspace reduces to.
* The *collapse* (SDR) form in the plane case is recorded as refuted in
  `Submission/Work/Topology/Surface/spine_subgraph_closed_of_isOpen.lean` (from an argument with
  the winding numbers around the punctures of `ℂ ∖ {1/n}`, a *non-open* example); the *homotopy
  equivalence* form is the classical theorem and is the one used in the datum above.
-/

variable {X : Type u} [TopologicalSpace X]

/-- **The spine is closed.**  Each arc is compact, so the family is a locally finite family of
closed sets; its union is closed. -/
theorem SpineDatum.isClosed_carrier [T2Space X] (D : SpineDatum X) : IsClosed D.carrier := by
  refine LocallyFinite.isClosed_iUnion D.lf (fun i => ?_)
  exact (isCompact_range (D.γ i).2).isClosed

/-- **The spine carries a CW structure with no cells of dimension `≥ 2`** (on the subspace
`carrier`): the cells are the arcs (`1`-cells) and the marked vertices (`0`-cells). -/
theorem SpineDatum.exists_cwComplex [T2Space X] (D : SpineDatum X) :
    ∃ hC : @Topology.CWComplex X _ D.carrier,
      ∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell X _ D.carrier hC n) := by
  obtain ⟨hC, hdim⟩ :=
    ArcCWInline.cwComplex_of_locallyFinite_arcs
      D.γ D.inj D.lf D.inter
  exact ⟨hC, hdim⟩

/-- **The assembly**: a space carrying a homotopy model given by a wild graph spine has free
fundamental group.

All the algebraic topology is in
`Commons.AlgebraicTopology.FundamentalGroup.freeGroup_of_oneDimCWComplex`: freeness of `π₁` of a
Hausdorff space carrying a CW structure on all of itself with no cells of dimension `≥ 2`.  The CW
structure of `D.carrier` (on the *subspace*) is transported to the subtype `↥D.carrier` with
`Commons.Topology.CWComplex.exists_cwComplex_univ_of_isClosed_subspace`, and the homotopy
equivalence `X ≃ₕ ↥D.carrier` is `he`. -/
theorem isFreeGroup_fundamentalGroup_of_spineDatum
    [T2Space X] [ConnectedSpace X] (D : SpineDatum X)
    (he : Nonempty (ContinuousMap.HomotopyEquiv X ↥D.carrier)) (x : X) :
    IsFreeGroup (FundamentalGroup X x) := by
  obtain ⟨hC, hdim⟩ := D.exists_cwComplex
  obtain ⟨hC', hcell'⟩ :=
    Commons.Topology.CWComplex.exists_cwComplex_univ_of_isClosed_subspace D.isClosed_carrier hC
  exact Commons.AlgebraicTopology.FundamentalGroup.freeGroup_of_oneDimCWComplex x
    ⟨↥D.carrier, inferInstance, inferInstance, hC', fun n hn => hcell' n (hdim n hn), he⟩


/-- **Interface with the existing chain of the subproject.**  The `SpineDatum` of this file is a
*stronger* input than the space-level statement of `Work.Spine.Spine.lean` (a homotopy equivalence
to a Hausdorff space carrying a CW structure on *all* of its points with no cells of dimension
`≥ 2`): take the carrier `D.carrier`, whose CW structure (on the subspace) transports to the
subtype by `Commons.Topology.CWComplex.exists_cwComplex_univ_of_isClosed_subspace`.  Hence any
proof of the geometric obligation of this file feeds the whole existing assembly layer
(`Work.Spine.isFreeGroup_fundamentalGroup_of_oneDimCWComplex`,
`Work.Spine.simplyConnectedSpace_of_subsingleton_hom_toReal`). -/
theorem exists_homotopyEquiv_oneDimCWComplex_of_spineDatum
    [T2Space X] (D : SpineDatum X)
    (he : Nonempty (ContinuousMap.HomotopyEquiv X ↥D.carrier)) :
    ∃ (Y : Type u) (tY : TopologicalSpace Y), @T2Space Y tY ∧
      ∃ (hC : @Topology.CWComplex Y tY Set.univ),
        (∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell Y tY Set.univ hC n)) ∧
        Nonempty (@ContinuousMap.HomotopyEquiv X Y _ tY) := by
  obtain ⟨hC, hdim⟩ := D.exists_cwComplex
  obtain ⟨hC', hcell'⟩ :=
    Commons.Topology.CWComplex.exists_cwComplex_univ_of_isClosed_subspace D.isClosed_carrier hC
  exact ⟨↥D.carrier, inferInstance, inferInstance, hC', fun n hn => hcell' n (hdim n hn), he⟩

/-- **The geometric obligation (Johansson/Stallings).**

A connected, second countable, non-compact Riemann surface has a wild graph spine which is a
homotopy model of it.  Equivalently: the surface is homotopy equivalent to a one-dimensional CW
complex.  The classical route exhausts the surface by compact subsurfaces whose spines are
subfamilies of the walls of a locally finite tiling, and passes to the homotopy colimit; the
"spine" accumulates at the ends of `X`, which is why the arcs of `D` are allowed to accumulate at
points outside `X`. -/
theorem exists_spineDatum_homotopyEquiv_of_noncompact
    [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) :
    ∃ D : SpineDatum X, Nonempty (ContinuousMap.HomotopyEquiv X ↥D.carrier) := by
  sorry


/-- **The geometric obligation in the CW-subspace form**, which is the form in which the existing
general-surface machinery delivers its output
(`Submission.Work.Topology.Surface.exists_deformationRetract_oneDimCW_of_band_decomposition`, whose
input is the "band (cusp) decomposition" obligation
`exists_bandDecomposition_of_noncompact` of that file).  The two forms are inter-derivable: the
CW-subspace form is exactly what a closed one-dimensional CW spine gives, and conversely a
`SpineDatum` produces one (`SpineDatum.exists_cwComplex`). -/
theorem exists_cwSpine_of_noncompact
    [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) :
    ∃ (G : Set X) (hC : @Topology.CWComplex X _ G),
      (∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell X _ G hC n)) ∧
      Nonempty (ContinuousMap.HomotopyEquiv X ↥G) := by
  obtain ⟨D, he⟩ := exists_spineDatum_homotopyEquiv_of_noncompact (X := X) hX
  obtain ⟨hC, hdim⟩ := D.exists_cwComplex
  exact ⟨D.carrier, hC, hdim, he⟩

/-- **Johannsson/Stallings: the fundamental group of a connected non-compact Riemann surface is
free.**  This is the deliverable of the subproject `Work.Spine` (the topological input of Hubbard
Theorem 1.1.2). -/
theorem isFreeGroup_fundamentalGroup_of_noncompact
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (x : X) : IsFreeGroup (FundamentalGroup X x) := by
  obtain ⟨D, he⟩ := exists_spineDatum_homotopyEquiv_of_noncompact (X := X) hX
  exact isFreeGroup_fundamentalGroup_of_spineDatum D he x

end Work.Spine.Surface
