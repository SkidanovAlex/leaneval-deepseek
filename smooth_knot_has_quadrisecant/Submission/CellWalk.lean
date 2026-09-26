import Mathlib
import Submission.ChartRefine
import Submission.ComponentWalk
import Submission.ComponentChart
import Submission.ConnectedWalk

open LeanEval.KnotTheory.Quadrisecant
open LeanEval.KnotTheory.Quadrisecant.ConnectedWalk
open Set
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# S215 — the component traversal walk over the countable cell cover

S213 produced the countable cover of the trisecant set by chart CELLS
(`osub_countable_chartCell_cover`: each member is an interval-charted
open subregion of its parent chart's trace); S214 fixed the target
statement and decomposed it into L1–L4.  This module proves the
traversal:

- **L1–L2** (`centre_mem_own_cell`, `centreCell_subset_component_of_meets`):
  every centre lies in its own cell; a connected centre cell meeting the
  connected component is contained in it (so the centres of the cells
  covering a component lie in the component themselves);
- **`component_cell_cover`** (L3): the cells centred at classes of the
  component itself form a countable enumerated cover of the component
  (`eq_open_union_nat` over the second-countable trisecant set, exactly
  as the S107 `component_countable_chart_cover` pattern);
- **`component_cell_traversal`** (L4, the S214 target): over a connected
  component of the trisecant set there is an enumeration `Y` of centres
  of the component such that (i) consecutive cells meet,
  (ii) the prefixes `⋃ m ∈ Iio (n+1), cell(Y m)` are path-connected
  open sets contained in and exhausting the component, and
  (iii) `connectedComponent c₀ ⊆ ⋃ n, cell(Y n)`.

The proof instantiates the generic walk machinery
(`ConnectedWalk.exists_pathConnected_open_exhaustion`) over the
component subspace `ComponentSub c₀` exactly as the S115
`component_trace_walk` did for chart traces, replacing traces by cells;
the ambient-level path-connectedness of the prefix unions transfers
through the embedding `ComponentSub c₀ → OSub r` via
`Topology.IsInducing.isPathConnected_iff` and
`Subtype.image_preimage_val`.

Together with the S210/S212 content (two cells meeting in a common
interval-charted cell within a common region) this certifies the per-step
overlaps of the exhaustion — clause (i) of the exhaustion ordering of
the interval side of the component classification.

Everything here is verified (no axioms, no `sorry`).
-/

/-- The canonical basis cell of the chart at a class `y` (the S213
cover cell centred at `y`). -/
abbrev centreCell {r : ℝ → Space} (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (y : OSub r) : Set (OSub r) :=
  chartCell (oChartAtClass h hqf hgp y)
    (basisCellA (oChartAtClass h hqf hgp y)
      (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem))
    (basisCellB (oChartAtClass h hqf hgp y)
      (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem))

/-- **L1 — every centre lies in its own cell.** -/
lemma centre_mem_own_cell {r : ℝ → Space} (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (y : OSub r) :
    y ∈ centreCell h hqf hgp y := by
  have hspec := basisCell_spec (oChartAtClass h hqf hgp y)
    (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem)
  simpa [centreCell, chParam_lift] using hspec.2.1

/-- The coordinate interval of the centre cell is nondegenerate. -/
lemma centreCell_lt {r : ℝ → Space} (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (y : OSub r) :
    basisCellA (oChartAtClass h hqf hgp y)
      (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem) <
    basisCellB (oChartAtClass h hqf hgp y)
      (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem) := by
  have hspec := basisCell_spec (oChartAtClass h hqf hgp y)
    (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem)
  exact lt_trans hspec.1.1 hspec.1.2

/-- The centre cell is interval-charted (S211 applied to the basis
cell). -/
lemma centreCell_charted {r : ℝ → Space} (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (y : OSub r) :
    Nonempty (ChartInterval
      (basisCellA (oChartAtClass h hqf hgp y)
        (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem))
      (basisCellB (oChartAtClass h hqf hgp y)
        (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem)) ≃ₜ
      {c : OSub r // c ∈ centreCell h hqf hgp y}) := by
  have hspec := basisCell_spec (oChartAtClass h hqf hgp y)
    (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem)
  exact ⟨chartCellHomeo (oChartAtClass h hqf hgp y) hspec.2.2⟩

/-- The centre cell is connected (interval-charted, nondegenerate
interval). -/
lemma centreCell_isConnected {r : ℝ → Space} (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (y : OSub r) :
    IsConnected (centreCell h hqf hgp y) := by
  let A := basisCellA (oChartAtClass h hqf hgp y)
    (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem)
  let B := basisCellB (oChartAtClass h hqf hgp y)
    (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem)
  rcases centreCell_charted h hqf hgp y with ⟨e⟩
  have hlt : A < B := centreCell_lt h hqf hgp y
  haveI : PathConnectedSpace (ChartInterval A B) := chartInterval_pathConnected hlt
  haveI : ConnectedSpace {c : OSub r // c ∈ centreCell h hqf hgp y} :=
    (Homeomorph.connectedSpace_iff e).mp PathConnectedSpace.connectedSpace
  have hpre : IsPreconnected (centreCell h hqf hgp y) :=
    (isPreconnected_iff_preconnectedSpace).mpr inferInstance
  exact ⟨⟨y, centre_mem_own_cell h hqf hgp y⟩, hpre⟩

/-- The centre cell is path-connected (interval-charted). -/
lemma centreCell_pathConnected {r : ℝ → Space} (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (y : OSub r) :
    IsPathConnected (centreCell h hqf hgp y) := by
  let A := basisCellA (oChartAtClass h hqf hgp y)
    (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem)
  let B := basisCellB (oChartAtClass h hqf hgp y)
    (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem)
  rcases centreCell_charted h hqf hgp y with ⟨e⟩
  have hlt : A < B := centreCell_lt h hqf hgp y
  haveI : PathConnectedSpace (ChartInterval A B) := chartInterval_pathConnected hlt
  -- IsPathConnected (univ : Set (ChartInterval A B)) under the homeo e to the cell-subtype
  have h1 : IsPathConnected (e '' (Set.univ : Set (ChartInterval A B))) := by
    have hu : IsPathConnected (Set.univ : Set (ChartInterval A B)) := isPathConnected_univ (X := ChartInterval A B)
    exact (Homeomorph.isPathConnected_image e).mpr hu
  have h2 : IsPathConnected (Set.univ : Set {c : OSub r // c ∈ centreCell h hqf hgp y}) := by
    simpa using h1
  haveI : PathConnectedSpace {c : OSub r // c ∈ centreCell h hqf hgp y} :=
    (pathConnectedSpace_iff_univ).mpr h2
  exact (isPathConnected_iff_pathConnectedSpace).mpr inferInstance

/-- **L2 — a connected centre cell meeting the component is contained in
it.**  If the cell of `y` meets `connectedComponent c₀`, then the whole
cell lies in that component (a connected set containing a point of a
connected component is contained in it). -/
lemma centreCell_subset_component_of_meets {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r) (y : OSub r)
    {c₀ : OSub r} (hmeet : (centreCell h hqf hgp y ∩ connectedComponent c₀).Nonempty) :
    centreCell h hqf hgp y ⊆ connectedComponent c₀ := by
  rcases hmeet with ⟨c, hc⟩
  have hconn := centreCell_isConnected h hqf hgp y
  have hsub := hconn.subset_connectedComponent hc.1
  have heq : connectedComponent c = connectedComponent c₀ :=
    (connectedComponent_eq (x := c₀) (y := c) hc.2).symm
  intro z hz
  simpa [heq] using hsub hz

/-- The cell centred at a class of the component is contained in the
component (derived from L1 + L2). -/
lemma centreCell_subset_component {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r)
    {y : OSub r} (hy : y ∈ connectedComponent c₀) :
    centreCell h hqf hgp y ⊆ connectedComponent c₀ :=
  centreCell_subset_component_of_meets h hqf hgp y (c₀ := c₀)
    ⟨y, centre_mem_own_cell h hqf hgp y, hy⟩

/-- Membership in an `Iio`-indexed union of sets. -/
private lemma mem_iUnion_Iio_cw (X : Type*) (U : ℕ → Set X) (n : ℕ) (x : X) :
    (x ∈ ⋃ m ∈ Set.Iio n, U m) ↔ ∃ m : ℕ, m < n ∧ x ∈ U m := by
  simp

/-- **L3 — the countable enumerated cover of a component by centre
cells.**  The cells centred at the classes of the component itself cover
the component (each class lies in its own cell), and the component is a
hereditarily-Lindelöf subspace of the second-countable trisecant set, so
there is a ℕ-enumeration `Y` of such centres whose cells cover the
component. -/
lemma component_cell_cover {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r) :
    ∃ Y : ℕ → OSub r,
      (∀ n : ℕ, Y n ∈ connectedComponent c₀) ∧
      (∀ y : OSub r, y ∈ connectedComponent c₀ → ∃ n : ℕ, y ∈ centreCell h hqf hgp (Y n)) := by
  classical
  let ι : Type := {x : OSub r // x ∈ connectedComponent c₀}
  have hι : Nonempty ι := ⟨⟨c₀, mem_connectedComponent⟩⟩
  let U : ι → Set (OSub r) := fun x => centreCell h hqf hgp x.1
  have hUo : ∀ i : ι, IsOpen (U i) := by
    intro i
    dsimp [U]
    simpa [centreCell] using isOpen_chartCell (oChartAtClass h hqf hgp i.1) _ _
  have hcov : (connectedComponent c₀ : Set (OSub r)) ⊆ ⋃ i : ι, U i := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, centre_mem_own_cell h hqf hgp y⟩
  rcases eq_open_union_nat (U := U) hUo with ⟨k, hk⟩
  let Y : ℕ → OSub r := fun n => (k n).1
  refine ⟨Y, ?_, ?_⟩
  · intro n
    dsimp [Y]
    exact (k n).2
  · intro y hy
    have hycov : y ∈ ⋃ i : ι, U i := by
      exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, centre_mem_own_cell h hqf hgp y⟩
    rw [← hk] at hycov
    rcases Set.mem_iUnion.mp hycov with ⟨n, hyn⟩
    refine ⟨n, ?_⟩
    simpa [Y, U] using hyn

/-- **L4 — the component traversal walk over the cell cover (S214
target).**  There is an enumeration `Y` of centre classes of a connected
component of the trisecant set such that consecutive cells meet, the
prefix unions `Pₙ = ⋃ m ∈ Iio (n+1), cell(Y m)` are path-connected open
sets contained in the component and increasing, the nested prefixes
exhaust the component, and the single cells already cover the component.
This is the enumeration input of the interval-chain-ordering construction
(clause (i) of the exhaustion ordering of the interval side). -/
theorem component_cell_traversal {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r) :
    ∃ Y : ℕ → OSub r,
      (∀ n : ℕ, Y n ∈ connectedComponent c₀) ∧
      (∀ n : ℕ, (centreCell h hqf hgp (Y n) ∩ centreCell h hqf hgp (Y (n + 1))).Nonempty) ∧
      (∀ n : ℕ, IsPathConnected (⋃ m ∈ Set.Iio (n + 1), centreCell h hqf hgp (Y m))) ∧
      (∀ n : ℕ, IsOpen (⋃ m ∈ Set.Iio (n + 1), centreCell h hqf hgp (Y m))) ∧
      (∀ n : ℕ, (⋃ m ∈ Set.Iio (n + 1), centreCell h hqf hgp (Y m)) ⊆ connectedComponent c₀) ∧
      (∀ n : ℕ, (⋃ m ∈ Set.Iio (n + 1), centreCell h hqf hgp (Y m)) ⊆
        ⋃ m ∈ Set.Iio (n + 2), centreCell h hqf hgp (Y m)) ∧
      (connectedComponent c₀ ⊆
        ⋃ n : ℕ, ⋃ m ∈ Set.Iio (n + 1), centreCell h hqf hgp (Y m)) ∧
      (connectedComponent c₀ ⊆ ⋃ n : ℕ, centreCell h hqf hgp (Y n)) := by
  classical
  rcases component_cell_cover h hqf hgp c₀ with ⟨Y0, hY0mem, hY0cov⟩
  -- the cell cover on the component subspace ComponentSub c₀
  let U : ℕ → Set (ComponentSub c₀) :=
    fun n => {p : ComponentSub c₀ | (p : OSub r) ∈ centreCell h hqf hgp (Y0 n)}
  have hUo : ∀ n, IsOpen (U n) := by
    intro n
    dsimp [U]
    exact ((isOpen_chartCell (oChartAtClass h hqf hgp (Y0 n)) _ _).preimage continuous_subtype_val)
  have hUn : ∀ n, (U n).Nonempty := by
    intro n
    refine ⟨⟨Y0 n, hY0mem n⟩, ?_⟩
    dsimp [U]
    exact centre_mem_own_cell h hqf hgp (Y0 n)
  have hUcov : ∀ p : ComponentSub c₀, ∃ n, p ∈ U n := by
    intro p
    rcases hY0cov p.1 p.2 with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    dsimp [U]
    exact hn
  have hUpc : ∀ n, IsPathConnected (U n) := by
    intro n
    let T : Set (OSub r) := centreCell h hqf hgp (Y0 n)
    have hTpc : IsPathConnected T := centreCell_pathConnected h hqf hgp (Y0 n)
    have hTsub : T ⊆ connectedComponent c₀ := centreCell_subset_component h hqf hgp c₀ (hY0mem n)
    have hUn_eq : U n = (fun p : ComponentSub c₀ => (p : OSub r)) ⁻¹' T := by
      ext p
      rfl
    rw [hUn_eq]
    rw [(Topology.IsInducing.isPathConnected_iff
        (X := ComponentSub c₀) (Y := OSub r)
        (f := fun p : ComponentSub c₀ => (p : OSub r))
        (F := (fun p : ComponentSub c₀ => (p : OSub r)) ⁻¹' T)
        (Topology.IsInducing.subtypeVal (Y := OSub r) (t := connectedComponent c₀)))]
    rw [Subtype.image_preimage_val (connectedComponent c₀) T]
    rw [Set.inter_comm]
    rw [Set.inter_eq_left.mpr hTsub]
    exact hTpc
  rcases exists_pathConnected_open_exhaustion
    (X := ComponentSub c₀) U hUo hUn hUcov hUpc with
    ⟨e, V, e0, esurj, hadj, hVopen, hVpc, hVinc, hVcov, hVeq⟩
  let Y : ℕ → OSub r := fun n => Y0 (e n)
  refine ⟨Y, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hY0mem (e n)
  · intro n
    rcases hadj n with ⟨p, hpU1, hpU2⟩
    refine ⟨(p : OSub r), hpU1, hpU2⟩
  · intro n
    have hcont : Continuous (fun p : ComponentSub c₀ => (p : OSub r)) := continuous_subtype_val
    have himg : IsPathConnected ((fun p : ComponentSub c₀ => (p : OSub r)) '' V n) :=
      (hVpc n).image hcont
    have hcells : (fun p : ComponentSub c₀ => (p : OSub r)) '' V n =
        (⋃ m ∈ Set.Iio (n + 1), centreCell h hqf hgp (Y m)) := by
      ext y
      rw [mem_iUnion_Iio_cw]
      constructor
      · rintro ⟨p, hpV, rfl⟩
        rw [hVeq n] at hpV
        rw [mem_iUnion_Iio_cw] at hpV
        rcases hpV with ⟨m, hm, hpm⟩
        refine ⟨m, hm, ?_⟩
        simpa [U, Y] using hpm
      · rintro ⟨m, hm, hym⟩
        refine ⟨⟨y, centreCell_subset_component h hqf hgp c₀ (hY0mem (e m)) hym⟩, ?_, rfl⟩
        rw [hVeq n]
        rw [mem_iUnion_Iio_cw]
        refine ⟨m, hm, ?_⟩
        simpa [U, Y] using hym
    rwa [← hcells]
  · intro n
    -- the prefix is open in OSub r as a union of open cells
    exact isOpen_biUnion (fun m hm => isOpen_chartCell (oChartAtClass h hqf hgp (Y m)) _ _)
  · intro n y hy
    rw [mem_iUnion_Iio_cw] at hy
    rcases hy with ⟨m, hm, hym⟩
    exact centreCell_subset_component h hqf hgp c₀ (hY0mem (e m)) hym
  · intro n y hy
    rw [mem_iUnion_Iio_cw] at hy
    rcases hy with ⟨m, hm, hym⟩
    have hyVn : (⟨y, centreCell_subset_component h hqf hgp c₀ (hY0mem (e m)) hym⟩ :
        ComponentSub c₀) ∈ V n := by
      rw [hVeq n]
      rw [mem_iUnion_Iio_cw]
      refine ⟨m, hm, ?_⟩
      simpa [U, Y] using hym
    have hyVn1 : (⟨y, centreCell_subset_component h hqf hgp c₀ (hY0mem (e m)) hym⟩ :
        ComponentSub c₀) ∈ V (n + 1) :=
      hVinc n hyVn
    rw [hVeq (n + 1)] at hyVn1
    rw [mem_iUnion_Iio_cw] at hyVn1
    rcases hyVn1 with ⟨m', hm', hpm'⟩
    have hym' : y ∈ centreCell h hqf hgp (Y m') := by
      simpa [U, Y] using hpm'
    exact Set.mem_iUnion₂.mpr ⟨m', Set.mem_Iio.mpr hm', hym'⟩
  · intro y hy
    let p : ComponentSub c₀ := ⟨y, hy⟩
    rcases hVcov p with ⟨n, hpn⟩
    rw [hVeq n] at hpn
    rw [mem_iUnion_Iio_cw] at hpn
    rcases hpn with ⟨m, hm, hpm⟩
    have hym : y ∈ centreCell h hqf hgp (Y m) := by
      simpa [U, Y, p] using hpm
    exact Set.mem_iUnion.mpr ⟨n,
      (Set.mem_iUnion₂.mpr ⟨m, Set.mem_Iio.mpr hm, hym⟩)⟩
  · intro y hy
    -- the single cells cover the component: each y is in some cell of
    -- the covering enumeration Y0, and e is surjective.
    rcases hY0cov y hy with ⟨m, hym⟩
    rcases esurj m with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, by simpa [Y, hn] using hym⟩

end LeanEval.KnotTheory.Quadrisecant
