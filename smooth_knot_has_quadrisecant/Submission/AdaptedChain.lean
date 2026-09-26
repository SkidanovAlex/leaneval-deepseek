import Mathlib
import ChallengeDeps
import Submission.GridPartition
import Submission.TorusPathFollow

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-!
# Layer A (xxi) — the adapted chain of a compact-interval path

`GridPartition.lean` (Layer A (xx)) produced the per-cell charts of the
grid: a number `m` of cells and, for every cell `[pᵢ, pᵢ₊₁]`, a cover
chart whose region contains the whole path over the cell.  This module
assembles the **adapted chain**:

1. **`CellChartData σ`** — the packaged per-cell data: the cell count
   `m`, the chart `cell i` of each cell, and the region fact
   `cellRegion` (the path over cell `i` stays in the region of `cell i`);
   `cellChartData_of` builds it from `perCell_chart` by `classical`
   choice.
2. **the ordered sigma list and the chain** — `adaptedCellCharts`
   (the sigma list of the cell charts in order, via `List.finRange`),
   `adaptedChartChain` (the `ChartChain` from the first cell chart
   through `chainFromList` over the tail).
3. **junction overlap** — `cellBoundaryTime` (the time `pᵢ₊₁` as an
   element of the compact interval) and `junction_cell_overlap`: at every
   junction `pᵢ₊₁` (with `i+1 < m`) the path point lies in the region of
   *both* consecutive cell charts — the right endpoint of cell `i` and the
   left endpoint of cell `i+1`.  This is the local fact behind
   `chartParam_junction_agree` at every junction of the chain.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

namespace LeanEval.KnotTheory.Quadrisecant

/-- **Per-cell chart data of a grid path**: a cell count `m`, a chart for
each cell, and the fact that the whole path over cell `i` stays inside the
region of the cell's chart. -/
structure CellChartData {r : ℝ → Space} {a b : ℝ}
    (σ : CompactInterval a b → ZeroSetPoint r) where
  m : ℕ
  hm : 0 < m
  cell : Fin m → Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p)
  cellRegion : ∀ i : Fin m, ∀ u : CompactInterval a b,
    (u : ℝ) ∈ Set.Icc (gridPoint a b m i.1) (gridPoint a b m (i.1 + 1)) →
      (σ u : KnotParamTriple) ∈ (cell i).2.V

/-- Build the per-cell chart data from the per-cell chart existence
theorem (`classical` choice of a chart for every cell). -/
noncomputable def cellChartData_of {r : ℝ → Space} {a b : ℝ} (hab : a ≤ b)
    (σ : CompactInterval a b → ZeroSetPoint r) (hσ : Continuous σ)
    (cs : List (Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p)))
    (hcover : ∀ u : CompactInterval a b,
      ∃ g : Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p), g ∈ cs ∧
        (σ u : KnotParamTriple) ∈ g.2.V) :
    CellChartData σ :=
  Classical.choice (by
    rcases perCell_chart hab σ hσ cs hcover with ⟨m, hm, hper⟩
    exact ⟨⟨m, hm, (fun i => Classical.choose (hper i.1 i.2)), (by
      intro i u hu
      exact (Classical.choose_spec (hper i.1 i.2)).2 u hu)⟩⟩)

/-- The ordered **sigma list** of the cell charts of the data. -/
noncomputable def adaptedCellCharts {r : ℝ → Space} {a b : ℝ}
    (σ : CompactInterval a b → ZeroSetPoint r) (data : CellChartData σ) :
    List (Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p)) :=
  (List.finRange data.m).map data.cell

/-- The **adapted chart chain**: the chain starting at the chart of the
first cell and following the cell charts in order (through
`chainFromList` over the tail of the sigma list). -/
noncomputable def adaptedChartChain {r : ℝ → Space} {a b : ℝ}
    (σ : CompactInterval a b → ZeroSetPoint r) (data : CellChartData σ) :
    ChartChain (data.cell ⟨0, data.hm⟩).2 :=
  let rest : List (Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p)) :=
    ((List.finRange data.m).tail).map data.cell
  chainFromList (data.cell ⟨0, data.hm⟩).2 rest

/-- The time `pᵢ` of a grid point with `i ≤ m`, as an element of the
compact interval. -/
noncomputable def cellBoundaryTime {a b : ℝ} (hab : a ≤ b) (m : ℕ) (hm : 0 < m)
    (i : ℕ) (hi : i ≤ m) : CompactInterval a b :=
  ⟨gridPoint a b m i,
    ⟨gridPoint_mem_Icc_left hab hm hi, gridPoint_mem_Icc_right hab hm hi⟩⟩

/-- **Junction overlap.**  At every junction time `pᵢ₊₁` (with
`i+1 < m`) the path point lies in the region of *both* consecutive cell
charts: the right endpoint of cell `i` and the left endpoint of cell
`i+1`.  This is the local membership fact behind
`chartParam_junction_agree` at the junctions of the chain. -/
lemma junction_cell_overlap {r : ℝ → Space} {a b : ℝ} (hab : a ≤ b)
    (σ : CompactInterval a b → ZeroSetPoint r) (data : CellChartData σ)
    {i : ℕ} (hi1 : i + 1 < data.m) :
    (σ (cellBoundaryTime hab data.m data.hm (i + 1) (le_of_lt hi1)) : KnotParamTriple) ∈
        (data.cell ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi1⟩).2.V ∧
      (σ (cellBoundaryTime hab data.m data.hm (i + 1) (le_of_lt hi1)) : KnotParamTriple) ∈
        (data.cell ⟨i + 1, hi1⟩).2.V := by
  let u : CompactInterval a b := cellBoundaryTime hab data.m data.hm (i + 1) (le_of_lt hi1)
  constructor
  · -- right endpoint of cell i
    have huR : (u : ℝ) ∈ Set.Icc (gridPoint a b data.m i) (gridPoint a b data.m (i + 1)) := by
      dsimp [u, cellBoundaryTime]
      exact ⟨gridPoint_mono hab (Nat.le_succ i), le_rfl⟩
    have hicell : i < data.m := Nat.lt_trans (Nat.lt_succ_self i) hi1
    exact data.cellRegion ⟨i, hicell⟩ u huR
  · -- left endpoint of cell (i+1)
    have huL : (u : ℝ) ∈ Set.Icc (gridPoint a b data.m (i + 1))
        (gridPoint a b data.m (i + 2)) := by
      dsimp [u, cellBoundaryTime]
      exact ⟨le_rfl, gridPoint_mono hab (Nat.le_succ (i + 1))⟩
    exact data.cellRegion ⟨i + 1, hi1⟩ u huL

/-- The **junction time** `pᵢ₊₁` of the boundary between cell `i` and cell
`i+1`, as an element of the compact interval (used whenever `i + 1 < m`). -/
noncomputable def junctionTime {a b : ℝ} (hab : a ≤ b) (m : ℕ) (hm : 0 < m)
    {i : ℕ} (hi1 : i + 1 < m) : CompactInterval a b :=
  cellBoundaryTime hab m hm (i + 1) (le_of_lt hi1)

/-- **Junction parameter agreement.**  At the junction `pᵢ₊₁` between cell
`i` and cell `i+1` (with `i + 1 < m`), the parameter of the path point
`σ(pᵢ₊₁)` in the next cell's chart is exactly the transition-transport of
its parameter in the current cell's chart — the instantiation of
`chartParam_junction_agree` at this junction, whose two memberships are
supplied by `junction_cell_overlap`. -/
lemma junction_param_agree {r : ℝ → Space} {a b : ℝ} (hab : a ≤ b)
    (σ : CompactInterval a b → ZeroSetPoint r) (data : CellChartData σ)
    {i : ℕ} (hi1 : i + 1 < data.m) :
    ((chartTransitionHomeo (data.cell ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi1⟩).2
        (data.cell ⟨i + 1, hi1⟩).2
        ⟨chartParam (data.cell ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi1⟩).2
            (σ (junctionTime hab data.m data.hm hi1))
            (junction_cell_overlap hab σ data (i := i) hi1).1,
          by
            have hq := chartParam_point (data.cell ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi1⟩).2
              (σ (junctionTime hab data.m data.hm hi1))
              (junction_cell_overlap hab σ data (i := i) hi1).1
            rw [hq]
            exact (junction_cell_overlap hab σ data (i := i) hi1).2⟩ :
          ChartTransitionDomain (data.cell ⟨i + 1, hi1⟩).2 (data.cell ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi1⟩).2) :
        ChartInterval (data.cell ⟨i + 1, hi1⟩).2.lo (data.cell ⟨i + 1, hi1⟩).2.hi) =
      chartParam (data.cell ⟨i + 1, hi1⟩).2 (σ (junctionTime hab data.m data.hm hi1))
        (junction_cell_overlap hab σ data (i := i) hi1).2 := by
  exact chartParam_junction_agree (data.cell ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi1⟩).2
    (data.cell ⟨i + 1, hi1⟩).2 σ (junctionTime hab data.m data.hm hi1)
    (junction_cell_overlap hab σ data (i := i) hi1).1
    (junction_cell_overlap hab σ data (i := i) hi1).2

/-! ## Piecewise parameter lift over the grid

The per-cell chart data gives, on every cell, a single-chart lift of the
path: `cellParam` (the canonical parameter `chartParam (cell i) (σ t)` with
the cell membership), continuous on the cell
(`continuous_cellParam_cell`) and round-tripping
(`cellParam_lift_roundTrip`).  The **single-cell base case**
(`single_cell_grid_lift`, for `m = 1`) is the single-chart lift over the
whole interval; the **grid-lift statement** `GridLift` packages the
per-cell lifts (the junction coherence at the cell boundaries is the
separately-proved `junction_param_agree`, whose two memberships are
supplied by `junction_cell_overlap`); `grid_lift_canonical` realises the
statement by the canonical per-cell lifts. -/

/-- The first grid point is `a`. -/
lemma gridPoint_zero (a b : ℝ) (m : ℕ) : gridPoint a b m 0 = a := by
  dsimp [gridPoint]
  ring

/-- The last grid point is `b`. -/
lemma gridPoint_last {a b : ℝ} {m : ℕ} (hm : 0 < m) : gridPoint a b m m = b := by
  dsimp [gridPoint]
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  field_simp [hmne]
  ring

/-- The **per-cell parameter lift**: at a time `t` of cell `i`, the
parameter of the path point `σ t` in the chart of cell `i`. -/
noncomputable def cellParam {r : ℝ → Space} {a b : ℝ}
    (σ : CompactInterval a b → ZeroSetPoint r) (data : CellChartData σ)
    {i : ℕ} (hicell : i < data.m) (t : CompactInterval a b)
    (ht : (t : ℝ) ∈ Set.Icc (gridPoint a b data.m i) (gridPoint a b data.m (i + 1))) :
    ChartInterval (data.cell ⟨i, hicell⟩).2.lo (data.cell ⟨i, hicell⟩).2.hi :=
  chartParam (data.cell ⟨i, hicell⟩).2 (σ t) (data.cellRegion ⟨i, hicell⟩ t ht)

/-- The per-cell parameter lift round-trips: its chart lift is the path
point. -/
lemma cellParam_lift_roundTrip {r : ℝ → Space} {a b : ℝ}
    (σ : CompactInterval a b → ZeroSetPoint r) (data : CellChartData σ)
    {i : ℕ} (hicell : i < data.m) (t : CompactInterval a b)
    (ht : (t : ℝ) ∈ Set.Icc (gridPoint a b data.m i) (gridPoint a b data.m (i + 1))) :
    chartLift (data.cell ⟨i, hicell⟩).2 (cellParam σ data hicell t ht) = σ t := by
  exact chartParam_lift (data.cell ⟨i, hicell⟩).2 (σ t) (data.cellRegion ⟨i, hicell⟩ t ht)

/-- The per-cell parameter lift is continuous on the cell. -/
lemma continuous_cellParam_cell {r : ℝ → Space} {a b : ℝ}
    (σ : CompactInterval a b → ZeroSetPoint r) (hσ : Continuous σ)
    (data : CellChartData σ) {i : ℕ} (hicell : i < data.m) :
    Continuous (fun t : {t : CompactInterval a b //
        (t : ℝ) ∈ Set.Icc (gridPoint a b data.m i) (gridPoint a b data.m (i + 1))} =>
      cellParam σ data hicell t.1 t.2) := by
  have hσ' : Continuous (fun t : {t : CompactInterval a b //
      (t : ℝ) ∈ Set.Icc (gridPoint a b data.m i) (gridPoint a b data.m (i + 1))} =>
        σ t.1) :=
    hσ.comp continuous_subtype_val
  have hV : ∀ t : {t : CompactInterval a b //
      (t : ℝ) ∈ Set.Icc (gridPoint a b data.m i) (gridPoint a b data.m (i + 1))},
      (σ t.1 : KnotParamTriple) ∈ (data.cell ⟨i, hicell⟩).2.V := by
    intro t
    exact data.cellRegion ⟨i, hicell⟩ t.1 t.2
  have hmain : Continuous (fun t : {t : CompactInterval a b //
      (t : ℝ) ∈ Set.Icc (gridPoint a b data.m i) (gridPoint a b data.m (i + 1))} =>
        chartParam (data.cell ⟨i, hicell⟩).2 (σ t.1) (hV t)) :=
    continuous_chartParam_path (data.cell ⟨i, hicell⟩).2 hσ' hV
  simpa [cellParam] using hmain

/-- **Single-cell base case of the grid lift.**  When the grid has a single
cell (`m = 1`), the whole path lies in the first cell chart's region and
the parameter lift over the whole compact interval exists (continuous and
round-tripping). -/
theorem single_cell_grid_lift {r : ℝ → Space} {a b : ℝ}
    (σ : CompactInterval a b → ZeroSetPoint r) (hσ : Continuous σ)
    (data : CellChartData σ) (hm1 : data.m = 1) :
    ∃ τ : CompactInterval a b → ChartInterval (data.cell ⟨0, data.hm⟩).2.lo
        (data.cell ⟨0, data.hm⟩).2.hi,
      Continuous τ ∧
        ∀ t : CompactInterval a b,
          chartLift (data.cell ⟨0, data.hm⟩).2 (τ t) = σ t := by
  -- with one cell, [a,b] = [p₀,p₁] of the grid
  let hcell : ∀ t : CompactInterval a b,
      (t : ℝ) ∈ Set.Icc (gridPoint a b data.m 0) (gridPoint a b data.m (0 + 1)) := by
    intro t
    have hp0 : gridPoint a b data.m 0 = a := gridPoint_zero a b data.m
    have hp1 : gridPoint a b data.m (0 + 1) = b := by
      rw [hm1]
      exact gridPoint_last (by omega : 0 < (1 : ℕ))
    exact ⟨by rw [hp0]; exact t.2.1, by rw [hp1]; exact t.2.2⟩
  refine ⟨fun t => cellParam σ data data.hm t (hcell t), ?_, ?_⟩
  · -- continuous on the whole interval (the point lies in the chart of
    -- the single cell at every time)
    exact continuous_chartParam_path (data.cell ⟨0, data.hm⟩).2 hσ
      (fun t => data.cellRegion ⟨0, data.hm⟩ t (hcell t))
  · intro t
    exact cellParam_lift_roundTrip σ data data.hm t (hcell t)

/-- **Grid lift (statement).**  A compact-interval path with per-cell chart
data has, on every cell, a continuous parameter lift that round-trips to
the path.  (The junction coherence at the cell boundaries is
`junction_param_agree`, whose two memberships are supplied by
`junction_cell_overlap`.) -/
def GridLift {r : ℝ → Space} {a b : ℝ} (σ : CompactInterval a b → ZeroSetPoint r)
    (data : CellChartData σ) : Prop :=
  ∀ i : Fin data.m,
    ∃ τ : {t : CompactInterval a b //
        (t : ℝ) ∈ Set.Icc (gridPoint a b data.m i.1) (gridPoint a b data.m (i.1 + 1))} →
        ChartInterval (data.cell i).2.lo (data.cell i).2.hi,
      Continuous τ ∧
        ∀ t : {t : CompactInterval a b //
            (t : ℝ) ∈ Set.Icc (gridPoint a b data.m i.1) (gridPoint a b data.m (i.1 + 1))},
          chartLift (data.cell i).2 (τ t) = σ t.1

/-- The canonical per-cell lifts realise the grid lift. -/
theorem grid_lift_canonical {r : ℝ → Space} {a b : ℝ}
    (σ : CompactInterval a b → ZeroSetPoint r) (hσ : Continuous σ)
    (data : CellChartData σ) : GridLift σ data := by
  intro i
  refine ⟨fun t => cellParam σ data i.2 t.1 t.2, ?_, ?_⟩
  · exact continuous_cellParam_cell σ hσ data i.2
  · intro t
    exact cellParam_lift_roundTrip σ data i.2 t.1 t.2


/-- The junction time `pᵢ₊₁` lies in the interval of cell `i` (as its
right endpoint). -/
lemma junctionTime_mem_Icc_left {a b : ℝ} (hab : a ≤ b) {r : ℝ → Space}
    (σ : CompactInterval a b → ZeroSetPoint r) (data : CellChartData σ)
    {i : ℕ} (hi1 : i + 1 < data.m) :
    ((junctionTime hab data.m data.hm hi1 : CompactInterval a b) : ℝ) ∈
      Set.Icc (gridPoint a b data.m i) (gridPoint a b data.m (i + 1)) := by
  dsimp [junctionTime, cellBoundaryTime]
  exact ⟨gridPoint_mono hab (Nat.le_succ i), le_rfl⟩

/-- The junction time `pᵢ₊₁` lies in the interval of cell `i+1` (as its
left endpoint). -/
lemma junctionTime_mem_Icc_right {a b : ℝ} (hab : a ≤ b) {r : ℝ → Space}
    (σ : CompactInterval a b → ZeroSetPoint r) (data : CellChartData σ)
    {i : ℕ} (hi1 : i + 1 < data.m) :
    ((junctionTime hab data.m data.hm hi1 : CompactInterval a b) : ℝ) ∈
      Set.Icc (gridPoint a b data.m (i + 1)) (gridPoint a b data.m (i + 2)) := by
  dsimp [junctionTime, cellBoundaryTime]
  exact ⟨le_rfl, gridPoint_mono hab (Nat.le_succ (i + 1))⟩


/-- The chart point of the cell-`i` parameter of the path at the junction
`pᵢ₊₁` lies in the region of the next cell (`cell i+1`). -/
lemma cellParam_point_mem_next {r : ℝ → Space} {a b : ℝ} (hab : a ≤ b)
    (σ : CompactInterval a b → ZeroSetPoint r) (data : CellChartData σ)
    {i : ℕ} (hi1 : i + 1 < data.m) :
    (((data.cell ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi1⟩).2).homeo
        (cellParam σ data (Nat.lt_trans (Nat.lt_succ_self i) hi1)
          (junctionTime hab data.m data.hm hi1)
          (junctionTime_mem_Icc_left hab σ data hi1)) : KnotParamTriple) ∈
      (data.cell ⟨i + 1, hi1⟩).2.V := by
  -- the chart point of the parameter is σ at the junction (round trip)
  have hval : (((data.cell ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi1⟩).2).homeo
        (cellParam σ data (Nat.lt_trans (Nat.lt_succ_self i) hi1)
          (junctionTime hab data.m data.hm hi1)
          (junctionTime_mem_Icc_left hab σ data hi1)) : KnotParamTriple) =
      (σ (junctionTime hab data.m data.hm hi1) : KnotParamTriple) := by
    simpa [cellParam] using chartParam_point (data.cell ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi1⟩).2
      (σ (junctionTime hab data.m data.hm hi1))
      (data.cellRegion ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi1⟩
        (junctionTime hab data.m data.hm hi1) (junctionTime_mem_Icc_left hab σ data hi1))
  rw [hval]
  exact (junction_cell_overlap hab σ data (i := i) hi1).2

/-- **Canonical junction equality.**  At the junction `pᵢ₊₁`, the two
per-cell parameter lifts agree: the transition-transport of the cell-`i`
parameter of `σ(pᵢ₊₁)` equals the cell-`(i+1)` parameter of `σ(pᵢ₊₁)`.
(Both sides are `chartParam` of the same point in the same next-cell
chart; the memberships are proof-irrelevant.) -/
lemma cellParam_junction {r : ℝ → Space} {a b : ℝ} (hab : a ≤ b)
    (σ : CompactInterval a b → ZeroSetPoint r) (data : CellChartData σ)
    {i : ℕ} (hi1 : i + 1 < data.m) :
    ((chartTransitionHomeo (data.cell ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi1⟩).2
        (data.cell ⟨i + 1, hi1⟩).2
        ⟨cellParam σ data (Nat.lt_trans (Nat.lt_succ_self i) hi1)
            (junctionTime hab data.m data.hm hi1)
            (junctionTime_mem_Icc_left hab σ data hi1),
          cellParam_point_mem_next hab σ data hi1⟩ :
          ChartTransitionDomain (data.cell ⟨i + 1, hi1⟩).2
            (data.cell ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi1⟩).2) :
        ChartInterval (data.cell ⟨i + 1, hi1⟩).2.lo (data.cell ⟨i + 1, hi1⟩).2.hi) =
      cellParam σ data hi1 (junctionTime hab data.m data.hm hi1)
        (junctionTime_mem_Icc_right hab σ data hi1) := by
  unfold cellParam
  simpa using (chartParam_junction_agree (a := a) (b := b)
    (data.cell ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi1⟩).2
    (data.cell ⟨i + 1, hi1⟩).2 σ (junctionTime hab data.m data.hm hi1)
    (junction_cell_overlap hab σ data (i := i) hi1).1
    (junction_cell_overlap hab σ data (i := i) hi1).2)


/-! ## Whole-grid lift: cell selection and junction well-definedness

The candidate whole-grid lift selects, for each time `x ∈ [a,b]`, the cell
whose interval contains `x` (deterministically: the leftmost such cell,
`cellIndexOf`) and applies that cell's per-cell lift.  The function is
**well defined at the cell boundaries** in the sense of
`JunctionCoherent`: at each junction `pᵢ₊₁` the transition-transport of the
left cell's lift value is the right cell's lift value (`cellParam_junction`,
packaged as `junction_coherent`).  Continuity on each open cell is then
inherited from the per-cell lifts, and continuity at a junction follows
from the junction equality. -/

/-- A cell whose interval contains the right part of `x` exists: the last
cell always contains `x` (its right endpoint is `b`). -/
lemma exists_cell_upper {a b : ℝ} {m : ℕ} (hm : 0 < m)
    (x : CompactInterval a b) :
    ∃ j : ℕ, j < m ∧ (x : ℝ) ≤ gridPoint a b m (j + 1) := by
  refine ⟨m - 1, Nat.sub_lt hm (by norm_num), ?_⟩
  -- p_{m-1+1} = p_m = b and x ≤ b
  have hcast : (m - 1) + 1 = m := by omega
  rw [hcast]
  -- (x : ℝ) ≤ b
  have hlast : gridPoint a b m m = b := gridPoint_last hm
  rw [hlast]
  exact x.2.2

/-- The **leftmost cell index** whose interval contains `x` (i.e. the least
`j < m` with `x ≤ p_{j+1}`); the cell selected by the whole-grid lift. -/
noncomputable def cellIndexOf {a b : ℝ} (m : ℕ) (hm : 0 < m)
    (x : CompactInterval a b) : ℕ :=
  Nat.find (exists_cell_upper (m := m) hm x)

/-- The selected cell index is a cell of the grid. -/
lemma cellIndexOf_lt {a b : ℝ} {m : ℕ} (hm : 0 < m) (x : CompactInterval a b) :
    cellIndexOf m hm x < m :=
  (Nat.find_spec (exists_cell_upper (m := m) hm x)).1

/-- The selected cell contains `x` on its right: `x ≤ p_{i+1}`. -/
lemma cellIndexOf_le_right {a b : ℝ} {m : ℕ} (hm : 0 < m) (x : CompactInterval a b) :
    (x : ℝ) ≤ gridPoint a b m (cellIndexOf m hm x + 1) :=
  (Nat.find_spec (exists_cell_upper (m := m) hm x)).2

/-- **Junction well-definedness (statement).**  At every junction `pᵢ₊₁`
the transition-transport of the left cell's per-cell lift value equals the
right cell's per-cell lift value: the two ways of reading the whole-grid
lift at a boundary agree (via `cellParam_junction`). -/
def JunctionCoherent {r : ℝ → Space} {a b : ℝ} (hab : a ≤ b)
    (σ : CompactInterval a b → ZeroSetPoint r) (data : CellChartData σ) : Prop :=
  ∀ {i : ℕ} (hi1 : i + 1 < data.m),
    ((chartTransitionHomeo (data.cell ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi1⟩).2
        (data.cell ⟨i + 1, hi1⟩).2
        ⟨cellParam σ data (Nat.lt_trans (Nat.lt_succ_self i) hi1)
            (junctionTime hab data.m data.hm hi1)
            (junctionTime_mem_Icc_left hab σ data hi1),
          cellParam_point_mem_next hab σ data hi1⟩ :
          ChartTransitionDomain (data.cell ⟨i + 1, hi1⟩).2
            (data.cell ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi1⟩).2) :
        ChartInterval (data.cell ⟨i + 1, hi1⟩).2.lo (data.cell ⟨i + 1, hi1⟩).2.hi) =
      cellParam σ data hi1 (junctionTime hab data.m data.hm hi1)
        (junctionTime_mem_Icc_right hab σ data hi1)

/-- The whole-grid lift is well defined at every junction
(`cellParam_junction` packaged). -/
theorem junction_coherent {r : ℝ → Space} {a b : ℝ} (hab : a ≤ b)
    (σ : CompactInterval a b → ZeroSetPoint r) (data : CellChartData σ) :
    JunctionCoherent hab σ data := by
  intro i hi1
  exact cellParam_junction hab σ data hi1


/-- The selected cell contains `x` on its left: `pᵢ ≤ x`, where
`i = cellIndexOf`.  (From the minimality of `cellIndexOf`: no cell to the
left of `i` reaches `x`, and `p₀ = a ≤ x` in the base case.)  Together
with `cellIndexOf_le_right`, the selected cell is a genuine containing
cell of `x`. -/
lemma cellIndexOf_ge_left {a b : ℝ} {m : ℕ} (hm : 0 < m) (x : CompactInterval a b) :
    gridPoint a b m (cellIndexOf m hm x) ≤ (x : ℝ) := by
  classical
  let i : ℕ := cellIndexOf m hm x
  have hi : i < m := by simpa [i] using cellIndexOf_lt hm x
  by_cases hi0 : i = 0
  · -- i = 0: p₀ = a ≤ x
    have h0 : cellIndexOf m hm x = 0 := by simpa [i] using hi0
    rw [h0, gridPoint_zero]
    exact x.2.1
  · -- i > 0: no cell to the left of i reaches x (minimality of the find)
    have hpos : 0 < i := Nat.pos_of_ne_zero hi0
    have hnot : ¬ ((x : ℝ) ≤ gridPoint a b m i) := by
      intro hle
      -- j := i - 1 satisfies the cell predicate: j < m and x ≤ p_{j+1} = pᵢ
      have hj : (i - 1) < m ∧ (x : ℝ) ≤ gridPoint a b m ((i - 1) + 1) := by
        constructor
        · omega
        · have hcast : (i - 1) + 1 = i := by omega
          rw [hcast]
          exact hle
      have hlt : i - 1 < cellIndexOf m hm x := by
        change i - 1 < i
        exact Nat.sub_lt hpos (by omega)
      exact (Nat.find_min (exists_cell_upper (m := m) hm x) hlt) hj
    exact (le_total (x : ℝ) (gridPoint a b m i)).resolve_left hnot


/-- The **certified cell membership** of `x` in the selected cell: the
selected cell `i = cellIndexOf` satisfies `pᵢ ≤ x ≤ pᵢ₊₁` (left bound
`cellIndexOf_ge_left`, right bound `cellIndexOf_le_right`). -/
lemma cellIndexOf_mem {a b : ℝ} {m : ℕ} (hm : 0 < m) (x : CompactInterval a b) :
    (x : ℝ) ∈ Set.Icc (gridPoint a b m (cellIndexOf m hm x))
      (gridPoint a b m (cellIndexOf m hm x + 1)) :=
  ⟨cellIndexOf_ge_left hm x, cellIndexOf_le_right hm x⟩

/-- **The whole-grid lift (value, as a real).**  At a time `x ∈ [a,b]` the
selected cell's parameter of the path point `σ x`, read as a real number.
The function is defined on all of the compact interval by the certified
cell membership; it is `ℝ`-valued because the per-cell parameters live in
different chart intervals (the per-cell charts are glued at the junctions
by the transition maps — the real values agree at a junction, see
`cellParam_junction`). -/
noncomputable def wholeGridParam {r : ℝ → Space} {a b : ℝ}
    (σ : CompactInterval a b → ZeroSetPoint r) (data : CellChartData σ)
    (x : CompactInterval a b) : ℝ :=
  (cellParam σ data (cellIndexOf_lt data.hm x) x (cellIndexOf_mem data.hm x) : ℝ)


/-! ## Continuity of the whole-grid lift on the open cells

On the *interior* of a cell the cell selector is constant:
`cellIndexOf_of_Ioo` shows that on the open cell `(pᵢ, pᵢ₊₁)` the selected
cell is `i` (minimality: no cell to the left of `i` reaches `x`, and `i`
itself does).  Consequently `wholeGridParam` coincides there with the
per-cell lift `cellParam` of cell `i`
(`wholeGridParam_val_eq_cellParam`), whose continuity is already
established; restricting the closed-cell continuity lemma to the open cell
gives `continuous_wholeGridParam_on_open_cell`. -/

/-- On the interior of cell `i`, the selected cell is `i` itself. -/
lemma cellIndexOf_of_Ioo {a b : ℝ} (hab : a ≤ b) {m : ℕ} (hm : 0 < m)
    {i : ℕ} (hicell : i < m) (x : CompactInterval a b)
    (hx : (x : ℝ) ∈ Set.Ioo (gridPoint a b m i) (gridPoint a b m (i + 1))) :
    cellIndexOf m hm x = i := by
  apply le_antisymm
  · -- i satisfies the cell predicate, so the found minimum is ≤ i
    apply Nat.find_min'
    exact ⟨hicell, le_of_lt hx.2⟩
  · -- no cell to the left of i reaches x (p_{j+1} ≤ pᵢ < x)
    apply le_of_not_gt
    intro hfi -- find < i
    have hno : ∀ j : ℕ, j < i → ¬ ((x : ℝ) ≤ gridPoint a b m (j + 1)) := by
      intro j hj hle
      have hji : j + 1 ≤ i := by omega
      have hmj : gridPoint a b m (j + 1) ≤ gridPoint a b m i := gridPoint_mono hab hji
      have hp : gridPoint a b m (j + 1) < x := lt_of_le_of_lt hmj hx.1
      exact (not_lt_of_ge hle) hp
    exact (hno (cellIndexOf m hm x) hfi) (cellIndexOf_le_right hm x)

/-- Applying the cell chart at the same index with different index proofs
gives the same chart. -/
lemma cell_eq_of_fin_eq {r : ℝ → Space} {a b : ℝ} {σ : CompactInterval a b → ZeroSetPoint r}
    (data : CellChartData σ) {i : ℕ} {h₁ h₂ : i < data.m} :
    data.cell ⟨i, h₁⟩ = data.cell ⟨i, h₂⟩ := by
  congr 1

/-- Comparing `chartParam` real values for the same point in equal bundled
charts: the bundled charts are equal (the base points and chart data
coincide), so the real parameter values agree (the two memberships of the
point in the two charts are proofs of the same proposition after the
substitution, hence irrelevant). -/
lemma chartParam_val_eq_of_sigma_eq {r : ℝ → Space}
    {c₁ c₂ : Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p)}
    (hc : c₁ = c₂) (z : ZeroSetPoint r)
    (hV₁ : (z : KnotParamTriple) ∈ c₁.2.V) (hV₂ : (z : KnotParamTriple) ∈ c₂.2.V) :
    (chartParam c₁.2 z hV₁ : ℝ) = (chartParam c₂.2 z hV₂ : ℝ) := by
  subst c₁
  unfold chartParam
  have hpt : (⟨(z : KnotParamTriple), ⟨z.2, hV₁⟩⟩ :
        {q : KnotParamTriple // q ∈ trisecantZeroSet r ∧ q ∈ c₂.2.V}) =
      ⟨(z : KnotParamTriple), ⟨z.2, hV₂⟩⟩ := by
    apply Subtype.ext
    rfl
  rw [hpt]

/-- The real value of the per-cell parameter lift is insensitive to which
index proof is used for the cell — indeed to which *equal* index: at the
same time `x` and the same path point, all per-cell lifts over equal cell
indices have the same real parameter value. -/
lemma cellParam_val_eq_of_nat_index {r : ℝ → Space} {a b : ℝ}
    (σ : CompactInterval a b → ZeroSetPoint r) (data : CellChartData σ)
    (x : CompactInterval a b) (i j : ℕ) (hij : i = j)
    (hicell : i < data.m) (hjcell : j < data.m)
    (hti : (x : ℝ) ∈ Set.Icc (gridPoint a b data.m i) (gridPoint a b data.m (i + 1)))
    (htj : (x : ℝ) ∈ Set.Icc (gridPoint a b data.m j) (gridPoint a b data.m (j + 1))) :
    (cellParam σ data hicell x hti : ℝ) = (cellParam σ data hjcell x htj : ℝ) := by
  subst j
  unfold cellParam
  exact chartParam_val_eq_of_sigma_eq (cell_eq_of_fin_eq data) (σ x)
    (data.cellRegion ⟨i, hicell⟩ x hti) (data.cellRegion ⟨i, hjcell⟩ x htj)

/-- On the interior of cell `i` the whole-grid lift value equals the
per-cell lift of cell `i` (as real parameter values). -/
lemma wholeGridParam_val_eq_cellParam {r : ℝ → Space} {a b : ℝ} (hab : a ≤ b)
    (σ : CompactInterval a b → ZeroSetPoint r) (data : CellChartData σ)
    {i : ℕ} (hicell : i < data.m) (x : CompactInterval a b)
    (hx : (x : ℝ) ∈ Set.Ioo (gridPoint a b data.m i) (gridPoint a b data.m (i + 1))) :
    wholeGridParam σ data x =
      (cellParam σ data hicell x (⟨le_of_lt hx.1, le_of_lt hx.2⟩ : _) : ℝ) := by
  have hsel := cellIndexOf_of_Ioo hab data.hm hicell x hx
  unfold wholeGridParam
  exact cellParam_val_eq_of_nat_index σ data x (cellIndexOf data.m data.hm x) i hsel
    (cellIndexOf_lt data.hm x) hicell (cellIndexOf_mem data.hm x) ⟨le_of_lt hx.1, le_of_lt hx.2⟩

/-- **Continuity of the whole-grid lift on an open cell.**  On the
interior of cell `i` the whole-grid lift coincides with the (continuous)
per-cell lift of cell `i`, so it is continuous there. -/
lemma continuous_wholeGridParam_on_open_cell {r : ℝ → Space} {a b : ℝ} (hab : a ≤ b)
    (σ : CompactInterval a b → ZeroSetPoint r) (hσ : Continuous σ)
    (data : CellChartData σ) {i : ℕ} (hicell : i < data.m) :
    Continuous (fun x : {x : CompactInterval a b //
        (x : ℝ) ∈ Set.Ioo (gridPoint a b data.m i) (gridPoint a b data.m (i + 1))} =>
      wholeGridParam σ data x.1) := by
  -- the map on the closed cell: the per-cell lift of cell i
  let D : Type := {t : CompactInterval a b //
    (t : ℝ) ∈ Set.Icc (gridPoint a b data.m i) (gridPoint a b data.m (i + 1))}
  have hclosed : Continuous (fun t : D => (cellParam σ data hicell t.1 t.2 : ℝ)) := by
    have hc := continuous_cellParam_cell σ hσ data hicell
    exact continuous_subtype_val.comp hc
  -- the inclusion of the open cell into the closed cell
  let inc : {t : CompactInterval a b //
      (t : ℝ) ∈ Set.Ioo (gridPoint a b data.m i) (gridPoint a b data.m (i + 1))} → D :=
    fun t => ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩
  have hinc : Continuous inc := by
    rw [continuous_def]
    intro U hUo
    rw [isOpen_induced_iff] at hUo
    rcases hUo with ⟨W, hWo, hUW⟩
    have hpre : inc ⁻¹' U =
        (fun t : {t : CompactInterval a b //
            (t : ℝ) ∈ Set.Ioo (gridPoint a b data.m i) (gridPoint a b data.m (i + 1))} =>
              (t.1 : CompactInterval a b)) ⁻¹' W := by
      ext t
      rw [← hUW]
      rfl
    rw [hpre]
    exact IsOpen.preimage continuous_subtype_val hWo
  -- the desired map equals hclosed ∘ inc (pointwise by the value lemma)
  have hmain : Continuous (fun x : {x : CompactInterval a b //
        (x : ℝ) ∈ Set.Ioo (gridPoint a b data.m i) (gridPoint a b data.m (i + 1))} =>
      wholeGridParam σ data x.1) := by
    have hc := (hclosed.comp hinc)
    exact hc.congr (fun x => by
      dsimp [inc]
      exact (wholeGridParam_val_eq_cellParam hab σ data hicell x.1 x.2).symm)
  exact hmain
