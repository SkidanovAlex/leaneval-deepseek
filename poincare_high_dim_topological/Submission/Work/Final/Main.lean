import Mathlib
import Submission.Work.Final.Assumptions
import Submission.Work.Compact.UnivPoly
import Submission.Work.Metric.Euclidean
import Submission.Work.Metric.PLCells
import Submission.Work.Metric.locCube_chartedSpace
import Submission.Work.Conn.ExtForm
import Submission.Work.Cells.Connell.Main
import Submission.Work.Brown.Criterion
import Submission.Work.Endgame.Main
import Submission.Work.Geo.Radial.ForConnell

/-!
# `Work.Final`: the final assembly of `poincare_high_dim_topological`

The end-to-end theorem, modulo the single holder `Work.Final.FinalInputs n`:

* `Work.Final.poincare_high_dim_topological_of_inputs` — the challenge theorem with an extra
  argument `I : FinalInputs n` carrying Newman's engulfing theorem (`E0`).

The chain (each step a delivered theorem of another area):

1. `Work.Compact.compactSpace_of_homotopyEquiv_sphere_univ` — `M` is compact (any universe);
2. `Work.Metric.metricOfCompactEuclideanSpace` — a compatible metric;
3. `Work.Metric.locCube_chartedSpace`, `Work.Metric.cellCover_exists` — `PL.LocCube` and a
   finite cover by open `n`-cells;
4. `Work.Conn.extOverDisc_of_homotopyEquiv_sphere` — `PL.ExtOverDisc M j` for `j < n`;
5. `Work.Final.assumptionsOfInputs` — the bundle for the Connell area;
6. `Work.Cells.Connell.nonempty_homeomorph_sphere_of_exists_cellCover` — the cell-count descent
   (`connell_step` iterated to two cells, `two_cells_sphere`, Brown's criterion) and the Endgame.
-/

open Metric (sphere)
open ContinuousMap

namespace Work.Final

universe u

set_option linter.style.haveILetI false in
/-- **The generalized topological Poincaré conjecture in dimensions `≥ 5`** (Smale 1961;
topological case Newman 1966 / Connell 1967), *modulo* Newman's engulfing theorem
(`Work.Final.FinalInputs`). -/
theorem poincare_high_dim_topological_of_inputs {n : ℕ} (h5 : 5 ≤ n)
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (h : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (I : FinalInputs.{u} n) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  -- 1. `M` is compact (from the homotopy equivalence to the sphere).
  haveI : CompactSpace M :=
    Work.Compact.compactSpace_of_homotopyEquiv_sphere_univ n (by omega) h
  -- 2. a metric compatible with the topology, and the local cube charts.
  letI : MetricSpace M := Work.Metric.metricOfCompactEuclideanSpace n M
  have hloc : PL.LocCube n M := Work.Metric.locCube_chartedSpace n M
  -- 3. a finite cover by open `n`-cells.
  have hcell : ∃ k, PL.CellCover n M k := Work.Metric.cellCover_exists n M
  -- 4. the connectivity of `M`.
  have hconn : ∀ j, j + 1 ≤ n → PL.ExtOverDisc M j := by
    intro j hj
    exact Work.Conn.extOverDisc_of_homotopyEquiv_sphere (n := n) (j := j) (by omega) h
  -- 5. Brown's criterion, the radial expansion and the extension of compactly supported
  --    homeomorphisms.
  have hbrown : Work.Cells.Connell.BrownCriterionAt n M := Work.Brown.brownCriterion n
  have hrad : Work.Cells.Connell.RadialExpandForm n := Work.Geo.Radial.radialExpandForm n
  have hext : Work.Cells.Connell.ExtHomeoForm.{u} n := Work.Geo.Radial.extHomeoForm n
  -- `M` is nonempty (it is homotopy equivalent to the nonempty sphere).
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin (n + 1))))
    (r := 1)).mpr zero_le_one
  have hne : Nonempty M := ⟨h.invFun (Subtype.mk x hx)⟩
  -- 6. Connell's cell-count reduction and the Endgame.
  exact Work.Cells.Connell.nonempty_homeomorph_sphere_of_exists_cellCover h5
    (assumptionsOfInputs I M) hloc hconn hbrown hrad hext hne hcell

/-- **The penultimate step of the assembly**: the same hypotheses produce a point `q` of `M` whose
complement is homeomorphic to `ℝⁿ` (this is where Connell's cell-count reduction, the two-cell step
and Brown's criterion land, before the one-point compactification of `Work.Endgame`). -/
theorem exists_compl_homeomorph_of_inputs {n : ℕ} (h5 : 5 ≤ n)
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (h : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (I : FinalInputs.{u} n) :
    ∃ q : M, Nonempty (↥({q}ᶜ : Set M) ≃ₜ PL.E n) := by
  haveI : CompactSpace M :=
    Work.Compact.compactSpace_of_homotopyEquiv_sphere_univ n (by omega) h
  letI : MetricSpace M := Work.Metric.metricOfCompactEuclideanSpace n M
  have hloc : PL.LocCube n M := Work.Metric.locCube_chartedSpace n M
  have hcell : ∃ k, PL.CellCover n M k := Work.Metric.cellCover_exists n M
  have hconn : ∀ j, j + 1 ≤ n → PL.ExtOverDisc M j := by
    intro j hj
    exact Work.Conn.extOverDisc_of_homotopyEquiv_sphere (n := n) (j := j) (by omega) h
  have hbrown : Work.Cells.Connell.BrownCriterionAt n M := Work.Brown.brownCriterion n
  have hrad : Work.Cells.Connell.RadialExpandForm n := Work.Geo.Radial.radialExpandForm n
  have hext : Work.Cells.Connell.ExtHomeoForm.{u} n := Work.Geo.Radial.extHomeoForm n
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin (n + 1))))
    (r := 1)).mpr zero_le_one
  have hne : Nonempty M := ⟨h.invFun (Subtype.mk x hx)⟩
  exact Work.Cells.Connell.exists_compl_homeomorph_of_exists_cellCover h5
    (assumptionsOfInputs I M) hloc hconn hbrown hrad hext hne hcell

end Work.Final
