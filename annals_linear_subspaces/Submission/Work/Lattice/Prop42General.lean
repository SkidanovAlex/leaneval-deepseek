import Mathlib
import Submission.Work.Lattice.LatticePolygon
import Submission.Work.Lattice.GraysonLattice
import Submission.Commons.Lattice.SuccessiveMinima.Basic

/-!
# P2/P3-general (b), step 2a: Prop-4(2) LOWER bound in the general vocabulary

The LOWER half of paper Prop 4(2) is an exact inequality valid for **any** full-rank
lattice `Λ ≤ ℝᵈ` whose per-rank Grayson data is bounded below: for every `1 ≤ j ≤ d`,

    `polygon Λ j ≤ Σ_{i : Fin j} log λ_{i.val+1}(Λ)`.

It is the composition of the two general pieces of the P1-general layer:
- **polygon below the data** (`LatticePolygon.polygon_le_covol`: for every subgroup
  `W ≤ Λ` of real rank `subDim W`, `polygon Λ (subDim W) ≤ log covol(W)` — the Grayson
  axiom `c ≤ φ`, needing only `BddBelow (rankDataSet Λ (subDim W))`), and
- **the block-structure lemma** (`GraysonLattice.convex_belowData_le_sum_log`: a function
  `c` lying below the data at every subgroup satisfies `c(j) ≤ Σ_{i≤j} log λᵢ(Λ)`, by
  evaluating on the rank-`j` realiser span `Wⱼ` whose covolume is
  `≤ ∏_{i≤j} λᵢ(Λ)` — `realiserSpan_covol_le_prod`).

The boundedness hypothesis `hbdd` is discharged per lattice; for the model exponential
flow lattice it follows from the model data lower bounds (see the companion module for
the flow instance).  All declarations are Mathlib + Submission (LatticePolygon/
GraysonLattice) + Commons.
-/

noncomputable section

open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Submission.Prop42General

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.LatticePolygon
open Commons.Lattice.SuccessiveMinima

/-- **Prop-4(2) lower bound, general form**: for a full-rank lattice `Λ ≤ ℝᵈ` whose
per-rank Grayson data is bounded below (`BddBelow (rankDataSet Λ r)` for every
`r ≤ d`), the Grayson polygon lies below the log-successive-minimum prefix sum:
`polygon Λ j ≤ Σ_{i : Fin j} log λ_{i.val+1}(Λ)` for every `1 ≤ j ≤ d`. -/
theorem polygon_le_sum_log_general {d j : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    (hbdd : ∀ r : ℕ, r ≤ d → BddBelow (rankDataSet Λ r))
    (hj1 : 1 ≤ j) (hjd : j ≤ d) :
    polygon Λ j ≤ ∑ i : Fin j, Real.log (successiveMinimum Λ (i.val + 1)) := by
  classical
  refine convex_belowData_le_sum_log (d := d) Λ hΛfin hj1 hjd (polygon Λ) ?_
  intro W hWle
  refine polygon_le_covol Λ hWle ?_ ?_
  · -- subDim W ≤ finrank ℤ Λ
    have hle : subDim W ≤ d := subDim_le_ambient W
    simpa [hΛfin] using hle
  · -- BddBelow (rankDataSet Λ (subDim W))
    exact hbdd (subDim W) (by simpa [hΛfin] using subDim_le_ambient W)

end Submission.Prop42General

end
