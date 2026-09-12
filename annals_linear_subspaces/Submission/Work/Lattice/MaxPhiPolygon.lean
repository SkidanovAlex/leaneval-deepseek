import Mathlib
import Submission.Work.Lattice.MaxPhi
import Submission.Work.Lattice.MaxRankData
import Submission.Work.Lattice.PhiPolygon

/-!
# The max-norm Grayson polygon of the slacked data, and the flag layer (definitions)

The max-norm analogue of `PhiPolygon`/`PhiFlag`: the slacked max-norm data
`maxphiData Λ A j = maxRankData Λ j + A·j·(d−j)` and its largest convex minorant
`maxphiPolygon Λ A`.

This module contains the definitions and the two basic facts
(`maxphiPolygon_le_data`, `maxphiPolygon_convex`).  The remaining steps of the flag argument
(`maxphiPolygon_le_maxPhi` — needs `BddBelow (maxRankDataSet Λ (subDim X))`, which holds for the
§3 lattice via `CnormDataBdd.bddBelow_flowMaxDataSet_imageSpan` and
`MaxRankData.flowMaxDataSet_eq_maxRankDataSet`; `maxphiPolygon_eq_data_at_angular`;
`exists_saturated_tight_at_angular`; and the replay of `PhiFlag.exists_tight_flag`) are recorded in
the roadmap.

Module `Submission.Work.Lattice.MaxPhiPolygon`, namespace `Submission.MaxPhiPolygon`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Submission.MaxPhiPolygon

open Submission.GraysonLattice
open Submission.GraysonData
open Submission.Polygon
open Submission.MaxRankData
open Submission.MaxPhi
open Submission.MaxCovol
open Submission.LatticePolygon

variable {d : ℕ}

/-- The **slacked max-norm rank data** of a lattice `Λ`. -/
noncomputable def maxphiData (Λ : Submodule ℤ (E d)) (A : ℝ) (j : ℕ) : ℝ :=
  (if h : j ≤ d then maxRankData Λ j h else 0) + A * ((j : ℝ) * ((d : ℝ) - (j : ℝ)))

/-- The **max-norm `φ_A`-Grayson polygon** of `Λ`: the largest convex minorant of the slacked
max-norm data. -/
noncomputable def maxphiPolygon (Λ : Submodule ℤ (E d)) (A : ℝ) (i : ℕ) : ℝ :=
  largestConvexMinorant (Module.finrank ℤ Λ) (maxphiData Λ A) i

/-- The polygon lies below the slacked data. -/
lemma maxphiPolygon_le_data (Λ : Submodule ℤ (E d)) (A : ℝ) {j : ℕ}
    (hj : j ≤ Module.finrank ℤ Λ) : maxphiPolygon Λ A j ≤ maxphiData Λ A j :=
  largestConvexMinorant_le_g (Module.finrank ℤ Λ) (maxphiData Λ A) hj

/-- The slacked polygon is discrete-convex. -/
lemma maxphiPolygon_convex (Λ : Submodule ℤ (E d)) (A : ℝ) :
    DiscreteConvexOn (maxphiPolygon Λ A) (Module.finrank ℤ Λ) :=
  largestConvexMinorant_convex (Module.finrank ℤ Λ) (maxphiData Λ A)

/-- **The max-norm polygon lies below the max-norm value.**  (Requires the max-norm data of `Λ`
at rank `subDim X` to be bounded below, which holds for the §3 lattice via
`CnormDataBdd.bddBelow_flowMaxDataSet_imageSpan`.) -/
theorem maxphiPolygon_le_maxPhi {Λ X : Submodule ℤ (E d)} [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (A : ℝ) (hXΛ : X ≤ Λ)
    (hBdd : BddBelow (maxRankDataSet (d := d) Λ (subDim X) (subDim_le_ambient X))) :
    maxphiPolygon (d := d) Λ A (subDim X) ≤ maxPhi (d := d) Λ hΛfin A X hXΛ := by
  have hjd : subDim X ≤ Module.finrank ℤ Λ := by rw [hΛfin]; exact subDim_le_ambient X
  have hle := maxphiPolygon_le_data (d := d) Λ A hjd
  have hdat : maxphiData (d := d) Λ A (subDim X) =
      maxRankData (d := d) Λ (subDim X) (subDim_le_ambient X) +
        A * ((subDim X : ℝ) * ((d : ℝ) - (subDim X : ℝ))) := by
    rw [maxphiData, dif_pos (subDim_le_ambient X)]
  rw [hdat] at hle
  have hcov : maxRankData (d := d) Λ (subDim X) (subDim_le_ambient X) ≤
      maxCovol (d := d) Λ hΛfin X hXΛ := by
    rw [maxCovol]
    by_cases h : X = ⊥
    · have hsub : subDim X = 0 := by
        rw [h]
        exact (subDim_eq_zero_iff_bot ⊥).mpr rfl
      rw [dif_pos h, maxRankData_eq_zero (subDim_le_ambient X) hsub]
    · rw [dif_neg h]
      refine csInf_le hBdd ⟨presFam (d := d) Λ hΛfin X hXΛ h, ?_, ?_, rfl⟩
      · intro i
        exact presFam_mem (d := d) (Λ := Λ) (hΛfin := hΛfin) (X := X) (hXΛ := hXΛ) (hX0 := h) i
      · exact presFam_linearIndependent (d := d) (Λ := Λ) (hΛfin := hΛfin) (X := X)
          (hXΛ := hXΛ) (hX0 := h)
  rw [maxPhi]
  linarith

end Submission.MaxPhiPolygon

end
