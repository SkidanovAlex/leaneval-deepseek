import Mathlib
import Submission.Work.PL.Defs

/-!
# `cubeChart_isCompact_image_closedCube`

A `PL.CubeChart n M` is an open embedding of the open unit cube of `ℝⁿ = PL.E n` into `M`.
Only its values on `PL.openCube 1` are meaningful, so the image of a closed sub-cube
`PL.closedCube r` (with `r < 1`) is a compact subset of `M`: the closed cube is compact in
`ℝⁿ` (a product of closed intervals, transported across `PiLp.homeomorph`), and the chart is
continuous on the open cube which contains it.
-/

open Set Metric

namespace Work.Cells.Connell

/-- The closed sup-norm cube `PL.closedCube r` of `PL.E n = ℝⁿ` is compact.  It is the
preimage of the product of the closed intervals `[-r, r]` under the (homeomorphic) identity
comparison map `PiLp.homeomorph` between `PL.E n = PiLp 2 (Fin n → ℝ)` and `Fin n → ℝ`. -/
theorem isCompact_closedCube (n : ℕ) (r : ℝ) : IsCompact (PL.closedCube (n := n) r) := by
  have h : PL.closedCube (n := n) r
      = (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)) ⁻¹'
          (Set.pi univ (fun _ : Fin n => Icc (-r) r)) := by
    ext x
    simp only [mem_preimage, PL.closedCube, mem_ofPred_eq, Set.mem_pi, mem_univ, true_implies,
      mem_Icc, abs_le]
    constructor
    · intro hx i; exact hx i
    · intro hx i; exact hx i
  rw [h]
  exact (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi fun _ => isCompact_Icc)

/-- The image of a closed sub-cube `PL.closedCube r`, `r < 1`, under a cube chart is compact:
`PL.closedCube r ⊆ PL.openCube 1`, so `c.toFun` is continuous there. -/
theorem cubeChart_isCompact_image_closedCube {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : PL.CubeChart n M) {r : ℝ} (hr : r < 1) : IsCompact (c.toFun '' PL.closedCube r) := by
  have hsub : PL.closedCube (n := n) r ⊆ PL.openCube (n := n) 1 :=
    fun x hx i => lt_of_le_of_lt (hx i) hr
  exact (isCompact_closedCube n r).image_of_continuousOn (c.cont.mono hsub)

end Work.Cells.Connell
