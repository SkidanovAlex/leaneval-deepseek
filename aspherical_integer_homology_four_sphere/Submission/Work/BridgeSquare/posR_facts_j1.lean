/-
# `BridgeSquare/posR_facts_j1.lean` — the geometric data of the `κ_{v,3}` fibre loops

The `B`-case analogue of `BridgeSquare/FibreGeomDataA.lean` (`fibreLen v 0`): for every cusp `v`
and every unit edge `k < fibreLen v 1` of the `κ_{v,3}`-loop, the two polytope points
`posR (edgeW0Face v 1 k)`, `posR (edgeW1Face v 1 k)` are the images under the ceiling chart of the
two ends of the cube edge `edgeCube v 1 k`, and `posR (edgeFace v 1 k)` is their midpoint.

All facts are verified on the generated tables (`qPos`, `cubeXToKlein`, `cubeXToKleinb`,
`cubeCorner`, `edgeCube`, `edgeW0Face`, `edgeW1Face`, `edgeFace`) by finite case analysis.
-/
import Mathlib
import Submission.Work.BridgeSquare.fibreSteps

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

open Work.BridgeSquare Work.MbarHomology
open Convexity

namespace Work.BridgeSquare

noncomputable section

theorem posR_facts_j1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < Work.BridgeSquare.fibreLen v 1) :
    (∀ i : Fin 4,
      (Work.ConvexCells.PolytopeData.posR Work.MbarHomology.QbarPD
          (Work.BridgeSquare.edgeW0Face v 1 k)) i =
        (Work.RTOwed.kleinPt (Work.BridgeSquare.edgeCube v 1 k)
          (WithLp.toLp 2 (fun j : Fin 3 =>
            (Work.Cusp.cubeCorner (Work.BridgeSquare.edgeCube v 1 k) j : ℝ)))) i)
    ∧ (∀ i : Fin 4,
      (Work.ConvexCells.PolytopeData.posR Work.MbarHomology.QbarPD
          (Work.BridgeSquare.edgeW1Face v 1 k)) i =
        (Work.RTOwed.kleinPt (Work.BridgeSquare.edgeCube v 1 k)
          (WithLp.toLp 2 (fun j : Fin 3 =>
            (Work.Cusp.cubeCorner (Work.BridgeSquare.edgeCube v 1 k) j : ℝ)
              + (if j = Work.BridgeSquare.fibreDir v 1 then 1 else 0)))) i)
    ∧ (2 : ℝ) • Work.ConvexCells.PolytopeData.posR Work.MbarHomology.QbarPD
          (Work.BridgeSquare.edgeFace v 1 k) =
        Work.ConvexCells.PolytopeData.posR Work.MbarHomology.QbarPD
          (Work.BridgeSquare.edgeW0Face v 1 k)
        + Work.ConvexCells.PolytopeData.posR Work.MbarHomology.QbarPD
          (Work.BridgeSquare.edgeW1Face v 1 k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases v <;> fin_cases k <;>
      first
        | (exfalso; revert hk; decide)
        | (fin_cases i <;>
            simp only [Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
              Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
              Work.Cusp.cubeCorner, Work.MbarHomology.qPos, Work.MbarHomology.QbarPD,
              Work.BridgeSquare.edgeW0Face, Work.BridgeSquare.edgeCube,
              Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.head_val',
              Matrix.tail_val', Fin.isValue, Fin.reduceFinMk, ↓reduceIte] <;>
            norm_num)
  · intro i
    fin_cases v <;> fin_cases k <;>
      first
        | (exfalso; revert hk; decide)
        | (fin_cases i <;>
            simp only [Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
              Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
              Work.Cusp.cubeCorner, Work.MbarHomology.qPos, Work.MbarHomology.QbarPD,
              Work.BridgeSquare.edgeW1Face, Work.BridgeSquare.edgeCube,
              Work.BridgeSquare.fibreDir, Work.BridgeSquare.dirKappa,
              Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.head_val',
              Matrix.tail_val', Fin.isValue, Fin.reduceFinMk, ↓reduceIte] <;>
            norm_num)
  · apply PiLp.ext
    intro i
    fin_cases v <;> fin_cases k <;>
      first
        | (exfalso; revert hk; decide)
        | (fin_cases i <;>
            simp only [Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
              Work.MbarHomology.qPos, Work.MbarHomology.QbarPD, Work.BridgeSquare.edgeFace,
              Work.BridgeSquare.edgeW0Face, Work.BridgeSquare.edgeW1Face,
              PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.isValue, Fin.reduceFinMk,
              ↓reduceIte] <;>
            norm_num)

end

end Work.BridgeSquare
