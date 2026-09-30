/-
# `BridgeSquare/FibreGeomDataA.lean` — the geometric data of the `κ_{v,2}` fibre loops

For the `A`-case of the fibre identities we need, for every cusp `v` and every unit edge
`k < fibreLen v 0` of the `κ_{v,2}`-loop, the cube `edgeCube v 0 k` carrying that edge, and the
*numeric* facts (checked on the generated tables `qPos`, `qInc`, `moRoot`, `moRootC`,
`cubeXToKlein`) that the two polytope vertices `edgeW0Face v 0 k`, `edgeW1Face v 0 k` are the
images of the two ends of the cube edge under the ceiling chart, that the ridge `edgeFace v 0 k`
is the midpoint, that the carrier cell of the node is `edgeCell v 0 k` and that the two vertices
are exactly the facets of the ridge.
-/
import Mathlib
import Submission.Work.BridgeSquare.FibreData
import Submission.Work.Cusp.Data
import Submission.Work.FoldInst.Basic
import Submission.Work.RTOwed.cuspDev
import Submission.Work.BridgeSquare.ChartAlgA
import Submission.Work.MbarHomology.Mbar.mbarReal_exists

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

/-- **The unit vector in the cube-coordinate axis of `κ_{v,2}`.** -/
def axVec (v : Fin 5) : cE3 := WithLp.toLp 2 fun i : Fin 3 => if i = dirKappa v 1 then 1 else 0

/-- **The cusp coordinates of the corner of the cube carrying the `k`-th unit edge**: the cube
corner of `edgeCube v 0 k` translated by `-h`, `h = (1/2,1/2,1/2)`. -/
def cuspCorner (v : Fin 5) (k : Fin 4) : cE3 :=
  WithLp.toLp 2 fun i : Fin 3 => (Work.Cusp.cubeCorner (edgeCube v 0 k) i : ℝ) - 1/2

/-- The cusp coordinates of the far end of the `k`-th unit edge. -/
def cuspCorner1 (v : Fin 5) (k : Fin 4) : cE3 := cuspCorner v k + axVec v

/-- The cusp coordinates of the midpoint of the `k`-th unit edge. -/
def cuspMid (v : Fin 5) (k : Fin 4) : cE3 := cuspCorner v k + (1/2 : ℝ) • axVec v

/-- The real vector of the lattice vector `κ_{v,2}`. -/
def lam2V (v : Fin 5) : cE3 := WithLp.toLp 2 fun i : Fin 3 => (Work.Cusp.kappa v 1 i : ℝ)

/-- The copy bit of the cell carrying the `k`-th unit edge. -/
def edgeBit (v : Fin 5) (k : Fin 4) : ZMod 2 := cubeBitF (edgeCube v 0 k)

/-! ## §1  `κ_{v,2}` is minus the lattice step in its axis -/

theorem lam2V_eq (v : Fin 5) : lam2V v = -((fibreLen v 0 : ℝ)) • axVec v := by
  apply PiLp.ext
  intro i
  fin_cases v <;> fin_cases i <;>
    simp only [lam2V, axVec, PiLp.neg_apply, PiLp.smul_apply, PiLp.toLp_apply, Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte, smul_eq_mul, Work.BridgeSquare.fibreLen,
      Work.BridgeSquare.fibreDir, Work.BridgeSquare.dirKappa, Work.Cusp.kappa,
      Work.Cusp.latMod] <;>
    norm_num

/-- The axis vector is a unit vector. -/
theorem axVec_eq_of_ne {v : Fin 5} {i : Fin 3} (h : i ≠ dirKappa v 1) : axVec v i = 0 := by
  simp only [axVec, PiLp.toLp_apply, h, ↓reduceIte]

theorem axVec_eq_self (v : Fin 5) : axVec v (dirKappa v 1) = 1 := by
  simp only [axVec, PiLp.toLp_apply, ↓reduceIte]

/-! ## §2  The numeric facts on the generated tables -/

/-- The lower vertex of the `k`-th unit edge is the image of the cube corner. -/
theorem posR_W0 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    (Work.ConvexCells.PolytopeData.posR Work.MbarHomology.QbarPD (edgeW0Face v 0 k))
      = Work.RTOwed.kleinPt (edgeCube v 0 k)
          (WithLp.toLp 2 (fun i : Fin 3 =>
            (Work.Cusp.cubeCorner (edgeCube v 0 k) i : ℝ))) := by
  apply PiLp.ext
  intro i
  fin_cases v <;> fin_cases k <;>
    first
      | (exfalso; revert hk; decide +kernel)
      | (fin_cases i <;>
          simp only [Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
            Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
            Work.Cusp.cubeCorner, Work.MbarHomology.qPos, Work.MbarHomology.QbarPD,
            Work.BridgeSquare.edgeW0Face, Work.BridgeSquare.edgeCube,
            Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.head_val',
            Matrix.tail_val', Fin.isValue, Fin.reduceFinMk, ↓reduceIte] <;>
          norm_num)

/-- The upper vertex of the `k`-th unit edge is the image of the next cube corner. -/
theorem posR_W1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    (Work.ConvexCells.PolytopeData.posR Work.MbarHomology.QbarPD (edgeW1Face v 0 k))
      = Work.RTOwed.kleinPt (edgeCube v 0 k)
          (WithLp.toLp 2 (fun i : Fin 3 =>
            (Work.Cusp.cubeCorner (edgeCube v 0 k) i : ℝ)
              + (if i = dirKappa v 1 then 1 else 0))) := by
  apply PiLp.ext
  intro i
  fin_cases v <;> fin_cases k <;>
    first
      | (exfalso; revert hk; decide +kernel)
      | (fin_cases i <;>
          simp only [Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
            Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
            Work.Cusp.cubeCorner, Work.MbarHomology.qPos, Work.MbarHomology.QbarPD,
            Work.BridgeSquare.edgeW1Face, Work.BridgeSquare.edgeCube,
            Work.BridgeSquare.dirKappa,
            Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.head_val',
            Matrix.tail_val', Fin.isValue, Fin.reduceFinMk, ↓reduceIte] <;>
          norm_num)

/-- The ridge is the midpoint of the two vertices. -/
theorem posR_mid (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    (2 : ℝ) • Work.ConvexCells.PolytopeData.posR Work.MbarHomology.QbarPD (edgeFace v 0 k)
      = Work.ConvexCells.PolytopeData.posR Work.MbarHomology.QbarPD (edgeW0Face v 0 k)
        + Work.ConvexCells.PolytopeData.posR Work.MbarHomology.QbarPD (edgeW1Face v 0 k) := by
  apply PiLp.ext
  intro i
  fin_cases v <;> fin_cases k <;>
    first
      | (exfalso; revert hk; decide +kernel)
      | (fin_cases i <;>
          simp only [Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
            Work.MbarHomology.qPos, Work.MbarHomology.QbarPD, Work.BridgeSquare.edgeFace,
            Work.BridgeSquare.edgeW0Face, Work.BridgeSquare.edgeW1Face,
            PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.isValue, Fin.reduceFinMk,
            ↓reduceIte] <;>
          norm_num)

/-- The carrier cell of the node of the `k`-th unit edge is `edgeCell v 0 k`. -/
theorem dim_edgeFace (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    Work.Subdivision.PolyCW.dim Work.MbarHomology.QbarCW (⟨edgeFace v 0 k⟩ : QbarCell) = 1 := by
  fin_cases v <;> fin_cases k <;>
    first
      | (exfalso; revert hk; decide +kernel)
      | decide +kernel

/-- The two vertices are exactly the facets of the ridge. -/
theorem facets_edgeFace (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    Work.Subdivision.PolyCW.facets Work.MbarHomology.QbarCW (⟨edgeFace v 0 k⟩ : QbarCell)
      = {(⟨edgeW0Face v 0 k⟩ : QbarCell), (⟨edgeW1Face v 0 k⟩ : QbarCell)} := by
  fin_cases v <;> fin_cases k <;>
    first
      | (exfalso; revert hk; decide +kernel)
      | decide +kernel

/-- The incidence numbers of the two vertices of the ridge are opposite. -/
theorem qInc_edgeFace (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    qInc (edgeFace v 0 k) (edgeW0Face v 0 k) = -qInc (edgeFace v 0 k) (edgeW1Face v 0 k) := by
  fin_cases v <;> fin_cases k <;>
    first
      | (exfalso; revert hk; decide +kernel)
      | decide +kernel

end

end Work.BridgeSquare
