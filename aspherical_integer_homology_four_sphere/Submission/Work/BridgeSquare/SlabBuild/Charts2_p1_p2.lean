import Mathlib
import Submission.Work.BridgeSquare.SlabCore
import Submission.Work.BridgeSquare.denseSimplex3
import Submission.Work.BridgeSquare.Psi1Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.BridgeSquare.SlabBuild

open Convexity
open Work.Subdivision
open Work.MbarHomology

noncomputable section

/-- Leaf `801` of the square `8` of cusp `2`. -/
theorem leaf_2_8_801 :
    Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (801 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `861` of the square `8` of cusp `2`. -/
theorem leaf_2_8_861 :
    Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (861 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `177` of the square `9` of cusp `2`. -/
theorem leaf_2_9_177 :
    Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (177 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `388` of the square `9` of cusp `2`. -/
theorem leaf_2_9_388 :
    Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (388 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `412` of the square `9` of cusp `2`. -/
theorem leaf_2_9_412 :
    Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (412 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `460` of the square `9` of cusp `2`. -/
theorem leaf_2_9_460 :
    Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (460 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `476` of the square `9` of cusp `2`. -/
theorem leaf_2_9_476 :
    Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (476 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `618` of the square `9` of cusp `2`. -/
theorem leaf_2_9_618 :
    Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (618 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `696` of the square `9` of cusp `2`. -/
theorem leaf_2_9_696 :
    Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (696 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `768` of the square `9` of cusp `2`. -/
theorem leaf_2_9_768 :
    Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (768 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `834` of the square `9` of cusp `2`. -/
theorem leaf_2_9_834 :
    Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (834 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `191` of the square `10` of cusp `2`. -/
theorem leaf_2_10_191 :
    Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (191 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `392` of the square `10` of cusp `2`. -/
theorem leaf_2_10_392 :
    Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (392 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `416` of the square `10` of cusp `2`. -/
theorem leaf_2_10_416 :
    Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (416 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `464` of the square `10` of cusp `2`. -/
theorem leaf_2_10_464 :
    Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (3/4) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (464 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `480` of the square `10` of cusp `2`. -/
theorem leaf_2_10_480 :
    Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (480 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `597` of the square `10` of cusp `2`. -/
theorem leaf_2_10_597 :
    Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (597 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `678` of the square `10` of cusp `2`. -/
theorem leaf_2_10_678 :
    Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (678 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `750` of the square `10` of cusp `2`. -/
theorem leaf_2_10_750 :
    Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (750 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `819` of the square `10` of cusp `2`. -/
theorem leaf_2_10_819 :
    Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (3/4) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (819 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `184` of the square `11` of cusp `2`. -/
theorem leaf_2_11_184 :
    Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (184 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `344` of the square `11` of cusp `2`. -/
theorem leaf_2_11_344 :
    Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/2) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (344 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `368` of the square `11` of cusp `2`. -/
theorem leaf_2_11_368 :
    Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (368 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `432` of the square `11` of cusp `2`. -/
theorem leaf_2_11_432 :
    Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (3/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (432 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `448` of the square `11` of cusp `2`. -/
theorem leaf_2_11_448 :
    Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (448 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `639` of the square `11` of cusp `2`. -/
theorem leaf_2_11_639 :
    Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (639 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `714` of the square `11` of cusp `2`. -/
theorem leaf_2_11_714 :
    Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (714 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `786` of the square `11` of cusp `2`. -/
theorem leaf_2_11_786 :
    Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (786 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num



end

end Work.BridgeSquare.SlabBuild
