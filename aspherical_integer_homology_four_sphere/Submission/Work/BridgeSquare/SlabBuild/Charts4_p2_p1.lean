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

/-- Leaf `662` of the square `20` of cusp `4`. -/
theorem leaf_4_20_662 :
    Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-3/8) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (662 : Fin 865) := by
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

/-- Leaf `668` of the square `20` of cusp `4`. -/
theorem leaf_4_20_668 :
    Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (668 : Fin 865) := by
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

/-- Leaf `674` of the square `20` of cusp `4`. -/
theorem leaf_4_20_674 :
    Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/8) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (674 : Fin 865) := by
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

/-- Leaf `677` of the square `20` of cusp `4`. -/
theorem leaf_4_20_677 :
    Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-3/8) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (677 : Fin 865) := by
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

/-- Leaf `104` of the square `21` of cusp `4`. -/
theorem leaf_4_21_104 :
    Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (104 : Fin 865) := by
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

/-- Leaf `303` of the square `21` of cusp `4`. -/
theorem leaf_4_21_303 :
    Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (303 : Fin 865) := by
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

/-- Leaf `399` of the square `21` of cusp `4`. -/
theorem leaf_4_21_399 :
    Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (1/8) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (399 : Fin 865) := by
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

/-- Leaf `466` of the square `21` of cusp `4`. -/
theorem leaf_4_21_466 :
    Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (-1/8) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (466 : Fin 865) := by
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

/-- Leaf `474` of the square `21` of cusp `4`. -/
theorem leaf_4_21_474 :
    Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (474 : Fin 865) := by
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

/-- Leaf `579` of the square `21` of cusp `4`. -/
theorem leaf_4_21_579 :
    Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (1/8) (-3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (579 : Fin 865) := by
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

/-- Leaf `608` of the square `21` of cusp `4`. -/
theorem leaf_4_21_608 :
    Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (608 : Fin 865) := by
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

/-- Leaf `614` of the square `21` of cusp `4`. -/
theorem leaf_4_21_614 :
    Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (-1/8) (-3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (614 : Fin 865) := by
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

/-- Leaf `617` of the square `21` of cusp `4`. -/
theorem leaf_4_21_617 :
    Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (1/8) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (617 : Fin 865) := by
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

/-- Leaf `91` of the square `22` of cusp `4`. -/
theorem leaf_4_22_91 :
    Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (91 : Fin 865) := by
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

/-- Leaf `266` of the square `22` of cusp `4`. -/
theorem leaf_4_22_266 :
    Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (266 : Fin 865) := by
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

/-- Leaf `326` of the square `22` of cusp `4`. -/
theorem leaf_4_22_326 :
    Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/8) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (326 : Fin 865) := by
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

/-- Leaf `439` of the square `22` of cusp `4`. -/
theorem leaf_4_22_439 :
    Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (3/8) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (439 : Fin 865) := by
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

/-- Leaf `447` of the square `22` of cusp `4`. -/
theorem leaf_4_22_447 :
    Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (447 : Fin 865) := by
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

/-- Leaf `630` of the square `22` of cusp `4`. -/
theorem leaf_4_22_630 :
    Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (3/8) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (630 : Fin 865) := by
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

/-- Leaf `773` of the square `22` of cusp `4`. -/
theorem leaf_4_22_773 :
    Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (773 : Fin 865) := by
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

/-- Leaf `782` of the square `22` of cusp `4`. -/
theorem leaf_4_22_782 :
    Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (3/8) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (782 : Fin 865) := by
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

/-- Leaf `785` of the square `22` of cusp `4`. -/
theorem leaf_4_22_785 :
    Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/8) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (785 : Fin 865) := by
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

/-- Leaf `98` of the square `24` of cusp `4`. -/
theorem leaf_4_24_98 :
    Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (98 : Fin 865) := by
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

/-- Leaf `206` of the square `24` of cusp `4`. -/
theorem leaf_4_24_206 :
    Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (206 : Fin 865) := by
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

/-- Leaf `370` of the square `24` of cusp `4`. -/
theorem leaf_4_24_370 :
    Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-3/8) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (370 : Fin 865) := by
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

/-- Leaf `455` of the square `24` of cusp `4`. -/
theorem leaf_4_24_455 :
    Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/8) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (455 : Fin 865) := by
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

/-- Leaf `463` of the square `24` of cusp `4`. -/
theorem leaf_4_24_463 :
    Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (463 : Fin 865) := by
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

/-- Leaf `669` of the square `24` of cusp `4`. -/
theorem leaf_4_24_669 :
    Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/8) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (669 : Fin 865) := by
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
