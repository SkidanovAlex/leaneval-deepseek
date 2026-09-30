/-
# The wall identities of the cusp cubes

For every cube `a : Fin 48` and every coordinate `i : Fin 3` the two *wall* sides of the cube
(`wallLo a i`, `wallHi a i`: the sides through the truncated ideal vertex whose facets contain the
face `{x i = cubeCorner a i}` resp. `{x i = cubeCorner a i + 1}`) have the affine slacks

  `sideSlack (wallLo a i) (kleinPt a x) = (2/5) * (x i − cubeCorner a i)`,
  `sideSlack (wallHi a i) (kleinPt a x) = (2/5) * (cubeCorner a i + 1 − x i)`.

This file is generated (one lemma per cube, plus the two general statements).
-/
import Mathlib
import Submission.Work.RTOwed.cuspDev

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped BigOperators

namespace Work.RTOwed

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_0 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 0 i) (kleinPt 0 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 0 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_0 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 0 i) (kleinPt 0 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 0 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_1 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 1 i) (kleinPt 1 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 1 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_1 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 1 i) (kleinPt 1 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 1 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_2 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 2 i) (kleinPt 2 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 2 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_2 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 2 i) (kleinPt 2 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 2 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_3 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 3 i) (kleinPt 3 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 3 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_3 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 3 i) (kleinPt 3 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 3 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_4 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 4 i) (kleinPt 4 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 4 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_4 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 4 i) (kleinPt 4 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 4 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_5 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 5 i) (kleinPt 5 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 5 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_5 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 5 i) (kleinPt 5 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 5 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_6 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 6 i) (kleinPt 6 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 6 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_6 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 6 i) (kleinPt 6 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 6 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_7 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 7 i) (kleinPt 7 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 7 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_7 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 7 i) (kleinPt 7 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 7 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_8 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 8 i) (kleinPt 8 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 8 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_8 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 8 i) (kleinPt 8 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 8 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_9 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 9 i) (kleinPt 9 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 9 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_9 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 9 i) (kleinPt 9 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 9 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_10 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 10 i) (kleinPt 10 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 10 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_10 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 10 i) (kleinPt 10 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 10 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_11 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 11 i) (kleinPt 11 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 11 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_11 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 11 i) (kleinPt 11 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 11 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_12 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 12 i) (kleinPt 12 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 12 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_12 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 12 i) (kleinPt 12 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 12 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_13 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 13 i) (kleinPt 13 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 13 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_13 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 13 i) (kleinPt 13 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 13 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_14 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 14 i) (kleinPt 14 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 14 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_14 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 14 i) (kleinPt 14 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 14 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_15 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 15 i) (kleinPt 15 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 15 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_15 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 15 i) (kleinPt 15 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 15 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_16 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 16 i) (kleinPt 16 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 16 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_16 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 16 i) (kleinPt 16 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 16 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_17 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 17 i) (kleinPt 17 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 17 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_17 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 17 i) (kleinPt 17 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 17 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_18 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 18 i) (kleinPt 18 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 18 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_18 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 18 i) (kleinPt 18 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 18 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_19 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 19 i) (kleinPt 19 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 19 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_19 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 19 i) (kleinPt 19 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 19 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_20 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 20 i) (kleinPt 20 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 20 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_20 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 20 i) (kleinPt 20 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 20 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_21 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 21 i) (kleinPt 21 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 21 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_21 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 21 i) (kleinPt 21 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 21 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_22 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 22 i) (kleinPt 22 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 22 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_22 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 22 i) (kleinPt 22 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 22 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_23 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 23 i) (kleinPt 23 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 23 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_23 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 23 i) (kleinPt 23 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 23 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_24 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 24 i) (kleinPt 24 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 24 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_24 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 24 i) (kleinPt 24 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 24 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_25 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 25 i) (kleinPt 25 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 25 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_25 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 25 i) (kleinPt 25 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 25 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_26 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 26 i) (kleinPt 26 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 26 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_26 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 26 i) (kleinPt 26 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 26 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_27 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 27 i) (kleinPt 27 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 27 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_27 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 27 i) (kleinPt 27 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 27 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_28 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 28 i) (kleinPt 28 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 28 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_28 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 28 i) (kleinPt 28 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 28 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_29 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 29 i) (kleinPt 29 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 29 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_29 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 29 i) (kleinPt 29 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 29 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_30 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 30 i) (kleinPt 30 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 30 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_30 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 30 i) (kleinPt 30 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 30 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_31 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 31 i) (kleinPt 31 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 31 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_31 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 31 i) (kleinPt 31 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 31 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_32 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 32 i) (kleinPt 32 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 32 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_32 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 32 i) (kleinPt 32 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 32 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_33 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 33 i) (kleinPt 33 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 33 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_33 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 33 i) (kleinPt 33 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 33 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_34 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 34 i) (kleinPt 34 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 34 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_34 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 34 i) (kleinPt 34 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 34 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_35 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 35 i) (kleinPt 35 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 35 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_35 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 35 i) (kleinPt 35 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 35 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_36 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 36 i) (kleinPt 36 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 36 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_36 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 36 i) (kleinPt 36 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 36 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_37 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 37 i) (kleinPt 37 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 37 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_37 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 37 i) (kleinPt 37 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 37 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_38 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 38 i) (kleinPt 38 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 38 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_38 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 38 i) (kleinPt 38 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 38 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_39 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 39 i) (kleinPt 39 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 39 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_39 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 39 i) (kleinPt 39 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 39 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_40 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 40 i) (kleinPt 40 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 40 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_40 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 40 i) (kleinPt 40 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 40 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_41 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 41 i) (kleinPt 41 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 41 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_41 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 41 i) (kleinPt 41 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 41 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_42 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 42 i) (kleinPt 42 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 42 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_42 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 42 i) (kleinPt 42 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 42 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_43 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 43 i) (kleinPt 43 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 43 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_43 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 43 i) (kleinPt 43 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 43 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_44 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 44 i) (kleinPt 44 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 44 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_44 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 44 i) (kleinPt 44 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 44 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_45 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 45 i) (kleinPt 45 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 45 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_45 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 45 i) (kleinPt 45 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 45 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_46 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 46 i) (kleinPt 46 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 46 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_46 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 46 i) (kleinPt 46 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 46 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo_47 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo 47 i) (kleinPt 47 x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner 47 i : ℝ)) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallLo, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi_47 (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi 47 i) (kleinPt 47 x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner 47 i : ℝ) + 1 - x i) := by
  fin_cases i <;>
    simp only [Work.FoldInst.sideSlack, Work.FoldInst.sideNormal, kleinPt, wallHi, Work.Cusp.cubeCorner, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb, PiLp.toLp_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring

set_option maxHeartbeats 800000 in
theorem sideSlack_wallLo (a : Fin 48) (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallLo a i) (kleinPt a x) =
      (2 / 5 : ℝ) * (x i - (Work.Cusp.cubeCorner a i : ℝ)) := by
  fin_cases a
  · exact sideSlack_wallLo_0 i x
  · exact sideSlack_wallLo_1 i x
  · exact sideSlack_wallLo_2 i x
  · exact sideSlack_wallLo_3 i x
  · exact sideSlack_wallLo_4 i x
  · exact sideSlack_wallLo_5 i x
  · exact sideSlack_wallLo_6 i x
  · exact sideSlack_wallLo_7 i x
  · exact sideSlack_wallLo_8 i x
  · exact sideSlack_wallLo_9 i x
  · exact sideSlack_wallLo_10 i x
  · exact sideSlack_wallLo_11 i x
  · exact sideSlack_wallLo_12 i x
  · exact sideSlack_wallLo_13 i x
  · exact sideSlack_wallLo_14 i x
  · exact sideSlack_wallLo_15 i x
  · exact sideSlack_wallLo_16 i x
  · exact sideSlack_wallLo_17 i x
  · exact sideSlack_wallLo_18 i x
  · exact sideSlack_wallLo_19 i x
  · exact sideSlack_wallLo_20 i x
  · exact sideSlack_wallLo_21 i x
  · exact sideSlack_wallLo_22 i x
  · exact sideSlack_wallLo_23 i x
  · exact sideSlack_wallLo_24 i x
  · exact sideSlack_wallLo_25 i x
  · exact sideSlack_wallLo_26 i x
  · exact sideSlack_wallLo_27 i x
  · exact sideSlack_wallLo_28 i x
  · exact sideSlack_wallLo_29 i x
  · exact sideSlack_wallLo_30 i x
  · exact sideSlack_wallLo_31 i x
  · exact sideSlack_wallLo_32 i x
  · exact sideSlack_wallLo_33 i x
  · exact sideSlack_wallLo_34 i x
  · exact sideSlack_wallLo_35 i x
  · exact sideSlack_wallLo_36 i x
  · exact sideSlack_wallLo_37 i x
  · exact sideSlack_wallLo_38 i x
  · exact sideSlack_wallLo_39 i x
  · exact sideSlack_wallLo_40 i x
  · exact sideSlack_wallLo_41 i x
  · exact sideSlack_wallLo_42 i x
  · exact sideSlack_wallLo_43 i x
  · exact sideSlack_wallLo_44 i x
  · exact sideSlack_wallLo_45 i x
  · exact sideSlack_wallLo_46 i x
  · exact sideSlack_wallLo_47 i x

set_option maxHeartbeats 800000 in
theorem sideSlack_wallHi (a : Fin 48) (i : Fin 3) (x : CuspE3) :
    Work.FoldInst.sideSlack (wallHi a i) (kleinPt a x) =
      (2 / 5 : ℝ) * ((Work.Cusp.cubeCorner a i : ℝ) + 1 - x i) := by
  fin_cases a
  · exact sideSlack_wallHi_0 i x
  · exact sideSlack_wallHi_1 i x
  · exact sideSlack_wallHi_2 i x
  · exact sideSlack_wallHi_3 i x
  · exact sideSlack_wallHi_4 i x
  · exact sideSlack_wallHi_5 i x
  · exact sideSlack_wallHi_6 i x
  · exact sideSlack_wallHi_7 i x
  · exact sideSlack_wallHi_8 i x
  · exact sideSlack_wallHi_9 i x
  · exact sideSlack_wallHi_10 i x
  · exact sideSlack_wallHi_11 i x
  · exact sideSlack_wallHi_12 i x
  · exact sideSlack_wallHi_13 i x
  · exact sideSlack_wallHi_14 i x
  · exact sideSlack_wallHi_15 i x
  · exact sideSlack_wallHi_16 i x
  · exact sideSlack_wallHi_17 i x
  · exact sideSlack_wallHi_18 i x
  · exact sideSlack_wallHi_19 i x
  · exact sideSlack_wallHi_20 i x
  · exact sideSlack_wallHi_21 i x
  · exact sideSlack_wallHi_22 i x
  · exact sideSlack_wallHi_23 i x
  · exact sideSlack_wallHi_24 i x
  · exact sideSlack_wallHi_25 i x
  · exact sideSlack_wallHi_26 i x
  · exact sideSlack_wallHi_27 i x
  · exact sideSlack_wallHi_28 i x
  · exact sideSlack_wallHi_29 i x
  · exact sideSlack_wallHi_30 i x
  · exact sideSlack_wallHi_31 i x
  · exact sideSlack_wallHi_32 i x
  · exact sideSlack_wallHi_33 i x
  · exact sideSlack_wallHi_34 i x
  · exact sideSlack_wallHi_35 i x
  · exact sideSlack_wallHi_36 i x
  · exact sideSlack_wallHi_37 i x
  · exact sideSlack_wallHi_38 i x
  · exact sideSlack_wallHi_39 i x
  · exact sideSlack_wallHi_40 i x
  · exact sideSlack_wallHi_41 i x
  · exact sideSlack_wallHi_42 i x
  · exact sideSlack_wallHi_43 i x
  · exact sideSlack_wallHi_44 i x
  · exact sideSlack_wallHi_45 i x
  · exact sideSlack_wallHi_46 i x
  · exact sideSlack_wallHi_47 i x
end Work.RTOwed
