/-
# The cube certificate: the affine images of the 48 cubes lie in `Q̄` on the truncation facet

This file proves `Work.RTOwed.cuspCert.cube_quad`, a certificate about the concrete cusp
development of `Work.FoldInst.Mbar` (definitions in `Submission/Work/RTOwed/cuspDev.lean`):

* for every cube `a : Fin 48`, the affine image `kleinPt a` of the closed unit cube `cubeBox a`
  lies in the truncated 24-cell `Q̄` (`Work.FoldInst.Qbar`), and
* that image lies on the truncation facet of the ideal vertex of the cube:
  `truncSlack (cubeVert a) (kleinPt a x) = 0` for every `x ∈ cubeBox a`.

## Method

Everything is affine:

  `kleinPt a x i = ∑_j A_{a,i,j} x_j + b_{a,i}`,
  `sideSlack S y = 1 - ∑_i n_{S,i} y_i`,
  `truncSlack w y = (8 - 5 ∑_i t_{w,i} y_i)/10`,

so `sideSlack S (kleinPt a ·)`, `truncSlack w (kleinPt a ·)` are affine functions of `x`.  Writing
`x = cl_a + t` with `cl_a = cubeCorner a` and `t ∈ [0,1]³`, such a function is
`K + ∑_j E_j t_j`, and since `K + ∑_j E_j t_j ≥ K + ∑_j min(E_j, 0)` for `t ∈ [0,1]³`, it suffices
to verify the *single* integer inequality `K + ∑_j min(E_j,0) ≥ 0` for each cube and each of the 48
constraints (`Q̄` has 24 side and 24 truncation constraints).  The integer tables used (`A10 = 10 A`,
`b10 = 10 b`, `cl`) are the data of `Work.Cusp.Data` rescaled by 10, so that these 48 × 48 checks are
decidable integer arithmetic (`minSideZ_nonneg`, `minTruncZ_nonneg` below, proved by `decide`).

The truncation constraints of the *own* ideal vertex are not merely non-negative but identically
zero on the cube (`twenty_truncSlack_vert`), because the two coefficient vectors `KVg`, `EVg` of
`20 · truncSlack (cubeVert a) (kleinPt a ·)` vanish identically (`KVg_vert_zero`, `EVg_vert_zero`).

The only bridge needed between the rescaled integer tables and the rational data of
`Work.Cusp.Data` is `hA10`/`hb10`/`hclR` below (entry-by-entry `norm_num`).
-/
import Mathlib
import Submission.Work.RTOwed.cuspDev

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators

namespace Work.RTOwed.cuspCert

/-! ## The rescaled integral data

`A10 a i j = 10 * cubeXToKlein a i j`, `b10 a i = 10 * cubeXToKleinb a i` and `cl = cubeCorner`
are the integer tables of the affine maps `kleinPt a` (whose entries have denominators dividing
5 and 10), rescaled so that all the later computations are integer arithmetic. -/

/-- `10 * cubeXToKlein a i j`. -/
def A10 : Fin 48 → Fin 4 → Fin 3 → ℤ := ![
  ![ ![0, 0, 0], ![-4, 0, 0], ![0, -4, 0], ![0, 0, -4]],
  ![ ![0, 0, 0], ![4, 0, 0], ![0, -4, 0], ![0, 0, -4]],
  ![ ![0, 0, 0], ![4, 0, 0], ![0, 4, 0], ![0, 0, -4]],
  ![ ![0, 0, 0], ![-4, 0, 0], ![0, 4, 0], ![0, 0, -4]],
  ![ ![-4, 0, 0], ![0, 0, 0], ![0, -4, 0], ![0, 0, -4]],
  ![ ![4, 0, 0], ![0, 0, 0], ![0, -4, 0], ![0, 0, 4]],
  ![ ![-4, 0, 0], ![0, 0, 0], ![0, -4, 0], ![0, 0, 4]],
  ![ ![4, 0, 0], ![0, 0, 0], ![0, -4, 0], ![0, 0, -4]],
  ![ ![-4, 0, 0], ![0, -4, 0], ![0, 0, 0], ![0, 0, -4]],
  ![ ![4, 0, 0], ![0, -4, 0], ![0, 0, 0], ![0, 0, -4]],
  ![ ![4, 0, 0], ![0, -4, 0], ![0, 0, 0], ![0, 0, 4]],
  ![ ![-4, 0, 0], ![0, -4, 0], ![0, 0, 0], ![0, 0, 4]],
  ![ ![-4, 0, 0], ![0, -4, 0], ![0, 0, -4], ![0, 0, 0]],
  ![ ![-4, 0, 0], ![0, 4, 0], ![0, 0, 4], ![0, 0, 0]],
  ![ ![-4, 0, 0], ![0, -4, 0], ![0, 0, 4], ![0, 0, 0]],
  ![ ![-4, 0, 0], ![0, 4, 0], ![0, 0, -4], ![0, 0, 0]],
  ![ ![2, 2, -2], ![2, -2, 2], ![-2, 2, 2], ![-2, -2, -2]],
  ![ ![2, -2, 2], ![-2, -2, 2], ![2, 2, 2], ![2, -2, -2]],
  ![ ![2, -2, -2], ![2, 2, 2], ![2, 2, -2], ![-2, 2, -2]],
  ![ ![-2, -2, -2], ![-2, 2, 2], ![2, -2, 2], ![2, 2, -2]],
  ![ ![2, -2, -2], ![-2, -2, -2], ![-2, -2, 2], ![-2, 2, -2]],
  ![ ![-2, 2, -2], ![-2, -2, 2], ![2, 2, 2], ![-2, 2, 2]],
  ![ ![2, 2, 2], ![-2, 2, 2], ![-2, 2, -2], ![2, 2, -2]],
  ![ ![-2, 2, 2], ![2, 2, 2], ![-2, -2, 2], ![-2, 2, -2]],
  ![ ![2, 2, 2], ![2, -2, -2], ![2, -2, 2], ![2, 2, -2]],
  ![ ![-2, -2, 2], ![2, -2, 2], ![-2, 2, 2], ![2, 2, 2]],
  ![ ![-2, 2, -2], ![-2, -2, 2], ![-2, -2, -2], ![2, -2, -2]],
  ![ ![2, 2, -2], ![-2, 2, -2], ![2, -2, -2], ![-2, -2, -2]],
  ![ ![-2, -2, -2], ![-2, 2, 2], ![-2, 2, -2], ![-2, -2, 2]],
  ![ ![-2, 2, -2], ![2, 2, -2], ![2, 2, 2], ![2, -2, -2]],
  ![ ![2, -2, -2], ![2, 2, 2], ![-2, -2, 2], ![2, -2, 2]],
  ![ ![-2, -2, -2], ![2, -2, -2], ![2, -2, 2], ![-2, -2, 2]],
  ![ ![-2, -2, 2], ![2, -2, 2], ![2, -2, -2], ![-2, -2, -2]],
  ![ ![2, -2, 2], ![2, 2, -2], ![-2, -2, -2], ![2, -2, -2]],
  ![ ![-2, 2, 2], ![2, 2, 2], ![2, 2, -2], ![2, -2, 2]],
  ![ ![-2, -2, 2], ![-2, 2, -2], ![-2, 2, 2], ![-2, -2, -2]],
  ![ ![2, 2, 2], ![-2, 2, 2], ![2, -2, 2], ![-2, -2, 2]],
  ![ ![-2, 2, 2], ![-2, -2, -2], ![-2, -2, 2], ![2, -2, 2]],
  ![ ![-2, -2, -2], ![2, -2, -2], ![-2, 2, -2], ![2, 2, -2]],
  ![ ![2, 2, -2], ![2, -2, 2], ![2, -2, -2], ![2, 2, 2]],
  ![ ![-2, 2, -2], ![2, 2, -2], ![-2, -2, -2], ![-2, 2, 2]],
  ![ ![2, 2, -2], ![-2, 2, -2], ![-2, 2, 2], ![2, 2, 2]],
  ![ ![-2, 2, 2], ![-2, -2, -2], ![2, 2, -2], ![-2, 2, -2]],
  ![ ![2, -2, 2], ![-2, -2, 2], ![-2, -2, -2], ![-2, 2, 2]],
  ![ ![-2, -2, 2], ![-2, 2, -2], ![2, -2, -2], ![2, 2, 2]],
  ![ ![2, -2, 2], ![2, 2, -2], ![2, 2, 2], ![-2, 2, 2]],
  ![ ![2, -2, -2], ![-2, -2, -2], ![2, 2, -2], ![2, -2, 2]],
  ![ ![2, 2, 2], ![2, -2, -2], ![-2, 2, -2], ![-2, -2, 2]]]

/-- `10 * cubeXToKleinb a i`. -/
def b10 : Fin 48 → Fin 4 → ℤ := ![
  ![8, 2, 2, 2],
  ![-8, 2, 2, 2],
  ![-8, -2, -2, -2],
  ![8, -2, -2, -2],
  ![2, 8, 2, 2],
  ![-2, -8, -2, -2],
  ![2, -8, 2, 2],
  ![-2, 8, -2, 6],
  ![2, 2, 8, 2],
  ![2, 2, -8, 2],
  ![-2, -2, -8, -2],
  ![-2, -2, 8, -2],
  ![2, 2, 2, 8],
  ![-2, -2, -2, -8],
  ![2, 2, 2, -8],
  ![-2, -2, 6, 8],
  ![-5, -5, -5, -1],
  ![5, -5, -5, -1],
  ![-5, -5, 5, -1],
  ![5, 5, 5, 1],
  ![-1, 9, -1, -5],
  ![-1, -1, -9, 5],
  ![5, -5, 5, -1],
  ![-5, 5, 5, 1],
  ![1, 9, -1, -5],
  ![1, -1, -9, 5],
  ![5, 5, -5, 1],
  ![-1, 9, 1, -5],
  ![-1, -1, 9, 5],
  ![1, -9, 1, 5],
  ![1, 1, 9, -5],
  ![3, 5, -5, 9],
  ![-5, 5, -5, 1],
  ![1, 9, 1, -5],
  ![1, -1, 9, 5],
  ![-1, -9, 1, 5],
  ![-1, 1, 9, -5],
  ![-3, 5, -5, 9],
  ![1, -9, -1, 5],
  ![1, 1, -9, -5],
  ![3, 5, 5, 9],
  ![-3, -5, 5, -9],
  ![-1, -9, -1, 5],
  ![-1, 1, -9, -5],
  ![-3, 5, 5, 9],
  ![3, -5, 5, -9],
  ![-3, -5, -5, -9],
  ![3, -5, -5, -9]]

/-- `cubeCorner a` (the lower corner of the cube in cube coordinates). -/
def cl : Fin 48 → Fin 3 → ℤ := ![
  ![0, 0, 0],
  ![-1, 0, 0],
  ![0, 0, -1],
  ![-1, 0, -1],
  ![0, 0, 0],
  ![0, -1, 0],
  ![0, 0, -1],
  ![0, -1, 1],
  ![0, 0, 0],
  ![-1, 0, 0],
  ![0, -1, 0],
  ![-1, -1, 0],
  ![0, 0, 0],
  ![-1, 0, 0],
  ![0, 0, -1],
  ![-1, 0, 1],
  ![0, 0, 0],
  ![-1, 0, 0],
  ![0, -1, 0],
  ![0, 0, -1],
  ![0, 1, 0],
  ![1, 0, 0],
  ![-1, -1, 0],
  ![-1, 0, -1],
  ![-1, 1, 0],
  ![-2, 0, 0],
  ![0, -1, -1],
  ![0, -2, 0],
  ![1, -1, 0],
  ![0, 1, -1],
  ![1, 0, -1],
  ![1, 1, 0],
  ![-1, -1, -1],
  ![-1, -2, 0],
  ![-2, -1, 0],
  ![-1, 1, -1],
  ![-2, 0, -1],
  ![-2, 1, 0],
  ![0, -2, -1],
  ![1, -1, -1],
  ![1, -2, 0],
  ![1, 1, -1],
  ![-1, -2, -1],
  ![-2, -1, -1],
  ![-2, -2, 0],
  ![-2, 1, -1],
  ![1, -2, -1],
  ![-2, -2, -1]]


/-! ## Evaluation lemmas for the tables

These are the only place where the big generated tables are unfolded; every later computation
rewrites with them.  They are `rfl`, and are registered `local simp` for the section below
(which is closed right after the bridges, so that no other file inherits the large simp set). -/

section Eval
@[local simp] theorem sideNormal_val_0_0 : Work.FoldInst.sideNormal 0 0 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_0_1 : Work.FoldInst.sideNormal 0 1 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_0_2 : Work.FoldInst.sideNormal 0 2 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_0_3 : Work.FoldInst.sideNormal 0 3 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_1_0 : Work.FoldInst.sideNormal 1 0 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_1_1 : Work.FoldInst.sideNormal 1 1 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_1_2 : Work.FoldInst.sideNormal 1 2 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_1_3 : Work.FoldInst.sideNormal 1 3 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_2_0 : Work.FoldInst.sideNormal 2 0 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_2_1 : Work.FoldInst.sideNormal 2 1 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_2_2 : Work.FoldInst.sideNormal 2 2 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_2_3 : Work.FoldInst.sideNormal 2 3 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_3_0 : Work.FoldInst.sideNormal 3 0 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_3_1 : Work.FoldInst.sideNormal 3 1 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_3_2 : Work.FoldInst.sideNormal 3 2 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_3_3 : Work.FoldInst.sideNormal 3 3 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_4_0 : Work.FoldInst.sideNormal 4 0 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_4_1 : Work.FoldInst.sideNormal 4 1 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_4_2 : Work.FoldInst.sideNormal 4 2 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_4_3 : Work.FoldInst.sideNormal 4 3 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_5_0 : Work.FoldInst.sideNormal 5 0 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_5_1 : Work.FoldInst.sideNormal 5 1 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_5_2 : Work.FoldInst.sideNormal 5 2 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_5_3 : Work.FoldInst.sideNormal 5 3 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_6_0 : Work.FoldInst.sideNormal 6 0 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_6_1 : Work.FoldInst.sideNormal 6 1 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_6_2 : Work.FoldInst.sideNormal 6 2 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_6_3 : Work.FoldInst.sideNormal 6 3 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_7_0 : Work.FoldInst.sideNormal 7 0 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_7_1 : Work.FoldInst.sideNormal 7 1 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_7_2 : Work.FoldInst.sideNormal 7 2 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_7_3 : Work.FoldInst.sideNormal 7 3 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_8_0 : Work.FoldInst.sideNormal 8 0 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_8_1 : Work.FoldInst.sideNormal 8 1 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_8_2 : Work.FoldInst.sideNormal 8 2 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_8_3 : Work.FoldInst.sideNormal 8 3 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_9_0 : Work.FoldInst.sideNormal 9 0 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_9_1 : Work.FoldInst.sideNormal 9 1 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_9_2 : Work.FoldInst.sideNormal 9 2 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_9_3 : Work.FoldInst.sideNormal 9 3 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_10_0 : Work.FoldInst.sideNormal 10 0 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_10_1 : Work.FoldInst.sideNormal 10 1 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_10_2 : Work.FoldInst.sideNormal 10 2 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_10_3 : Work.FoldInst.sideNormal 10 3 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_11_0 : Work.FoldInst.sideNormal 11 0 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_11_1 : Work.FoldInst.sideNormal 11 1 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_11_2 : Work.FoldInst.sideNormal 11 2 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_11_3 : Work.FoldInst.sideNormal 11 3 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_12_0 : Work.FoldInst.sideNormal 12 0 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_12_1 : Work.FoldInst.sideNormal 12 1 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_12_2 : Work.FoldInst.sideNormal 12 2 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_12_3 : Work.FoldInst.sideNormal 12 3 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_13_0 : Work.FoldInst.sideNormal 13 0 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_13_1 : Work.FoldInst.sideNormal 13 1 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_13_2 : Work.FoldInst.sideNormal 13 2 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_13_3 : Work.FoldInst.sideNormal 13 3 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_14_0 : Work.FoldInst.sideNormal 14 0 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_14_1 : Work.FoldInst.sideNormal 14 1 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_14_2 : Work.FoldInst.sideNormal 14 2 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_14_3 : Work.FoldInst.sideNormal 14 3 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_15_0 : Work.FoldInst.sideNormal 15 0 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_15_1 : Work.FoldInst.sideNormal 15 1 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_15_2 : Work.FoldInst.sideNormal 15 2 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_15_3 : Work.FoldInst.sideNormal 15 3 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_16_0 : Work.FoldInst.sideNormal 16 0 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_16_1 : Work.FoldInst.sideNormal 16 1 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_16_2 : Work.FoldInst.sideNormal 16 2 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_16_3 : Work.FoldInst.sideNormal 16 3 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_17_0 : Work.FoldInst.sideNormal 17 0 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_17_1 : Work.FoldInst.sideNormal 17 1 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_17_2 : Work.FoldInst.sideNormal 17 2 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_17_3 : Work.FoldInst.sideNormal 17 3 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_18_0 : Work.FoldInst.sideNormal 18 0 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_18_1 : Work.FoldInst.sideNormal 18 1 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_18_2 : Work.FoldInst.sideNormal 18 2 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_18_3 : Work.FoldInst.sideNormal 18 3 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_19_0 : Work.FoldInst.sideNormal 19 0 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_19_1 : Work.FoldInst.sideNormal 19 1 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_19_2 : Work.FoldInst.sideNormal 19 2 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_19_3 : Work.FoldInst.sideNormal 19 3 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_20_0 : Work.FoldInst.sideNormal 20 0 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_20_1 : Work.FoldInst.sideNormal 20 1 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_20_2 : Work.FoldInst.sideNormal 20 2 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_20_3 : Work.FoldInst.sideNormal 20 3 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_21_0 : Work.FoldInst.sideNormal 21 0 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_21_1 : Work.FoldInst.sideNormal 21 1 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_21_2 : Work.FoldInst.sideNormal 21 2 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_21_3 : Work.FoldInst.sideNormal 21 3 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_22_0 : Work.FoldInst.sideNormal 22 0 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_22_1 : Work.FoldInst.sideNormal 22 1 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_22_2 : Work.FoldInst.sideNormal 22 2 = (1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_22_3 : Work.FoldInst.sideNormal 22 3 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_23_0 : Work.FoldInst.sideNormal 23 0 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_23_1 : Work.FoldInst.sideNormal 23 1 = (0 : ℤ) := rfl
@[local simp] theorem sideNormal_val_23_2 : Work.FoldInst.sideNormal 23 2 = (-1 : ℤ) := rfl
@[local simp] theorem sideNormal_val_23_3 : Work.FoldInst.sideNormal 23 3 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_0_0 : Work.FoldInst.truncNormal2 0 0 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_0_1 : Work.FoldInst.truncNormal2 0 1 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_0_2 : Work.FoldInst.truncNormal2 0 2 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_0_3 : Work.FoldInst.truncNormal2 0 3 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_1_0 : Work.FoldInst.truncNormal2 1 0 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_1_1 : Work.FoldInst.truncNormal2 1 1 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_1_2 : Work.FoldInst.truncNormal2 1 2 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_1_3 : Work.FoldInst.truncNormal2 1 3 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_2_0 : Work.FoldInst.truncNormal2 2 0 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_2_1 : Work.FoldInst.truncNormal2 2 1 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_2_2 : Work.FoldInst.truncNormal2 2 2 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_2_3 : Work.FoldInst.truncNormal2 2 3 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_3_0 : Work.FoldInst.truncNormal2 3 0 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_3_1 : Work.FoldInst.truncNormal2 3 1 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_3_2 : Work.FoldInst.truncNormal2 3 2 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_3_3 : Work.FoldInst.truncNormal2 3 3 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_4_0 : Work.FoldInst.truncNormal2 4 0 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_4_1 : Work.FoldInst.truncNormal2 4 1 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_4_2 : Work.FoldInst.truncNormal2 4 2 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_4_3 : Work.FoldInst.truncNormal2 4 3 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_5_0 : Work.FoldInst.truncNormal2 5 0 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_5_1 : Work.FoldInst.truncNormal2 5 1 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_5_2 : Work.FoldInst.truncNormal2 5 2 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_5_3 : Work.FoldInst.truncNormal2 5 3 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_6_0 : Work.FoldInst.truncNormal2 6 0 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_6_1 : Work.FoldInst.truncNormal2 6 1 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_6_2 : Work.FoldInst.truncNormal2 6 2 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_6_3 : Work.FoldInst.truncNormal2 6 3 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_7_0 : Work.FoldInst.truncNormal2 7 0 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_7_1 : Work.FoldInst.truncNormal2 7 1 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_7_2 : Work.FoldInst.truncNormal2 7 2 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_7_3 : Work.FoldInst.truncNormal2 7 3 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_8_0 : Work.FoldInst.truncNormal2 8 0 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_8_1 : Work.FoldInst.truncNormal2 8 1 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_8_2 : Work.FoldInst.truncNormal2 8 2 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_8_3 : Work.FoldInst.truncNormal2 8 3 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_9_0 : Work.FoldInst.truncNormal2 9 0 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_9_1 : Work.FoldInst.truncNormal2 9 1 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_9_2 : Work.FoldInst.truncNormal2 9 2 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_9_3 : Work.FoldInst.truncNormal2 9 3 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_10_0 : Work.FoldInst.truncNormal2 10 0 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_10_1 : Work.FoldInst.truncNormal2 10 1 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_10_2 : Work.FoldInst.truncNormal2 10 2 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_10_3 : Work.FoldInst.truncNormal2 10 3 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_11_0 : Work.FoldInst.truncNormal2 11 0 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_11_1 : Work.FoldInst.truncNormal2 11 1 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_11_2 : Work.FoldInst.truncNormal2 11 2 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_11_3 : Work.FoldInst.truncNormal2 11 3 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_12_0 : Work.FoldInst.truncNormal2 12 0 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_12_1 : Work.FoldInst.truncNormal2 12 1 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_12_2 : Work.FoldInst.truncNormal2 12 2 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_12_3 : Work.FoldInst.truncNormal2 12 3 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_13_0 : Work.FoldInst.truncNormal2 13 0 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_13_1 : Work.FoldInst.truncNormal2 13 1 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_13_2 : Work.FoldInst.truncNormal2 13 2 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_13_3 : Work.FoldInst.truncNormal2 13 3 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_14_0 : Work.FoldInst.truncNormal2 14 0 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_14_1 : Work.FoldInst.truncNormal2 14 1 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_14_2 : Work.FoldInst.truncNormal2 14 2 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_14_3 : Work.FoldInst.truncNormal2 14 3 = (-1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_15_0 : Work.FoldInst.truncNormal2 15 0 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_15_1 : Work.FoldInst.truncNormal2 15 1 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_15_2 : Work.FoldInst.truncNormal2 15 2 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_15_3 : Work.FoldInst.truncNormal2 15 3 = (1 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_16_0 : Work.FoldInst.truncNormal2 16 0 = (2 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_16_1 : Work.FoldInst.truncNormal2 16 1 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_16_2 : Work.FoldInst.truncNormal2 16 2 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_16_3 : Work.FoldInst.truncNormal2 16 3 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_17_0 : Work.FoldInst.truncNormal2 17 0 = (-2 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_17_1 : Work.FoldInst.truncNormal2 17 1 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_17_2 : Work.FoldInst.truncNormal2 17 2 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_17_3 : Work.FoldInst.truncNormal2 17 3 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_18_0 : Work.FoldInst.truncNormal2 18 0 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_18_1 : Work.FoldInst.truncNormal2 18 1 = (2 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_18_2 : Work.FoldInst.truncNormal2 18 2 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_18_3 : Work.FoldInst.truncNormal2 18 3 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_19_0 : Work.FoldInst.truncNormal2 19 0 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_19_1 : Work.FoldInst.truncNormal2 19 1 = (-2 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_19_2 : Work.FoldInst.truncNormal2 19 2 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_19_3 : Work.FoldInst.truncNormal2 19 3 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_20_0 : Work.FoldInst.truncNormal2 20 0 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_20_1 : Work.FoldInst.truncNormal2 20 1 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_20_2 : Work.FoldInst.truncNormal2 20 2 = (2 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_20_3 : Work.FoldInst.truncNormal2 20 3 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_21_0 : Work.FoldInst.truncNormal2 21 0 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_21_1 : Work.FoldInst.truncNormal2 21 1 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_21_2 : Work.FoldInst.truncNormal2 21 2 = (-2 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_21_3 : Work.FoldInst.truncNormal2 21 3 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_22_0 : Work.FoldInst.truncNormal2 22 0 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_22_1 : Work.FoldInst.truncNormal2 22 1 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_22_2 : Work.FoldInst.truncNormal2 22 2 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_22_3 : Work.FoldInst.truncNormal2 22 3 = (2 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_23_0 : Work.FoldInst.truncNormal2 23 0 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_23_1 : Work.FoldInst.truncNormal2 23 1 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_23_2 : Work.FoldInst.truncNormal2 23 2 = (0 : ℤ) := rfl
@[local simp] theorem truncNormal2_val_23_3 : Work.FoldInst.truncNormal2 23 3 = (-2 : ℤ) := rfl
@[local simp] theorem cubeVert_val_0 : Work.RTOwed.cubeVert 0 = (16 : Fin 24) := rfl
@[local simp] theorem cl_val_0_0 : cl 0 0 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_0_1 : cl 0 1 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_0_2 : cl 0 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_0_0_0 : A10 0 0 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_0_0_1 : A10 0 0 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_0_0_2 : A10 0 0 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_0_0 : b10 0 0 = (8 : ℤ) := rfl
@[local simp] theorem A10_val_0_1_0 : A10 0 1 0 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_0_1_1 : A10 0 1 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_0_1_2 : A10 0 1 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_0_1 : b10 0 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_0_2_0 : A10 0 2 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_0_2_1 : A10 0 2 1 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_0_2_2 : A10 0 2 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_0_2 : b10 0 2 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_0_3_0 : A10 0 3 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_0_3_1 : A10 0 3 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_0_3_2 : A10 0 3 2 = (-4 : ℤ) := rfl
@[local simp] theorem b10_val_0_3 : b10 0 3 = (2 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_0_0_0 : Work.Cusp.cubeXToKlein 0 0 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_0_0_1 : Work.Cusp.cubeXToKlein 0 0 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_0_0_2 : Work.Cusp.cubeXToKlein 0 0 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_0_0 : Work.Cusp.cubeXToKleinb 0 0 = ((4 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_0_1_0 : Work.Cusp.cubeXToKlein 0 1 0 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_0_1_1 : Work.Cusp.cubeXToKlein 0 1 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_0_1_2 : Work.Cusp.cubeXToKlein 0 1 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_0_1 : Work.Cusp.cubeXToKleinb 0 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_0_2_0 : Work.Cusp.cubeXToKlein 0 2 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_0_2_1 : Work.Cusp.cubeXToKlein 0 2 1 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_0_2_2 : Work.Cusp.cubeXToKlein 0 2 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_0_2 : Work.Cusp.cubeXToKleinb 0 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_0_3_0 : Work.Cusp.cubeXToKlein 0 3 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_0_3_1 : Work.Cusp.cubeXToKlein 0 3 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_0_3_2 : Work.Cusp.cubeXToKlein 0 3 2 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_0_3 : Work.Cusp.cubeXToKleinb 0 3 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeVert_val_1 : Work.RTOwed.cubeVert 1 = (17 : Fin 24) := rfl
@[local simp] theorem cl_val_1_0 : cl 1 0 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_1_1 : cl 1 1 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_1_2 : cl 1 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_1_0_0 : A10 1 0 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_1_0_1 : A10 1 0 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_1_0_2 : A10 1 0 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_1_0 : b10 1 0 = (-8 : ℤ) := rfl
@[local simp] theorem A10_val_1_1_0 : A10 1 1 0 = (4 : ℤ) := rfl
@[local simp] theorem A10_val_1_1_1 : A10 1 1 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_1_1_2 : A10 1 1 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_1_1 : b10 1 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_1_2_0 : A10 1 2 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_1_2_1 : A10 1 2 1 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_1_2_2 : A10 1 2 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_1_2 : b10 1 2 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_1_3_0 : A10 1 3 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_1_3_1 : A10 1 3 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_1_3_2 : A10 1 3 2 = (-4 : ℤ) := rfl
@[local simp] theorem b10_val_1_3 : b10 1 3 = (2 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_1_0_0 : Work.Cusp.cubeXToKlein 1 0 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_1_0_1 : Work.Cusp.cubeXToKlein 1 0 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_1_0_2 : Work.Cusp.cubeXToKlein 1 0 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_1_0 : Work.Cusp.cubeXToKleinb 1 0 = ((-4 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_1_1_0 : Work.Cusp.cubeXToKlein 1 1 0 = ((2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_1_1_1 : Work.Cusp.cubeXToKlein 1 1 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_1_1_2 : Work.Cusp.cubeXToKlein 1 1 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_1_1 : Work.Cusp.cubeXToKleinb 1 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_1_2_0 : Work.Cusp.cubeXToKlein 1 2 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_1_2_1 : Work.Cusp.cubeXToKlein 1 2 1 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_1_2_2 : Work.Cusp.cubeXToKlein 1 2 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_1_2 : Work.Cusp.cubeXToKleinb 1 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_1_3_0 : Work.Cusp.cubeXToKlein 1 3 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_1_3_1 : Work.Cusp.cubeXToKlein 1 3 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_1_3_2 : Work.Cusp.cubeXToKlein 1 3 2 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_1_3 : Work.Cusp.cubeXToKleinb 1 3 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeVert_val_2 : Work.RTOwed.cubeVert 2 = (17 : Fin 24) := rfl
@[local simp] theorem cl_val_2_0 : cl 2 0 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_2_1 : cl 2 1 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_2_2 : cl 2 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_2_0_0 : A10 2 0 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_2_0_1 : A10 2 0 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_2_0_2 : A10 2 0 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_2_0 : b10 2 0 = (-8 : ℤ) := rfl
@[local simp] theorem A10_val_2_1_0 : A10 2 1 0 = (4 : ℤ) := rfl
@[local simp] theorem A10_val_2_1_1 : A10 2 1 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_2_1_2 : A10 2 1 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_2_1 : b10 2 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_2_2_0 : A10 2 2 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_2_2_1 : A10 2 2 1 = (4 : ℤ) := rfl
@[local simp] theorem A10_val_2_2_2 : A10 2 2 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_2_2 : b10 2 2 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_2_3_0 : A10 2 3 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_2_3_1 : A10 2 3 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_2_3_2 : A10 2 3 2 = (-4 : ℤ) := rfl
@[local simp] theorem b10_val_2_3 : b10 2 3 = (-2 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_2_0_0 : Work.Cusp.cubeXToKlein 2 0 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_2_0_1 : Work.Cusp.cubeXToKlein 2 0 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_2_0_2 : Work.Cusp.cubeXToKlein 2 0 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_2_0 : Work.Cusp.cubeXToKleinb 2 0 = ((-4 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_2_1_0 : Work.Cusp.cubeXToKlein 2 1 0 = ((2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_2_1_1 : Work.Cusp.cubeXToKlein 2 1 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_2_1_2 : Work.Cusp.cubeXToKlein 2 1 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_2_1 : Work.Cusp.cubeXToKleinb 2 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_2_2_0 : Work.Cusp.cubeXToKlein 2 2 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_2_2_1 : Work.Cusp.cubeXToKlein 2 2 1 = ((2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_2_2_2 : Work.Cusp.cubeXToKlein 2 2 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_2_2 : Work.Cusp.cubeXToKleinb 2 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_2_3_0 : Work.Cusp.cubeXToKlein 2 3 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_2_3_1 : Work.Cusp.cubeXToKlein 2 3 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_2_3_2 : Work.Cusp.cubeXToKlein 2 3 2 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_2_3 : Work.Cusp.cubeXToKleinb 2 3 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeVert_val_3 : Work.RTOwed.cubeVert 3 = (16 : Fin 24) := rfl
@[local simp] theorem cl_val_3_0 : cl 3 0 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_3_1 : cl 3 1 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_3_2 : cl 3 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_3_0_0 : A10 3 0 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_3_0_1 : A10 3 0 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_3_0_2 : A10 3 0 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_3_0 : b10 3 0 = (8 : ℤ) := rfl
@[local simp] theorem A10_val_3_1_0 : A10 3 1 0 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_3_1_1 : A10 3 1 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_3_1_2 : A10 3 1 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_3_1 : b10 3 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_3_2_0 : A10 3 2 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_3_2_1 : A10 3 2 1 = (4 : ℤ) := rfl
@[local simp] theorem A10_val_3_2_2 : A10 3 2 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_3_2 : b10 3 2 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_3_3_0 : A10 3 3 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_3_3_1 : A10 3 3 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_3_3_2 : A10 3 3 2 = (-4 : ℤ) := rfl
@[local simp] theorem b10_val_3_3 : b10 3 3 = (-2 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_3_0_0 : Work.Cusp.cubeXToKlein 3 0 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_3_0_1 : Work.Cusp.cubeXToKlein 3 0 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_3_0_2 : Work.Cusp.cubeXToKlein 3 0 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_3_0 : Work.Cusp.cubeXToKleinb 3 0 = ((4 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_3_1_0 : Work.Cusp.cubeXToKlein 3 1 0 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_3_1_1 : Work.Cusp.cubeXToKlein 3 1 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_3_1_2 : Work.Cusp.cubeXToKlein 3 1 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_3_1 : Work.Cusp.cubeXToKleinb 3 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_3_2_0 : Work.Cusp.cubeXToKlein 3 2 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_3_2_1 : Work.Cusp.cubeXToKlein 3 2 1 = ((2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_3_2_2 : Work.Cusp.cubeXToKlein 3 2 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_3_2 : Work.Cusp.cubeXToKleinb 3 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_3_3_0 : Work.Cusp.cubeXToKlein 3 3 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_3_3_1 : Work.Cusp.cubeXToKlein 3 3 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_3_3_2 : Work.Cusp.cubeXToKlein 3 3 2 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_3_3 : Work.Cusp.cubeXToKleinb 3 3 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeVert_val_4 : Work.RTOwed.cubeVert 4 = (18 : Fin 24) := rfl
@[local simp] theorem cl_val_4_0 : cl 4 0 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_4_1 : cl 4 1 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_4_2 : cl 4 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_4_0_0 : A10 4 0 0 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_4_0_1 : A10 4 0 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_4_0_2 : A10 4 0 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_4_0 : b10 4 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_4_1_0 : A10 4 1 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_4_1_1 : A10 4 1 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_4_1_2 : A10 4 1 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_4_1 : b10 4 1 = (8 : ℤ) := rfl
@[local simp] theorem A10_val_4_2_0 : A10 4 2 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_4_2_1 : A10 4 2 1 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_4_2_2 : A10 4 2 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_4_2 : b10 4 2 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_4_3_0 : A10 4 3 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_4_3_1 : A10 4 3 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_4_3_2 : A10 4 3 2 = (-4 : ℤ) := rfl
@[local simp] theorem b10_val_4_3 : b10 4 3 = (2 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_4_0_0 : Work.Cusp.cubeXToKlein 4 0 0 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_4_0_1 : Work.Cusp.cubeXToKlein 4 0 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_4_0_2 : Work.Cusp.cubeXToKlein 4 0 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_4_0 : Work.Cusp.cubeXToKleinb 4 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_4_1_0 : Work.Cusp.cubeXToKlein 4 1 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_4_1_1 : Work.Cusp.cubeXToKlein 4 1 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_4_1_2 : Work.Cusp.cubeXToKlein 4 1 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_4_1 : Work.Cusp.cubeXToKleinb 4 1 = ((4 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_4_2_0 : Work.Cusp.cubeXToKlein 4 2 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_4_2_1 : Work.Cusp.cubeXToKlein 4 2 1 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_4_2_2 : Work.Cusp.cubeXToKlein 4 2 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_4_2 : Work.Cusp.cubeXToKleinb 4 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_4_3_0 : Work.Cusp.cubeXToKlein 4 3 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_4_3_1 : Work.Cusp.cubeXToKlein 4 3 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_4_3_2 : Work.Cusp.cubeXToKlein 4 3 2 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_4_3 : Work.Cusp.cubeXToKleinb 4 3 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeVert_val_5 : Work.RTOwed.cubeVert 5 = (19 : Fin 24) := rfl
@[local simp] theorem cl_val_5_0 : cl 5 0 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_5_1 : cl 5 1 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_5_2 : cl 5 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_5_0_0 : A10 5 0 0 = (4 : ℤ) := rfl
@[local simp] theorem A10_val_5_0_1 : A10 5 0 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_5_0_2 : A10 5 0 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_5_0 : b10 5 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_5_1_0 : A10 5 1 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_5_1_1 : A10 5 1 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_5_1_2 : A10 5 1 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_5_1 : b10 5 1 = (-8 : ℤ) := rfl
@[local simp] theorem A10_val_5_2_0 : A10 5 2 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_5_2_1 : A10 5 2 1 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_5_2_2 : A10 5 2 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_5_2 : b10 5 2 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_5_3_0 : A10 5 3 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_5_3_1 : A10 5 3 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_5_3_2 : A10 5 3 2 = (4 : ℤ) := rfl
@[local simp] theorem b10_val_5_3 : b10 5 3 = (-2 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_5_0_0 : Work.Cusp.cubeXToKlein 5 0 0 = ((2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_5_0_1 : Work.Cusp.cubeXToKlein 5 0 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_5_0_2 : Work.Cusp.cubeXToKlein 5 0 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_5_0 : Work.Cusp.cubeXToKleinb 5 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_5_1_0 : Work.Cusp.cubeXToKlein 5 1 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_5_1_1 : Work.Cusp.cubeXToKlein 5 1 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_5_1_2 : Work.Cusp.cubeXToKlein 5 1 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_5_1 : Work.Cusp.cubeXToKleinb 5 1 = ((-4 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_5_2_0 : Work.Cusp.cubeXToKlein 5 2 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_5_2_1 : Work.Cusp.cubeXToKlein 5 2 1 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_5_2_2 : Work.Cusp.cubeXToKlein 5 2 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_5_2 : Work.Cusp.cubeXToKleinb 5 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_5_3_0 : Work.Cusp.cubeXToKlein 5 3 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_5_3_1 : Work.Cusp.cubeXToKlein 5 3 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_5_3_2 : Work.Cusp.cubeXToKlein 5 3 2 = ((2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_5_3 : Work.Cusp.cubeXToKleinb 5 3 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeVert_val_6 : Work.RTOwed.cubeVert 6 = (19 : Fin 24) := rfl
@[local simp] theorem cl_val_6_0 : cl 6 0 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_6_1 : cl 6 1 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_6_2 : cl 6 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_6_0_0 : A10 6 0 0 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_6_0_1 : A10 6 0 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_6_0_2 : A10 6 0 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_6_0 : b10 6 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_6_1_0 : A10 6 1 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_6_1_1 : A10 6 1 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_6_1_2 : A10 6 1 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_6_1 : b10 6 1 = (-8 : ℤ) := rfl
@[local simp] theorem A10_val_6_2_0 : A10 6 2 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_6_2_1 : A10 6 2 1 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_6_2_2 : A10 6 2 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_6_2 : b10 6 2 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_6_3_0 : A10 6 3 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_6_3_1 : A10 6 3 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_6_3_2 : A10 6 3 2 = (4 : ℤ) := rfl
@[local simp] theorem b10_val_6_3 : b10 6 3 = (2 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_6_0_0 : Work.Cusp.cubeXToKlein 6 0 0 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_6_0_1 : Work.Cusp.cubeXToKlein 6 0 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_6_0_2 : Work.Cusp.cubeXToKlein 6 0 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_6_0 : Work.Cusp.cubeXToKleinb 6 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_6_1_0 : Work.Cusp.cubeXToKlein 6 1 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_6_1_1 : Work.Cusp.cubeXToKlein 6 1 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_6_1_2 : Work.Cusp.cubeXToKlein 6 1 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_6_1 : Work.Cusp.cubeXToKleinb 6 1 = ((-4 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_6_2_0 : Work.Cusp.cubeXToKlein 6 2 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_6_2_1 : Work.Cusp.cubeXToKlein 6 2 1 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_6_2_2 : Work.Cusp.cubeXToKlein 6 2 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_6_2 : Work.Cusp.cubeXToKleinb 6 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_6_3_0 : Work.Cusp.cubeXToKlein 6 3 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_6_3_1 : Work.Cusp.cubeXToKlein 6 3 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_6_3_2 : Work.Cusp.cubeXToKlein 6 3 2 = ((2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_6_3 : Work.Cusp.cubeXToKleinb 6 3 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeVert_val_7 : Work.RTOwed.cubeVert 7 = (18 : Fin 24) := rfl
@[local simp] theorem cl_val_7_0 : cl 7 0 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_7_1 : cl 7 1 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_7_2 : cl 7 2 = (1 : ℤ) := rfl
@[local simp] theorem A10_val_7_0_0 : A10 7 0 0 = (4 : ℤ) := rfl
@[local simp] theorem A10_val_7_0_1 : A10 7 0 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_7_0_2 : A10 7 0 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_7_0 : b10 7 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_7_1_0 : A10 7 1 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_7_1_1 : A10 7 1 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_7_1_2 : A10 7 1 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_7_1 : b10 7 1 = (8 : ℤ) := rfl
@[local simp] theorem A10_val_7_2_0 : A10 7 2 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_7_2_1 : A10 7 2 1 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_7_2_2 : A10 7 2 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_7_2 : b10 7 2 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_7_3_0 : A10 7 3 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_7_3_1 : A10 7 3 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_7_3_2 : A10 7 3 2 = (-4 : ℤ) := rfl
@[local simp] theorem b10_val_7_3 : b10 7 3 = (6 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_7_0_0 : Work.Cusp.cubeXToKlein 7 0 0 = ((2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_7_0_1 : Work.Cusp.cubeXToKlein 7 0 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_7_0_2 : Work.Cusp.cubeXToKlein 7 0 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_7_0 : Work.Cusp.cubeXToKleinb 7 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_7_1_0 : Work.Cusp.cubeXToKlein 7 1 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_7_1_1 : Work.Cusp.cubeXToKlein 7 1 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_7_1_2 : Work.Cusp.cubeXToKlein 7 1 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_7_1 : Work.Cusp.cubeXToKleinb 7 1 = ((4 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_7_2_0 : Work.Cusp.cubeXToKlein 7 2 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_7_2_1 : Work.Cusp.cubeXToKlein 7 2 1 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_7_2_2 : Work.Cusp.cubeXToKlein 7 2 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_7_2 : Work.Cusp.cubeXToKleinb 7 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_7_3_0 : Work.Cusp.cubeXToKlein 7 3 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_7_3_1 : Work.Cusp.cubeXToKlein 7 3 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_7_3_2 : Work.Cusp.cubeXToKlein 7 3 2 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_7_3 : Work.Cusp.cubeXToKleinb 7 3 = ((3 : ℚ)/5) := rfl
@[local simp] theorem cubeVert_val_8 : Work.RTOwed.cubeVert 8 = (20 : Fin 24) := rfl
@[local simp] theorem cl_val_8_0 : cl 8 0 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_8_1 : cl 8 1 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_8_2 : cl 8 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_8_0_0 : A10 8 0 0 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_8_0_1 : A10 8 0 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_8_0_2 : A10 8 0 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_8_0 : b10 8 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_8_1_0 : A10 8 1 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_8_1_1 : A10 8 1 1 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_8_1_2 : A10 8 1 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_8_1 : b10 8 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_8_2_0 : A10 8 2 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_8_2_1 : A10 8 2 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_8_2_2 : A10 8 2 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_8_2 : b10 8 2 = (8 : ℤ) := rfl
@[local simp] theorem A10_val_8_3_0 : A10 8 3 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_8_3_1 : A10 8 3 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_8_3_2 : A10 8 3 2 = (-4 : ℤ) := rfl
@[local simp] theorem b10_val_8_3 : b10 8 3 = (2 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_8_0_0 : Work.Cusp.cubeXToKlein 8 0 0 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_8_0_1 : Work.Cusp.cubeXToKlein 8 0 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_8_0_2 : Work.Cusp.cubeXToKlein 8 0 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_8_0 : Work.Cusp.cubeXToKleinb 8 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_8_1_0 : Work.Cusp.cubeXToKlein 8 1 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_8_1_1 : Work.Cusp.cubeXToKlein 8 1 1 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_8_1_2 : Work.Cusp.cubeXToKlein 8 1 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_8_1 : Work.Cusp.cubeXToKleinb 8 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_8_2_0 : Work.Cusp.cubeXToKlein 8 2 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_8_2_1 : Work.Cusp.cubeXToKlein 8 2 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_8_2_2 : Work.Cusp.cubeXToKlein 8 2 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_8_2 : Work.Cusp.cubeXToKleinb 8 2 = ((4 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_8_3_0 : Work.Cusp.cubeXToKlein 8 3 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_8_3_1 : Work.Cusp.cubeXToKlein 8 3 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_8_3_2 : Work.Cusp.cubeXToKlein 8 3 2 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_8_3 : Work.Cusp.cubeXToKleinb 8 3 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeVert_val_9 : Work.RTOwed.cubeVert 9 = (21 : Fin 24) := rfl
@[local simp] theorem cl_val_9_0 : cl 9 0 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_9_1 : cl 9 1 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_9_2 : cl 9 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_9_0_0 : A10 9 0 0 = (4 : ℤ) := rfl
@[local simp] theorem A10_val_9_0_1 : A10 9 0 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_9_0_2 : A10 9 0 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_9_0 : b10 9 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_9_1_0 : A10 9 1 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_9_1_1 : A10 9 1 1 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_9_1_2 : A10 9 1 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_9_1 : b10 9 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_9_2_0 : A10 9 2 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_9_2_1 : A10 9 2 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_9_2_2 : A10 9 2 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_9_2 : b10 9 2 = (-8 : ℤ) := rfl
@[local simp] theorem A10_val_9_3_0 : A10 9 3 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_9_3_1 : A10 9 3 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_9_3_2 : A10 9 3 2 = (-4 : ℤ) := rfl
@[local simp] theorem b10_val_9_3 : b10 9 3 = (2 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_9_0_0 : Work.Cusp.cubeXToKlein 9 0 0 = ((2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_9_0_1 : Work.Cusp.cubeXToKlein 9 0 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_9_0_2 : Work.Cusp.cubeXToKlein 9 0 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_9_0 : Work.Cusp.cubeXToKleinb 9 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_9_1_0 : Work.Cusp.cubeXToKlein 9 1 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_9_1_1 : Work.Cusp.cubeXToKlein 9 1 1 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_9_1_2 : Work.Cusp.cubeXToKlein 9 1 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_9_1 : Work.Cusp.cubeXToKleinb 9 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_9_2_0 : Work.Cusp.cubeXToKlein 9 2 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_9_2_1 : Work.Cusp.cubeXToKlein 9 2 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_9_2_2 : Work.Cusp.cubeXToKlein 9 2 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_9_2 : Work.Cusp.cubeXToKleinb 9 2 = ((-4 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_9_3_0 : Work.Cusp.cubeXToKlein 9 3 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_9_3_1 : Work.Cusp.cubeXToKlein 9 3 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_9_3_2 : Work.Cusp.cubeXToKlein 9 3 2 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_9_3 : Work.Cusp.cubeXToKleinb 9 3 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeVert_val_10 : Work.RTOwed.cubeVert 10 = (21 : Fin 24) := rfl
@[local simp] theorem cl_val_10_0 : cl 10 0 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_10_1 : cl 10 1 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_10_2 : cl 10 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_10_0_0 : A10 10 0 0 = (4 : ℤ) := rfl
@[local simp] theorem A10_val_10_0_1 : A10 10 0 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_10_0_2 : A10 10 0 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_10_0 : b10 10 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_10_1_0 : A10 10 1 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_10_1_1 : A10 10 1 1 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_10_1_2 : A10 10 1 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_10_1 : b10 10 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_10_2_0 : A10 10 2 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_10_2_1 : A10 10 2 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_10_2_2 : A10 10 2 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_10_2 : b10 10 2 = (-8 : ℤ) := rfl
@[local simp] theorem A10_val_10_3_0 : A10 10 3 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_10_3_1 : A10 10 3 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_10_3_2 : A10 10 3 2 = (4 : ℤ) := rfl
@[local simp] theorem b10_val_10_3 : b10 10 3 = (-2 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_10_0_0 : Work.Cusp.cubeXToKlein 10 0 0 = ((2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_10_0_1 : Work.Cusp.cubeXToKlein 10 0 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_10_0_2 : Work.Cusp.cubeXToKlein 10 0 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_10_0 : Work.Cusp.cubeXToKleinb 10 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_10_1_0 : Work.Cusp.cubeXToKlein 10 1 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_10_1_1 : Work.Cusp.cubeXToKlein 10 1 1 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_10_1_2 : Work.Cusp.cubeXToKlein 10 1 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_10_1 : Work.Cusp.cubeXToKleinb 10 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_10_2_0 : Work.Cusp.cubeXToKlein 10 2 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_10_2_1 : Work.Cusp.cubeXToKlein 10 2 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_10_2_2 : Work.Cusp.cubeXToKlein 10 2 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_10_2 : Work.Cusp.cubeXToKleinb 10 2 = ((-4 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_10_3_0 : Work.Cusp.cubeXToKlein 10 3 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_10_3_1 : Work.Cusp.cubeXToKlein 10 3 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_10_3_2 : Work.Cusp.cubeXToKlein 10 3 2 = ((2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_10_3 : Work.Cusp.cubeXToKleinb 10 3 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeVert_val_11 : Work.RTOwed.cubeVert 11 = (20 : Fin 24) := rfl
@[local simp] theorem cl_val_11_0 : cl 11 0 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_11_1 : cl 11 1 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_11_2 : cl 11 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_11_0_0 : A10 11 0 0 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_11_0_1 : A10 11 0 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_11_0_2 : A10 11 0 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_11_0 : b10 11 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_11_1_0 : A10 11 1 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_11_1_1 : A10 11 1 1 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_11_1_2 : A10 11 1 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_11_1 : b10 11 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_11_2_0 : A10 11 2 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_11_2_1 : A10 11 2 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_11_2_2 : A10 11 2 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_11_2 : b10 11 2 = (8 : ℤ) := rfl
@[local simp] theorem A10_val_11_3_0 : A10 11 3 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_11_3_1 : A10 11 3 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_11_3_2 : A10 11 3 2 = (4 : ℤ) := rfl
@[local simp] theorem b10_val_11_3 : b10 11 3 = (-2 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_11_0_0 : Work.Cusp.cubeXToKlein 11 0 0 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_11_0_1 : Work.Cusp.cubeXToKlein 11 0 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_11_0_2 : Work.Cusp.cubeXToKlein 11 0 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_11_0 : Work.Cusp.cubeXToKleinb 11 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_11_1_0 : Work.Cusp.cubeXToKlein 11 1 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_11_1_1 : Work.Cusp.cubeXToKlein 11 1 1 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_11_1_2 : Work.Cusp.cubeXToKlein 11 1 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_11_1 : Work.Cusp.cubeXToKleinb 11 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_11_2_0 : Work.Cusp.cubeXToKlein 11 2 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_11_2_1 : Work.Cusp.cubeXToKlein 11 2 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_11_2_2 : Work.Cusp.cubeXToKlein 11 2 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_11_2 : Work.Cusp.cubeXToKleinb 11 2 = ((4 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_11_3_0 : Work.Cusp.cubeXToKlein 11 3 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_11_3_1 : Work.Cusp.cubeXToKlein 11 3 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_11_3_2 : Work.Cusp.cubeXToKlein 11 3 2 = ((2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_11_3 : Work.Cusp.cubeXToKleinb 11 3 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeVert_val_12 : Work.RTOwed.cubeVert 12 = (22 : Fin 24) := rfl
@[local simp] theorem cl_val_12_0 : cl 12 0 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_12_1 : cl 12 1 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_12_2 : cl 12 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_12_0_0 : A10 12 0 0 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_12_0_1 : A10 12 0 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_12_0_2 : A10 12 0 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_12_0 : b10 12 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_12_1_0 : A10 12 1 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_12_1_1 : A10 12 1 1 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_12_1_2 : A10 12 1 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_12_1 : b10 12 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_12_2_0 : A10 12 2 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_12_2_1 : A10 12 2 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_12_2_2 : A10 12 2 2 = (-4 : ℤ) := rfl
@[local simp] theorem b10_val_12_2 : b10 12 2 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_12_3_0 : A10 12 3 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_12_3_1 : A10 12 3 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_12_3_2 : A10 12 3 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_12_3 : b10 12 3 = (8 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_12_0_0 : Work.Cusp.cubeXToKlein 12 0 0 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_12_0_1 : Work.Cusp.cubeXToKlein 12 0 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_12_0_2 : Work.Cusp.cubeXToKlein 12 0 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_12_0 : Work.Cusp.cubeXToKleinb 12 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_12_1_0 : Work.Cusp.cubeXToKlein 12 1 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_12_1_1 : Work.Cusp.cubeXToKlein 12 1 1 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_12_1_2 : Work.Cusp.cubeXToKlein 12 1 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_12_1 : Work.Cusp.cubeXToKleinb 12 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_12_2_0 : Work.Cusp.cubeXToKlein 12 2 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_12_2_1 : Work.Cusp.cubeXToKlein 12 2 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_12_2_2 : Work.Cusp.cubeXToKlein 12 2 2 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_12_2 : Work.Cusp.cubeXToKleinb 12 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_12_3_0 : Work.Cusp.cubeXToKlein 12 3 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_12_3_1 : Work.Cusp.cubeXToKlein 12 3 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_12_3_2 : Work.Cusp.cubeXToKlein 12 3 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_12_3 : Work.Cusp.cubeXToKleinb 12 3 = ((4 : ℚ)/5) := rfl
@[local simp] theorem cubeVert_val_13 : Work.RTOwed.cubeVert 13 = (23 : Fin 24) := rfl
@[local simp] theorem cl_val_13_0 : cl 13 0 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_13_1 : cl 13 1 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_13_2 : cl 13 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_13_0_0 : A10 13 0 0 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_13_0_1 : A10 13 0 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_13_0_2 : A10 13 0 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_13_0 : b10 13 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_13_1_0 : A10 13 1 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_13_1_1 : A10 13 1 1 = (4 : ℤ) := rfl
@[local simp] theorem A10_val_13_1_2 : A10 13 1 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_13_1 : b10 13 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_13_2_0 : A10 13 2 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_13_2_1 : A10 13 2 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_13_2_2 : A10 13 2 2 = (4 : ℤ) := rfl
@[local simp] theorem b10_val_13_2 : b10 13 2 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_13_3_0 : A10 13 3 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_13_3_1 : A10 13 3 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_13_3_2 : A10 13 3 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_13_3 : b10 13 3 = (-8 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_13_0_0 : Work.Cusp.cubeXToKlein 13 0 0 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_13_0_1 : Work.Cusp.cubeXToKlein 13 0 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_13_0_2 : Work.Cusp.cubeXToKlein 13 0 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_13_0 : Work.Cusp.cubeXToKleinb 13 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_13_1_0 : Work.Cusp.cubeXToKlein 13 1 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_13_1_1 : Work.Cusp.cubeXToKlein 13 1 1 = ((2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_13_1_2 : Work.Cusp.cubeXToKlein 13 1 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_13_1 : Work.Cusp.cubeXToKleinb 13 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_13_2_0 : Work.Cusp.cubeXToKlein 13 2 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_13_2_1 : Work.Cusp.cubeXToKlein 13 2 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_13_2_2 : Work.Cusp.cubeXToKlein 13 2 2 = ((2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_13_2 : Work.Cusp.cubeXToKleinb 13 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_13_3_0 : Work.Cusp.cubeXToKlein 13 3 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_13_3_1 : Work.Cusp.cubeXToKlein 13 3 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_13_3_2 : Work.Cusp.cubeXToKlein 13 3 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_13_3 : Work.Cusp.cubeXToKleinb 13 3 = ((-4 : ℚ)/5) := rfl
@[local simp] theorem cubeVert_val_14 : Work.RTOwed.cubeVert 14 = (23 : Fin 24) := rfl
@[local simp] theorem cl_val_14_0 : cl 14 0 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_14_1 : cl 14 1 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_14_2 : cl 14 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_14_0_0 : A10 14 0 0 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_14_0_1 : A10 14 0 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_14_0_2 : A10 14 0 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_14_0 : b10 14 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_14_1_0 : A10 14 1 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_14_1_1 : A10 14 1 1 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_14_1_2 : A10 14 1 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_14_1 : b10 14 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_14_2_0 : A10 14 2 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_14_2_1 : A10 14 2 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_14_2_2 : A10 14 2 2 = (4 : ℤ) := rfl
@[local simp] theorem b10_val_14_2 : b10 14 2 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_14_3_0 : A10 14 3 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_14_3_1 : A10 14 3 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_14_3_2 : A10 14 3 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_14_3 : b10 14 3 = (-8 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_14_0_0 : Work.Cusp.cubeXToKlein 14 0 0 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_14_0_1 : Work.Cusp.cubeXToKlein 14 0 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_14_0_2 : Work.Cusp.cubeXToKlein 14 0 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_14_0 : Work.Cusp.cubeXToKleinb 14 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_14_1_0 : Work.Cusp.cubeXToKlein 14 1 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_14_1_1 : Work.Cusp.cubeXToKlein 14 1 1 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_14_1_2 : Work.Cusp.cubeXToKlein 14 1 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_14_1 : Work.Cusp.cubeXToKleinb 14 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_14_2_0 : Work.Cusp.cubeXToKlein 14 2 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_14_2_1 : Work.Cusp.cubeXToKlein 14 2 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_14_2_2 : Work.Cusp.cubeXToKlein 14 2 2 = ((2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_14_2 : Work.Cusp.cubeXToKleinb 14 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_14_3_0 : Work.Cusp.cubeXToKlein 14 3 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_14_3_1 : Work.Cusp.cubeXToKlein 14 3 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_14_3_2 : Work.Cusp.cubeXToKlein 14 3 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_14_3 : Work.Cusp.cubeXToKleinb 14 3 = ((-4 : ℚ)/5) := rfl
@[local simp] theorem cubeVert_val_15 : Work.RTOwed.cubeVert 15 = (22 : Fin 24) := rfl
@[local simp] theorem cl_val_15_0 : cl 15 0 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_15_1 : cl 15 1 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_15_2 : cl 15 2 = (1 : ℤ) := rfl
@[local simp] theorem A10_val_15_0_0 : A10 15 0 0 = (-4 : ℤ) := rfl
@[local simp] theorem A10_val_15_0_1 : A10 15 0 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_15_0_2 : A10 15 0 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_15_0 : b10 15 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_15_1_0 : A10 15 1 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_15_1_1 : A10 15 1 1 = (4 : ℤ) := rfl
@[local simp] theorem A10_val_15_1_2 : A10 15 1 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_15_1 : b10 15 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_15_2_0 : A10 15 2 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_15_2_1 : A10 15 2 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_15_2_2 : A10 15 2 2 = (-4 : ℤ) := rfl
@[local simp] theorem b10_val_15_2 : b10 15 2 = (6 : ℤ) := rfl
@[local simp] theorem A10_val_15_3_0 : A10 15 3 0 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_15_3_1 : A10 15 3 1 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_15_3_2 : A10 15 3 2 = (0 : ℤ) := rfl
@[local simp] theorem b10_val_15_3 : b10 15 3 = (8 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_15_0_0 : Work.Cusp.cubeXToKlein 15 0 0 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_15_0_1 : Work.Cusp.cubeXToKlein 15 0 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_15_0_2 : Work.Cusp.cubeXToKlein 15 0 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_15_0 : Work.Cusp.cubeXToKleinb 15 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_15_1_0 : Work.Cusp.cubeXToKlein 15 1 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_15_1_1 : Work.Cusp.cubeXToKlein 15 1 1 = ((2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_15_1_2 : Work.Cusp.cubeXToKlein 15 1 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_15_1 : Work.Cusp.cubeXToKleinb 15 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_15_2_0 : Work.Cusp.cubeXToKlein 15 2 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_15_2_1 : Work.Cusp.cubeXToKlein 15 2 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_15_2_2 : Work.Cusp.cubeXToKlein 15 2 2 = ((-2 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_15_2 : Work.Cusp.cubeXToKleinb 15 2 = ((3 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_15_3_0 : Work.Cusp.cubeXToKlein 15 3 0 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_15_3_1 : Work.Cusp.cubeXToKlein 15 3 1 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKlein_val_15_3_2 : Work.Cusp.cubeXToKlein 15 3 2 = ((0 : ℚ)/1) := rfl
@[local simp] theorem cubeXToKleinb_val_15_3 : Work.Cusp.cubeXToKleinb 15 3 = ((4 : ℚ)/5) := rfl
@[local simp] theorem cubeVert_val_16 : Work.RTOwed.cubeVert 16 = (0 : Fin 24) := rfl
@[local simp] theorem cl_val_16_0 : cl 16 0 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_16_1 : cl 16 1 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_16_2 : cl 16 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_16_0_0 : A10 16 0 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_16_0_1 : A10 16 0 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_16_0_2 : A10 16 0 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_16_0 : b10 16 0 = (-5 : ℤ) := rfl
@[local simp] theorem A10_val_16_1_0 : A10 16 1 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_16_1_1 : A10 16 1 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_16_1_2 : A10 16 1 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_16_1 : b10 16 1 = (-5 : ℤ) := rfl
@[local simp] theorem A10_val_16_2_0 : A10 16 2 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_16_2_1 : A10 16 2 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_16_2_2 : A10 16 2 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_16_2 : b10 16 2 = (-5 : ℤ) := rfl
@[local simp] theorem A10_val_16_3_0 : A10 16 3 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_16_3_1 : A10 16 3 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_16_3_2 : A10 16 3 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_16_3 : b10 16 3 = (-1 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_16_0_0 : Work.Cusp.cubeXToKlein 16 0 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_16_0_1 : Work.Cusp.cubeXToKlein 16 0 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_16_0_2 : Work.Cusp.cubeXToKlein 16 0 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_16_0 : Work.Cusp.cubeXToKleinb 16 0 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_16_1_0 : Work.Cusp.cubeXToKlein 16 1 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_16_1_1 : Work.Cusp.cubeXToKlein 16 1 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_16_1_2 : Work.Cusp.cubeXToKlein 16 1 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_16_1 : Work.Cusp.cubeXToKleinb 16 1 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_16_2_0 : Work.Cusp.cubeXToKlein 16 2 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_16_2_1 : Work.Cusp.cubeXToKlein 16 2 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_16_2_2 : Work.Cusp.cubeXToKlein 16 2 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_16_2 : Work.Cusp.cubeXToKleinb 16 2 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_16_3_0 : Work.Cusp.cubeXToKlein 16 3 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_16_3_1 : Work.Cusp.cubeXToKlein 16 3 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_16_3_2 : Work.Cusp.cubeXToKlein 16 3 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_16_3 : Work.Cusp.cubeXToKleinb 16 3 = ((-1 : ℚ)/10) := rfl
@[local simp] theorem cubeVert_val_17 : Work.RTOwed.cubeVert 17 = (8 : Fin 24) := rfl
@[local simp] theorem cl_val_17_0 : cl 17 0 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_17_1 : cl 17 1 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_17_2 : cl 17 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_17_0_0 : A10 17 0 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_17_0_1 : A10 17 0 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_17_0_2 : A10 17 0 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_17_0 : b10 17 0 = (5 : ℤ) := rfl
@[local simp] theorem A10_val_17_1_0 : A10 17 1 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_17_1_1 : A10 17 1 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_17_1_2 : A10 17 1 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_17_1 : b10 17 1 = (-5 : ℤ) := rfl
@[local simp] theorem A10_val_17_2_0 : A10 17 2 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_17_2_1 : A10 17 2 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_17_2_2 : A10 17 2 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_17_2 : b10 17 2 = (-5 : ℤ) := rfl
@[local simp] theorem A10_val_17_3_0 : A10 17 3 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_17_3_1 : A10 17 3 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_17_3_2 : A10 17 3 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_17_3 : b10 17 3 = (-1 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_17_0_0 : Work.Cusp.cubeXToKlein 17 0 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_17_0_1 : Work.Cusp.cubeXToKlein 17 0 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_17_0_2 : Work.Cusp.cubeXToKlein 17 0 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_17_0 : Work.Cusp.cubeXToKleinb 17 0 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_17_1_0 : Work.Cusp.cubeXToKlein 17 1 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_17_1_1 : Work.Cusp.cubeXToKlein 17 1 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_17_1_2 : Work.Cusp.cubeXToKlein 17 1 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_17_1 : Work.Cusp.cubeXToKleinb 17 1 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_17_2_0 : Work.Cusp.cubeXToKlein 17 2 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_17_2_1 : Work.Cusp.cubeXToKlein 17 2 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_17_2_2 : Work.Cusp.cubeXToKlein 17 2 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_17_2 : Work.Cusp.cubeXToKleinb 17 2 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_17_3_0 : Work.Cusp.cubeXToKlein 17 3 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_17_3_1 : Work.Cusp.cubeXToKlein 17 3 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_17_3_2 : Work.Cusp.cubeXToKlein 17 3 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_17_3 : Work.Cusp.cubeXToKleinb 17 3 = ((-1 : ℚ)/10) := rfl
@[local simp] theorem cubeVert_val_18 : Work.RTOwed.cubeVert 18 = (2 : Fin 24) := rfl
@[local simp] theorem cl_val_18_0 : cl 18 0 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_18_1 : cl 18 1 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_18_2 : cl 18 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_18_0_0 : A10 18 0 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_18_0_1 : A10 18 0 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_18_0_2 : A10 18 0 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_18_0 : b10 18 0 = (-5 : ℤ) := rfl
@[local simp] theorem A10_val_18_1_0 : A10 18 1 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_18_1_1 : A10 18 1 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_18_1_2 : A10 18 1 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_18_1 : b10 18 1 = (-5 : ℤ) := rfl
@[local simp] theorem A10_val_18_2_0 : A10 18 2 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_18_2_1 : A10 18 2 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_18_2_2 : A10 18 2 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_18_2 : b10 18 2 = (5 : ℤ) := rfl
@[local simp] theorem A10_val_18_3_0 : A10 18 3 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_18_3_1 : A10 18 3 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_18_3_2 : A10 18 3 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_18_3 : b10 18 3 = (-1 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_18_0_0 : Work.Cusp.cubeXToKlein 18 0 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_18_0_1 : Work.Cusp.cubeXToKlein 18 0 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_18_0_2 : Work.Cusp.cubeXToKlein 18 0 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_18_0 : Work.Cusp.cubeXToKleinb 18 0 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_18_1_0 : Work.Cusp.cubeXToKlein 18 1 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_18_1_1 : Work.Cusp.cubeXToKlein 18 1 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_18_1_2 : Work.Cusp.cubeXToKlein 18 1 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_18_1 : Work.Cusp.cubeXToKleinb 18 1 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_18_2_0 : Work.Cusp.cubeXToKlein 18 2 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_18_2_1 : Work.Cusp.cubeXToKlein 18 2 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_18_2_2 : Work.Cusp.cubeXToKlein 18 2 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_18_2 : Work.Cusp.cubeXToKleinb 18 2 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_18_3_0 : Work.Cusp.cubeXToKlein 18 3 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_18_3_1 : Work.Cusp.cubeXToKlein 18 3 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_18_3_2 : Work.Cusp.cubeXToKlein 18 3 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_18_3 : Work.Cusp.cubeXToKleinb 18 3 = ((-1 : ℚ)/10) := rfl
@[local simp] theorem cubeVert_val_19 : Work.RTOwed.cubeVert 19 = (15 : Fin 24) := rfl
@[local simp] theorem cl_val_19_0 : cl 19 0 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_19_1 : cl 19 1 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_19_2 : cl 19 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_19_0_0 : A10 19 0 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_19_0_1 : A10 19 0 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_19_0_2 : A10 19 0 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_19_0 : b10 19 0 = (5 : ℤ) := rfl
@[local simp] theorem A10_val_19_1_0 : A10 19 1 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_19_1_1 : A10 19 1 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_19_1_2 : A10 19 1 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_19_1 : b10 19 1 = (5 : ℤ) := rfl
@[local simp] theorem A10_val_19_2_0 : A10 19 2 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_19_2_1 : A10 19 2 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_19_2_2 : A10 19 2 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_19_2 : b10 19 2 = (5 : ℤ) := rfl
@[local simp] theorem A10_val_19_3_0 : A10 19 3 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_19_3_1 : A10 19 3 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_19_3_2 : A10 19 3 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_19_3 : b10 19 3 = (1 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_19_0_0 : Work.Cusp.cubeXToKlein 19 0 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_19_0_1 : Work.Cusp.cubeXToKlein 19 0 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_19_0_2 : Work.Cusp.cubeXToKlein 19 0 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_19_0 : Work.Cusp.cubeXToKleinb 19 0 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_19_1_0 : Work.Cusp.cubeXToKlein 19 1 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_19_1_1 : Work.Cusp.cubeXToKlein 19 1 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_19_1_2 : Work.Cusp.cubeXToKlein 19 1 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_19_1 : Work.Cusp.cubeXToKleinb 19 1 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_19_2_0 : Work.Cusp.cubeXToKlein 19 2 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_19_2_1 : Work.Cusp.cubeXToKlein 19 2 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_19_2_2 : Work.Cusp.cubeXToKlein 19 2 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_19_2 : Work.Cusp.cubeXToKleinb 19 2 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_19_3_0 : Work.Cusp.cubeXToKlein 19 3 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_19_3_1 : Work.Cusp.cubeXToKlein 19 3 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_19_3_2 : Work.Cusp.cubeXToKlein 19 3 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_19_3 : Work.Cusp.cubeXToKleinb 19 3 = ((1 : ℚ)/10) := rfl
@[local simp] theorem cubeVert_val_20 : Work.RTOwed.cubeVert 20 = (4 : Fin 24) := rfl
@[local simp] theorem cl_val_20_0 : cl 20 0 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_20_1 : cl 20 1 = (1 : ℤ) := rfl
@[local simp] theorem cl_val_20_2 : cl 20 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_20_0_0 : A10 20 0 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_20_0_1 : A10 20 0 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_20_0_2 : A10 20 0 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_20_0 : b10 20 0 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_20_1_0 : A10 20 1 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_20_1_1 : A10 20 1 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_20_1_2 : A10 20 1 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_20_1 : b10 20 1 = (9 : ℤ) := rfl
@[local simp] theorem A10_val_20_2_0 : A10 20 2 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_20_2_1 : A10 20 2 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_20_2_2 : A10 20 2 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_20_2 : b10 20 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_20_3_0 : A10 20 3 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_20_3_1 : A10 20 3 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_20_3_2 : A10 20 3 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_20_3 : b10 20 3 = (-5 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_20_0_0 : Work.Cusp.cubeXToKlein 20 0 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_20_0_1 : Work.Cusp.cubeXToKlein 20 0 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_20_0_2 : Work.Cusp.cubeXToKlein 20 0 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_20_0 : Work.Cusp.cubeXToKleinb 20 0 = ((-1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_20_1_0 : Work.Cusp.cubeXToKlein 20 1 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_20_1_1 : Work.Cusp.cubeXToKlein 20 1 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_20_1_2 : Work.Cusp.cubeXToKlein 20 1 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_20_1 : Work.Cusp.cubeXToKleinb 20 1 = ((9 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_20_2_0 : Work.Cusp.cubeXToKlein 20 2 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_20_2_1 : Work.Cusp.cubeXToKlein 20 2 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_20_2_2 : Work.Cusp.cubeXToKlein 20 2 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_20_2 : Work.Cusp.cubeXToKleinb 20 2 = ((-1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_20_3_0 : Work.Cusp.cubeXToKlein 20 3 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_20_3_1 : Work.Cusp.cubeXToKlein 20 3 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_20_3_2 : Work.Cusp.cubeXToKlein 20 3 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_20_3 : Work.Cusp.cubeXToKleinb 20 3 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeVert_val_21 : Work.RTOwed.cubeVert 21 = (1 : Fin 24) := rfl
@[local simp] theorem cl_val_21_0 : cl 21 0 = (1 : ℤ) := rfl
@[local simp] theorem cl_val_21_1 : cl 21 1 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_21_2 : cl 21 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_21_0_0 : A10 21 0 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_21_0_1 : A10 21 0 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_21_0_2 : A10 21 0 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_21_0 : b10 21 0 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_21_1_0 : A10 21 1 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_21_1_1 : A10 21 1 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_21_1_2 : A10 21 1 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_21_1 : b10 21 1 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_21_2_0 : A10 21 2 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_21_2_1 : A10 21 2 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_21_2_2 : A10 21 2 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_21_2 : b10 21 2 = (-9 : ℤ) := rfl
@[local simp] theorem A10_val_21_3_0 : A10 21 3 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_21_3_1 : A10 21 3 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_21_3_2 : A10 21 3 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_21_3 : b10 21 3 = (5 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_21_0_0 : Work.Cusp.cubeXToKlein 21 0 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_21_0_1 : Work.Cusp.cubeXToKlein 21 0 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_21_0_2 : Work.Cusp.cubeXToKlein 21 0 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_21_0 : Work.Cusp.cubeXToKleinb 21 0 = ((-1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_21_1_0 : Work.Cusp.cubeXToKlein 21 1 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_21_1_1 : Work.Cusp.cubeXToKlein 21 1 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_21_1_2 : Work.Cusp.cubeXToKlein 21 1 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_21_1 : Work.Cusp.cubeXToKleinb 21 1 = ((-1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_21_2_0 : Work.Cusp.cubeXToKlein 21 2 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_21_2_1 : Work.Cusp.cubeXToKlein 21 2 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_21_2_2 : Work.Cusp.cubeXToKlein 21 2 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_21_2 : Work.Cusp.cubeXToKleinb 21 2 = ((-9 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_21_3_0 : Work.Cusp.cubeXToKlein 21 3 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_21_3_1 : Work.Cusp.cubeXToKlein 21 3 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_21_3_2 : Work.Cusp.cubeXToKlein 21 3 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_21_3 : Work.Cusp.cubeXToKleinb 21 3 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeVert_val_22 : Work.RTOwed.cubeVert 22 = (10 : Fin 24) := rfl
@[local simp] theorem cl_val_22_0 : cl 22 0 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_22_1 : cl 22 1 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_22_2 : cl 22 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_22_0_0 : A10 22 0 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_22_0_1 : A10 22 0 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_22_0_2 : A10 22 0 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_22_0 : b10 22 0 = (5 : ℤ) := rfl
@[local simp] theorem A10_val_22_1_0 : A10 22 1 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_22_1_1 : A10 22 1 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_22_1_2 : A10 22 1 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_22_1 : b10 22 1 = (-5 : ℤ) := rfl
@[local simp] theorem A10_val_22_2_0 : A10 22 2 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_22_2_1 : A10 22 2 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_22_2_2 : A10 22 2 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_22_2 : b10 22 2 = (5 : ℤ) := rfl
@[local simp] theorem A10_val_22_3_0 : A10 22 3 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_22_3_1 : A10 22 3 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_22_3_2 : A10 22 3 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_22_3 : b10 22 3 = (-1 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_22_0_0 : Work.Cusp.cubeXToKlein 22 0 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_22_0_1 : Work.Cusp.cubeXToKlein 22 0 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_22_0_2 : Work.Cusp.cubeXToKlein 22 0 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_22_0 : Work.Cusp.cubeXToKleinb 22 0 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_22_1_0 : Work.Cusp.cubeXToKlein 22 1 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_22_1_1 : Work.Cusp.cubeXToKlein 22 1 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_22_1_2 : Work.Cusp.cubeXToKlein 22 1 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_22_1 : Work.Cusp.cubeXToKleinb 22 1 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_22_2_0 : Work.Cusp.cubeXToKlein 22 2 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_22_2_1 : Work.Cusp.cubeXToKlein 22 2 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_22_2_2 : Work.Cusp.cubeXToKlein 22 2 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_22_2 : Work.Cusp.cubeXToKleinb 22 2 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_22_3_0 : Work.Cusp.cubeXToKlein 22 3 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_22_3_1 : Work.Cusp.cubeXToKlein 22 3 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_22_3_2 : Work.Cusp.cubeXToKlein 22 3 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_22_3 : Work.Cusp.cubeXToKleinb 22 3 = ((-1 : ℚ)/10) := rfl
@[local simp] theorem cubeVert_val_23 : Work.RTOwed.cubeVert 23 = (7 : Fin 24) := rfl
@[local simp] theorem cl_val_23_0 : cl 23 0 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_23_1 : cl 23 1 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_23_2 : cl 23 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_23_0_0 : A10 23 0 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_23_0_1 : A10 23 0 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_23_0_2 : A10 23 0 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_23_0 : b10 23 0 = (-5 : ℤ) := rfl
@[local simp] theorem A10_val_23_1_0 : A10 23 1 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_23_1_1 : A10 23 1 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_23_1_2 : A10 23 1 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_23_1 : b10 23 1 = (5 : ℤ) := rfl
@[local simp] theorem A10_val_23_2_0 : A10 23 2 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_23_2_1 : A10 23 2 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_23_2_2 : A10 23 2 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_23_2 : b10 23 2 = (5 : ℤ) := rfl
@[local simp] theorem A10_val_23_3_0 : A10 23 3 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_23_3_1 : A10 23 3 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_23_3_2 : A10 23 3 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_23_3 : b10 23 3 = (1 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_23_0_0 : Work.Cusp.cubeXToKlein 23 0 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_23_0_1 : Work.Cusp.cubeXToKlein 23 0 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_23_0_2 : Work.Cusp.cubeXToKlein 23 0 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_23_0 : Work.Cusp.cubeXToKleinb 23 0 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_23_1_0 : Work.Cusp.cubeXToKlein 23 1 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_23_1_1 : Work.Cusp.cubeXToKlein 23 1 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_23_1_2 : Work.Cusp.cubeXToKlein 23 1 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_23_1 : Work.Cusp.cubeXToKleinb 23 1 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_23_2_0 : Work.Cusp.cubeXToKlein 23 2 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_23_2_1 : Work.Cusp.cubeXToKlein 23 2 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_23_2_2 : Work.Cusp.cubeXToKlein 23 2 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_23_2 : Work.Cusp.cubeXToKleinb 23 2 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_23_3_0 : Work.Cusp.cubeXToKlein 23 3 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_23_3_1 : Work.Cusp.cubeXToKlein 23 3 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_23_3_2 : Work.Cusp.cubeXToKlein 23 3 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_23_3 : Work.Cusp.cubeXToKleinb 23 3 = ((1 : ℚ)/10) := rfl
@[local simp] theorem cubeVert_val_24 : Work.RTOwed.cubeVert 24 = (12 : Fin 24) := rfl
@[local simp] theorem cl_val_24_0 : cl 24 0 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_24_1 : cl 24 1 = (1 : ℤ) := rfl
@[local simp] theorem cl_val_24_2 : cl 24 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_24_0_0 : A10 24 0 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_24_0_1 : A10 24 0 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_24_0_2 : A10 24 0 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_24_0 : b10 24 0 = (1 : ℤ) := rfl
@[local simp] theorem A10_val_24_1_0 : A10 24 1 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_24_1_1 : A10 24 1 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_24_1_2 : A10 24 1 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_24_1 : b10 24 1 = (9 : ℤ) := rfl
@[local simp] theorem A10_val_24_2_0 : A10 24 2 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_24_2_1 : A10 24 2 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_24_2_2 : A10 24 2 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_24_2 : b10 24 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_24_3_0 : A10 24 3 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_24_3_1 : A10 24 3 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_24_3_2 : A10 24 3 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_24_3 : b10 24 3 = (-5 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_24_0_0 : Work.Cusp.cubeXToKlein 24 0 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_24_0_1 : Work.Cusp.cubeXToKlein 24 0 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_24_0_2 : Work.Cusp.cubeXToKlein 24 0 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_24_0 : Work.Cusp.cubeXToKleinb 24 0 = ((1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_24_1_0 : Work.Cusp.cubeXToKlein 24 1 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_24_1_1 : Work.Cusp.cubeXToKlein 24 1 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_24_1_2 : Work.Cusp.cubeXToKlein 24 1 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_24_1 : Work.Cusp.cubeXToKleinb 24 1 = ((9 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_24_2_0 : Work.Cusp.cubeXToKlein 24 2 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_24_2_1 : Work.Cusp.cubeXToKlein 24 2 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_24_2_2 : Work.Cusp.cubeXToKlein 24 2 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_24_2 : Work.Cusp.cubeXToKleinb 24 2 = ((-1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_24_3_0 : Work.Cusp.cubeXToKlein 24 3 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_24_3_1 : Work.Cusp.cubeXToKlein 24 3 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_24_3_2 : Work.Cusp.cubeXToKlein 24 3 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_24_3 : Work.Cusp.cubeXToKleinb 24 3 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeVert_val_25 : Work.RTOwed.cubeVert 25 = (9 : Fin 24) := rfl
@[local simp] theorem cl_val_25_0 : cl 25 0 = (-2 : ℤ) := rfl
@[local simp] theorem cl_val_25_1 : cl 25 1 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_25_2 : cl 25 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_25_0_0 : A10 25 0 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_25_0_1 : A10 25 0 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_25_0_2 : A10 25 0 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_25_0 : b10 25 0 = (1 : ℤ) := rfl
@[local simp] theorem A10_val_25_1_0 : A10 25 1 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_25_1_1 : A10 25 1 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_25_1_2 : A10 25 1 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_25_1 : b10 25 1 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_25_2_0 : A10 25 2 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_25_2_1 : A10 25 2 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_25_2_2 : A10 25 2 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_25_2 : b10 25 2 = (-9 : ℤ) := rfl
@[local simp] theorem A10_val_25_3_0 : A10 25 3 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_25_3_1 : A10 25 3 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_25_3_2 : A10 25 3 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_25_3 : b10 25 3 = (5 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_25_0_0 : Work.Cusp.cubeXToKlein 25 0 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_25_0_1 : Work.Cusp.cubeXToKlein 25 0 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_25_0_2 : Work.Cusp.cubeXToKlein 25 0 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_25_0 : Work.Cusp.cubeXToKleinb 25 0 = ((1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_25_1_0 : Work.Cusp.cubeXToKlein 25 1 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_25_1_1 : Work.Cusp.cubeXToKlein 25 1 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_25_1_2 : Work.Cusp.cubeXToKlein 25 1 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_25_1 : Work.Cusp.cubeXToKleinb 25 1 = ((-1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_25_2_0 : Work.Cusp.cubeXToKlein 25 2 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_25_2_1 : Work.Cusp.cubeXToKlein 25 2 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_25_2_2 : Work.Cusp.cubeXToKlein 25 2 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_25_2 : Work.Cusp.cubeXToKleinb 25 2 = ((-9 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_25_3_0 : Work.Cusp.cubeXToKlein 25 3 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_25_3_1 : Work.Cusp.cubeXToKlein 25 3 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_25_3_2 : Work.Cusp.cubeXToKlein 25 3 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_25_3 : Work.Cusp.cubeXToKleinb 25 3 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeVert_val_26 : Work.RTOwed.cubeVert 26 = (13 : Fin 24) := rfl
@[local simp] theorem cl_val_26_0 : cl 26 0 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_26_1 : cl 26 1 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_26_2 : cl 26 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_26_0_0 : A10 26 0 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_26_0_1 : A10 26 0 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_26_0_2 : A10 26 0 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_26_0 : b10 26 0 = (5 : ℤ) := rfl
@[local simp] theorem A10_val_26_1_0 : A10 26 1 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_26_1_1 : A10 26 1 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_26_1_2 : A10 26 1 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_26_1 : b10 26 1 = (5 : ℤ) := rfl
@[local simp] theorem A10_val_26_2_0 : A10 26 2 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_26_2_1 : A10 26 2 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_26_2_2 : A10 26 2 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_26_2 : b10 26 2 = (-5 : ℤ) := rfl
@[local simp] theorem A10_val_26_3_0 : A10 26 3 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_26_3_1 : A10 26 3 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_26_3_2 : A10 26 3 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_26_3 : b10 26 3 = (1 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_26_0_0 : Work.Cusp.cubeXToKlein 26 0 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_26_0_1 : Work.Cusp.cubeXToKlein 26 0 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_26_0_2 : Work.Cusp.cubeXToKlein 26 0 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_26_0 : Work.Cusp.cubeXToKleinb 26 0 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_26_1_0 : Work.Cusp.cubeXToKlein 26 1 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_26_1_1 : Work.Cusp.cubeXToKlein 26 1 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_26_1_2 : Work.Cusp.cubeXToKlein 26 1 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_26_1 : Work.Cusp.cubeXToKleinb 26 1 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_26_2_0 : Work.Cusp.cubeXToKlein 26 2 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_26_2_1 : Work.Cusp.cubeXToKlein 26 2 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_26_2_2 : Work.Cusp.cubeXToKlein 26 2 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_26_2 : Work.Cusp.cubeXToKleinb 26 2 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_26_3_0 : Work.Cusp.cubeXToKlein 26 3 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_26_3_1 : Work.Cusp.cubeXToKlein 26 3 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_26_3_2 : Work.Cusp.cubeXToKlein 26 3 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_26_3 : Work.Cusp.cubeXToKleinb 26 3 = ((1 : ℚ)/10) := rfl
@[local simp] theorem cubeVert_val_27 : Work.RTOwed.cubeVert 27 = (6 : Fin 24) := rfl
@[local simp] theorem cl_val_27_0 : cl 27 0 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_27_1 : cl 27 1 = (-2 : ℤ) := rfl
@[local simp] theorem cl_val_27_2 : cl 27 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_27_0_0 : A10 27 0 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_27_0_1 : A10 27 0 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_27_0_2 : A10 27 0 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_27_0 : b10 27 0 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_27_1_0 : A10 27 1 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_27_1_1 : A10 27 1 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_27_1_2 : A10 27 1 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_27_1 : b10 27 1 = (9 : ℤ) := rfl
@[local simp] theorem A10_val_27_2_0 : A10 27 2 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_27_2_1 : A10 27 2 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_27_2_2 : A10 27 2 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_27_2 : b10 27 2 = (1 : ℤ) := rfl
@[local simp] theorem A10_val_27_3_0 : A10 27 3 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_27_3_1 : A10 27 3 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_27_3_2 : A10 27 3 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_27_3 : b10 27 3 = (-5 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_27_0_0 : Work.Cusp.cubeXToKlein 27 0 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_27_0_1 : Work.Cusp.cubeXToKlein 27 0 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_27_0_2 : Work.Cusp.cubeXToKlein 27 0 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_27_0 : Work.Cusp.cubeXToKleinb 27 0 = ((-1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_27_1_0 : Work.Cusp.cubeXToKlein 27 1 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_27_1_1 : Work.Cusp.cubeXToKlein 27 1 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_27_1_2 : Work.Cusp.cubeXToKlein 27 1 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_27_1 : Work.Cusp.cubeXToKleinb 27 1 = ((9 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_27_2_0 : Work.Cusp.cubeXToKlein 27 2 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_27_2_1 : Work.Cusp.cubeXToKlein 27 2 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_27_2_2 : Work.Cusp.cubeXToKlein 27 2 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_27_2 : Work.Cusp.cubeXToKleinb 27 2 = ((1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_27_3_0 : Work.Cusp.cubeXToKlein 27 3 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_27_3_1 : Work.Cusp.cubeXToKlein 27 3 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_27_3_2 : Work.Cusp.cubeXToKlein 27 3 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_27_3 : Work.Cusp.cubeXToKleinb 27 3 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeVert_val_28 : Work.RTOwed.cubeVert 28 = (3 : Fin 24) := rfl
@[local simp] theorem cl_val_28_0 : cl 28 0 = (1 : ℤ) := rfl
@[local simp] theorem cl_val_28_1 : cl 28 1 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_28_2 : cl 28 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_28_0_0 : A10 28 0 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_28_0_1 : A10 28 0 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_28_0_2 : A10 28 0 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_28_0 : b10 28 0 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_28_1_0 : A10 28 1 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_28_1_1 : A10 28 1 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_28_1_2 : A10 28 1 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_28_1 : b10 28 1 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_28_2_0 : A10 28 2 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_28_2_1 : A10 28 2 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_28_2_2 : A10 28 2 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_28_2 : b10 28 2 = (9 : ℤ) := rfl
@[local simp] theorem A10_val_28_3_0 : A10 28 3 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_28_3_1 : A10 28 3 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_28_3_2 : A10 28 3 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_28_3 : b10 28 3 = (5 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_28_0_0 : Work.Cusp.cubeXToKlein 28 0 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_28_0_1 : Work.Cusp.cubeXToKlein 28 0 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_28_0_2 : Work.Cusp.cubeXToKlein 28 0 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_28_0 : Work.Cusp.cubeXToKleinb 28 0 = ((-1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_28_1_0 : Work.Cusp.cubeXToKlein 28 1 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_28_1_1 : Work.Cusp.cubeXToKlein 28 1 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_28_1_2 : Work.Cusp.cubeXToKlein 28 1 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_28_1 : Work.Cusp.cubeXToKleinb 28 1 = ((-1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_28_2_0 : Work.Cusp.cubeXToKlein 28 2 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_28_2_1 : Work.Cusp.cubeXToKlein 28 2 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_28_2_2 : Work.Cusp.cubeXToKlein 28 2 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_28_2 : Work.Cusp.cubeXToKleinb 28 2 = ((9 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_28_3_0 : Work.Cusp.cubeXToKlein 28 3 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_28_3_1 : Work.Cusp.cubeXToKlein 28 3 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_28_3_2 : Work.Cusp.cubeXToKlein 28 3 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_28_3 : Work.Cusp.cubeXToKleinb 28 3 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeVert_val_29 : Work.RTOwed.cubeVert 29 = (11 : Fin 24) := rfl
@[local simp] theorem cl_val_29_0 : cl 29 0 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_29_1 : cl 29 1 = (1 : ℤ) := rfl
@[local simp] theorem cl_val_29_2 : cl 29 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_29_0_0 : A10 29 0 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_29_0_1 : A10 29 0 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_29_0_2 : A10 29 0 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_29_0 : b10 29 0 = (1 : ℤ) := rfl
@[local simp] theorem A10_val_29_1_0 : A10 29 1 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_29_1_1 : A10 29 1 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_29_1_2 : A10 29 1 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_29_1 : b10 29 1 = (-9 : ℤ) := rfl
@[local simp] theorem A10_val_29_2_0 : A10 29 2 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_29_2_1 : A10 29 2 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_29_2_2 : A10 29 2 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_29_2 : b10 29 2 = (1 : ℤ) := rfl
@[local simp] theorem A10_val_29_3_0 : A10 29 3 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_29_3_1 : A10 29 3 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_29_3_2 : A10 29 3 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_29_3 : b10 29 3 = (5 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_29_0_0 : Work.Cusp.cubeXToKlein 29 0 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_29_0_1 : Work.Cusp.cubeXToKlein 29 0 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_29_0_2 : Work.Cusp.cubeXToKlein 29 0 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_29_0 : Work.Cusp.cubeXToKleinb 29 0 = ((1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_29_1_0 : Work.Cusp.cubeXToKlein 29 1 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_29_1_1 : Work.Cusp.cubeXToKlein 29 1 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_29_1_2 : Work.Cusp.cubeXToKlein 29 1 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_29_1 : Work.Cusp.cubeXToKleinb 29 1 = ((-9 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_29_2_0 : Work.Cusp.cubeXToKlein 29 2 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_29_2_1 : Work.Cusp.cubeXToKlein 29 2 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_29_2_2 : Work.Cusp.cubeXToKlein 29 2 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_29_2 : Work.Cusp.cubeXToKleinb 29 2 = ((1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_29_3_0 : Work.Cusp.cubeXToKlein 29 3 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_29_3_1 : Work.Cusp.cubeXToKlein 29 3 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_29_3_2 : Work.Cusp.cubeXToKlein 29 3 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_29_3 : Work.Cusp.cubeXToKleinb 29 3 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeVert_val_30 : Work.RTOwed.cubeVert 30 = (14 : Fin 24) := rfl
@[local simp] theorem cl_val_30_0 : cl 30 0 = (1 : ℤ) := rfl
@[local simp] theorem cl_val_30_1 : cl 30 1 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_30_2 : cl 30 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_30_0_0 : A10 30 0 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_30_0_1 : A10 30 0 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_30_0_2 : A10 30 0 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_30_0 : b10 30 0 = (1 : ℤ) := rfl
@[local simp] theorem A10_val_30_1_0 : A10 30 1 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_30_1_1 : A10 30 1 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_30_1_2 : A10 30 1 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_30_1 : b10 30 1 = (1 : ℤ) := rfl
@[local simp] theorem A10_val_30_2_0 : A10 30 2 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_30_2_1 : A10 30 2 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_30_2_2 : A10 30 2 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_30_2 : b10 30 2 = (9 : ℤ) := rfl
@[local simp] theorem A10_val_30_3_0 : A10 30 3 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_30_3_1 : A10 30 3 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_30_3_2 : A10 30 3 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_30_3 : b10 30 3 = (-5 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_30_0_0 : Work.Cusp.cubeXToKlein 30 0 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_30_0_1 : Work.Cusp.cubeXToKlein 30 0 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_30_0_2 : Work.Cusp.cubeXToKlein 30 0 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_30_0 : Work.Cusp.cubeXToKleinb 30 0 = ((1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_30_1_0 : Work.Cusp.cubeXToKlein 30 1 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_30_1_1 : Work.Cusp.cubeXToKlein 30 1 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_30_1_2 : Work.Cusp.cubeXToKlein 30 1 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_30_1 : Work.Cusp.cubeXToKleinb 30 1 = ((1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_30_2_0 : Work.Cusp.cubeXToKlein 30 2 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_30_2_1 : Work.Cusp.cubeXToKlein 30 2 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_30_2_2 : Work.Cusp.cubeXToKlein 30 2 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_30_2 : Work.Cusp.cubeXToKleinb 30 2 = ((9 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_30_3_0 : Work.Cusp.cubeXToKlein 30 3 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_30_3_1 : Work.Cusp.cubeXToKlein 30 3 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_30_3_2 : Work.Cusp.cubeXToKlein 30 3 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_30_3 : Work.Cusp.cubeXToKleinb 30 3 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeVert_val_31 : Work.RTOwed.cubeVert 31 = (5 : Fin 24) := rfl
@[local simp] theorem cl_val_31_0 : cl 31 0 = (1 : ℤ) := rfl
@[local simp] theorem cl_val_31_1 : cl 31 1 = (1 : ℤ) := rfl
@[local simp] theorem cl_val_31_2 : cl 31 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_31_0_0 : A10 31 0 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_31_0_1 : A10 31 0 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_31_0_2 : A10 31 0 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_31_0 : b10 31 0 = (3 : ℤ) := rfl
@[local simp] theorem A10_val_31_1_0 : A10 31 1 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_31_1_1 : A10 31 1 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_31_1_2 : A10 31 1 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_31_1 : b10 31 1 = (5 : ℤ) := rfl
@[local simp] theorem A10_val_31_2_0 : A10 31 2 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_31_2_1 : A10 31 2 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_31_2_2 : A10 31 2 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_31_2 : b10 31 2 = (-5 : ℤ) := rfl
@[local simp] theorem A10_val_31_3_0 : A10 31 3 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_31_3_1 : A10 31 3 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_31_3_2 : A10 31 3 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_31_3 : b10 31 3 = (9 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_31_0_0 : Work.Cusp.cubeXToKlein 31 0 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_31_0_1 : Work.Cusp.cubeXToKlein 31 0 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_31_0_2 : Work.Cusp.cubeXToKlein 31 0 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_31_0 : Work.Cusp.cubeXToKleinb 31 0 = ((3 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_31_1_0 : Work.Cusp.cubeXToKlein 31 1 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_31_1_1 : Work.Cusp.cubeXToKlein 31 1 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_31_1_2 : Work.Cusp.cubeXToKlein 31 1 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_31_1 : Work.Cusp.cubeXToKleinb 31 1 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_31_2_0 : Work.Cusp.cubeXToKlein 31 2 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_31_2_1 : Work.Cusp.cubeXToKlein 31 2 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_31_2_2 : Work.Cusp.cubeXToKlein 31 2 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_31_2 : Work.Cusp.cubeXToKleinb 31 2 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_31_3_0 : Work.Cusp.cubeXToKlein 31 3 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_31_3_1 : Work.Cusp.cubeXToKlein 31 3 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_31_3_2 : Work.Cusp.cubeXToKlein 31 3 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_31_3 : Work.Cusp.cubeXToKleinb 31 3 = ((9 : ℚ)/10) := rfl
@[local simp] theorem cubeVert_val_32 : Work.RTOwed.cubeVert 32 = (5 : Fin 24) := rfl
@[local simp] theorem cl_val_32_0 : cl 32 0 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_32_1 : cl 32 1 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_32_2 : cl 32 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_32_0_0 : A10 32 0 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_32_0_1 : A10 32 0 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_32_0_2 : A10 32 0 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_32_0 : b10 32 0 = (-5 : ℤ) := rfl
@[local simp] theorem A10_val_32_1_0 : A10 32 1 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_32_1_1 : A10 32 1 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_32_1_2 : A10 32 1 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_32_1 : b10 32 1 = (5 : ℤ) := rfl
@[local simp] theorem A10_val_32_2_0 : A10 32 2 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_32_2_1 : A10 32 2 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_32_2_2 : A10 32 2 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_32_2 : b10 32 2 = (-5 : ℤ) := rfl
@[local simp] theorem A10_val_32_3_0 : A10 32 3 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_32_3_1 : A10 32 3 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_32_3_2 : A10 32 3 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_32_3 : b10 32 3 = (1 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_32_0_0 : Work.Cusp.cubeXToKlein 32 0 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_32_0_1 : Work.Cusp.cubeXToKlein 32 0 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_32_0_2 : Work.Cusp.cubeXToKlein 32 0 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_32_0 : Work.Cusp.cubeXToKleinb 32 0 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_32_1_0 : Work.Cusp.cubeXToKlein 32 1 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_32_1_1 : Work.Cusp.cubeXToKlein 32 1 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_32_1_2 : Work.Cusp.cubeXToKlein 32 1 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_32_1 : Work.Cusp.cubeXToKleinb 32 1 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_32_2_0 : Work.Cusp.cubeXToKlein 32 2 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_32_2_1 : Work.Cusp.cubeXToKlein 32 2 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_32_2_2 : Work.Cusp.cubeXToKlein 32 2 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_32_2 : Work.Cusp.cubeXToKleinb 32 2 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_32_3_0 : Work.Cusp.cubeXToKlein 32 3 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_32_3_1 : Work.Cusp.cubeXToKlein 32 3 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_32_3_2 : Work.Cusp.cubeXToKlein 32 3 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_32_3 : Work.Cusp.cubeXToKleinb 32 3 = ((1 : ℚ)/10) := rfl
@[local simp] theorem cubeVert_val_33 : Work.RTOwed.cubeVert 33 = (14 : Fin 24) := rfl
@[local simp] theorem cl_val_33_0 : cl 33 0 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_33_1 : cl 33 1 = (-2 : ℤ) := rfl
@[local simp] theorem cl_val_33_2 : cl 33 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_33_0_0 : A10 33 0 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_33_0_1 : A10 33 0 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_33_0_2 : A10 33 0 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_33_0 : b10 33 0 = (1 : ℤ) := rfl
@[local simp] theorem A10_val_33_1_0 : A10 33 1 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_33_1_1 : A10 33 1 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_33_1_2 : A10 33 1 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_33_1 : b10 33 1 = (9 : ℤ) := rfl
@[local simp] theorem A10_val_33_2_0 : A10 33 2 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_33_2_1 : A10 33 2 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_33_2_2 : A10 33 2 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_33_2 : b10 33 2 = (1 : ℤ) := rfl
@[local simp] theorem A10_val_33_3_0 : A10 33 3 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_33_3_1 : A10 33 3 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_33_3_2 : A10 33 3 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_33_3 : b10 33 3 = (-5 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_33_0_0 : Work.Cusp.cubeXToKlein 33 0 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_33_0_1 : Work.Cusp.cubeXToKlein 33 0 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_33_0_2 : Work.Cusp.cubeXToKlein 33 0 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_33_0 : Work.Cusp.cubeXToKleinb 33 0 = ((1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_33_1_0 : Work.Cusp.cubeXToKlein 33 1 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_33_1_1 : Work.Cusp.cubeXToKlein 33 1 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_33_1_2 : Work.Cusp.cubeXToKlein 33 1 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_33_1 : Work.Cusp.cubeXToKleinb 33 1 = ((9 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_33_2_0 : Work.Cusp.cubeXToKlein 33 2 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_33_2_1 : Work.Cusp.cubeXToKlein 33 2 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_33_2_2 : Work.Cusp.cubeXToKlein 33 2 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_33_2 : Work.Cusp.cubeXToKleinb 33 2 = ((1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_33_3_0 : Work.Cusp.cubeXToKlein 33 3 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_33_3_1 : Work.Cusp.cubeXToKlein 33 3 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_33_3_2 : Work.Cusp.cubeXToKlein 33 3 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_33_3 : Work.Cusp.cubeXToKleinb 33 3 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeVert_val_34 : Work.RTOwed.cubeVert 34 = (11 : Fin 24) := rfl
@[local simp] theorem cl_val_34_0 : cl 34 0 = (-2 : ℤ) := rfl
@[local simp] theorem cl_val_34_1 : cl 34 1 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_34_2 : cl 34 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_34_0_0 : A10 34 0 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_34_0_1 : A10 34 0 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_34_0_2 : A10 34 0 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_34_0 : b10 34 0 = (1 : ℤ) := rfl
@[local simp] theorem A10_val_34_1_0 : A10 34 1 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_34_1_1 : A10 34 1 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_34_1_2 : A10 34 1 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_34_1 : b10 34 1 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_34_2_0 : A10 34 2 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_34_2_1 : A10 34 2 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_34_2_2 : A10 34 2 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_34_2 : b10 34 2 = (9 : ℤ) := rfl
@[local simp] theorem A10_val_34_3_0 : A10 34 3 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_34_3_1 : A10 34 3 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_34_3_2 : A10 34 3 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_34_3 : b10 34 3 = (5 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_34_0_0 : Work.Cusp.cubeXToKlein 34 0 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_34_0_1 : Work.Cusp.cubeXToKlein 34 0 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_34_0_2 : Work.Cusp.cubeXToKlein 34 0 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_34_0 : Work.Cusp.cubeXToKleinb 34 0 = ((1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_34_1_0 : Work.Cusp.cubeXToKlein 34 1 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_34_1_1 : Work.Cusp.cubeXToKlein 34 1 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_34_1_2 : Work.Cusp.cubeXToKlein 34 1 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_34_1 : Work.Cusp.cubeXToKleinb 34 1 = ((-1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_34_2_0 : Work.Cusp.cubeXToKlein 34 2 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_34_2_1 : Work.Cusp.cubeXToKlein 34 2 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_34_2_2 : Work.Cusp.cubeXToKlein 34 2 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_34_2 : Work.Cusp.cubeXToKleinb 34 2 = ((9 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_34_3_0 : Work.Cusp.cubeXToKlein 34 3 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_34_3_1 : Work.Cusp.cubeXToKlein 34 3 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_34_3_2 : Work.Cusp.cubeXToKlein 34 3 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_34_3 : Work.Cusp.cubeXToKleinb 34 3 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeVert_val_35 : Work.RTOwed.cubeVert 35 = (3 : Fin 24) := rfl
@[local simp] theorem cl_val_35_0 : cl 35 0 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_35_1 : cl 35 1 = (1 : ℤ) := rfl
@[local simp] theorem cl_val_35_2 : cl 35 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_35_0_0 : A10 35 0 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_35_0_1 : A10 35 0 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_35_0_2 : A10 35 0 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_35_0 : b10 35 0 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_35_1_0 : A10 35 1 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_35_1_1 : A10 35 1 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_35_1_2 : A10 35 1 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_35_1 : b10 35 1 = (-9 : ℤ) := rfl
@[local simp] theorem A10_val_35_2_0 : A10 35 2 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_35_2_1 : A10 35 2 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_35_2_2 : A10 35 2 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_35_2 : b10 35 2 = (1 : ℤ) := rfl
@[local simp] theorem A10_val_35_3_0 : A10 35 3 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_35_3_1 : A10 35 3 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_35_3_2 : A10 35 3 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_35_3 : b10 35 3 = (5 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_35_0_0 : Work.Cusp.cubeXToKlein 35 0 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_35_0_1 : Work.Cusp.cubeXToKlein 35 0 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_35_0_2 : Work.Cusp.cubeXToKlein 35 0 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_35_0 : Work.Cusp.cubeXToKleinb 35 0 = ((-1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_35_1_0 : Work.Cusp.cubeXToKlein 35 1 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_35_1_1 : Work.Cusp.cubeXToKlein 35 1 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_35_1_2 : Work.Cusp.cubeXToKlein 35 1 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_35_1 : Work.Cusp.cubeXToKleinb 35 1 = ((-9 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_35_2_0 : Work.Cusp.cubeXToKlein 35 2 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_35_2_1 : Work.Cusp.cubeXToKlein 35 2 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_35_2_2 : Work.Cusp.cubeXToKlein 35 2 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_35_2 : Work.Cusp.cubeXToKleinb 35 2 = ((1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_35_3_0 : Work.Cusp.cubeXToKlein 35 3 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_35_3_1 : Work.Cusp.cubeXToKlein 35 3 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_35_3_2 : Work.Cusp.cubeXToKlein 35 3 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_35_3 : Work.Cusp.cubeXToKleinb 35 3 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeVert_val_36 : Work.RTOwed.cubeVert 36 = (6 : Fin 24) := rfl
@[local simp] theorem cl_val_36_0 : cl 36 0 = (-2 : ℤ) := rfl
@[local simp] theorem cl_val_36_1 : cl 36 1 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_36_2 : cl 36 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_36_0_0 : A10 36 0 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_36_0_1 : A10 36 0 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_36_0_2 : A10 36 0 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_36_0 : b10 36 0 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_36_1_0 : A10 36 1 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_36_1_1 : A10 36 1 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_36_1_2 : A10 36 1 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_36_1 : b10 36 1 = (1 : ℤ) := rfl
@[local simp] theorem A10_val_36_2_0 : A10 36 2 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_36_2_1 : A10 36 2 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_36_2_2 : A10 36 2 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_36_2 : b10 36 2 = (9 : ℤ) := rfl
@[local simp] theorem A10_val_36_3_0 : A10 36 3 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_36_3_1 : A10 36 3 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_36_3_2 : A10 36 3 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_36_3 : b10 36 3 = (-5 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_36_0_0 : Work.Cusp.cubeXToKlein 36 0 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_36_0_1 : Work.Cusp.cubeXToKlein 36 0 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_36_0_2 : Work.Cusp.cubeXToKlein 36 0 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_36_0 : Work.Cusp.cubeXToKleinb 36 0 = ((-1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_36_1_0 : Work.Cusp.cubeXToKlein 36 1 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_36_1_1 : Work.Cusp.cubeXToKlein 36 1 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_36_1_2 : Work.Cusp.cubeXToKlein 36 1 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_36_1 : Work.Cusp.cubeXToKleinb 36 1 = ((1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_36_2_0 : Work.Cusp.cubeXToKlein 36 2 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_36_2_1 : Work.Cusp.cubeXToKlein 36 2 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_36_2_2 : Work.Cusp.cubeXToKlein 36 2 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_36_2 : Work.Cusp.cubeXToKleinb 36 2 = ((9 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_36_3_0 : Work.Cusp.cubeXToKlein 36 3 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_36_3_1 : Work.Cusp.cubeXToKlein 36 3 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_36_3_2 : Work.Cusp.cubeXToKlein 36 3 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_36_3 : Work.Cusp.cubeXToKleinb 36 3 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeVert_val_37 : Work.RTOwed.cubeVert 37 = (13 : Fin 24) := rfl
@[local simp] theorem cl_val_37_0 : cl 37 0 = (-2 : ℤ) := rfl
@[local simp] theorem cl_val_37_1 : cl 37 1 = (1 : ℤ) := rfl
@[local simp] theorem cl_val_37_2 : cl 37 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_37_0_0 : A10 37 0 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_37_0_1 : A10 37 0 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_37_0_2 : A10 37 0 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_37_0 : b10 37 0 = (-3 : ℤ) := rfl
@[local simp] theorem A10_val_37_1_0 : A10 37 1 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_37_1_1 : A10 37 1 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_37_1_2 : A10 37 1 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_37_1 : b10 37 1 = (5 : ℤ) := rfl
@[local simp] theorem A10_val_37_2_0 : A10 37 2 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_37_2_1 : A10 37 2 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_37_2_2 : A10 37 2 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_37_2 : b10 37 2 = (-5 : ℤ) := rfl
@[local simp] theorem A10_val_37_3_0 : A10 37 3 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_37_3_1 : A10 37 3 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_37_3_2 : A10 37 3 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_37_3 : b10 37 3 = (9 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_37_0_0 : Work.Cusp.cubeXToKlein 37 0 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_37_0_1 : Work.Cusp.cubeXToKlein 37 0 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_37_0_2 : Work.Cusp.cubeXToKlein 37 0 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_37_0 : Work.Cusp.cubeXToKleinb 37 0 = ((-3 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_37_1_0 : Work.Cusp.cubeXToKlein 37 1 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_37_1_1 : Work.Cusp.cubeXToKlein 37 1 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_37_1_2 : Work.Cusp.cubeXToKlein 37 1 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_37_1 : Work.Cusp.cubeXToKleinb 37 1 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_37_2_0 : Work.Cusp.cubeXToKlein 37 2 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_37_2_1 : Work.Cusp.cubeXToKlein 37 2 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_37_2_2 : Work.Cusp.cubeXToKlein 37 2 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_37_2 : Work.Cusp.cubeXToKleinb 37 2 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_37_3_0 : Work.Cusp.cubeXToKlein 37 3 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_37_3_1 : Work.Cusp.cubeXToKlein 37 3 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_37_3_2 : Work.Cusp.cubeXToKlein 37 3 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_37_3 : Work.Cusp.cubeXToKleinb 37 3 = ((9 : ℚ)/10) := rfl
@[local simp] theorem cubeVert_val_38 : Work.RTOwed.cubeVert 38 = (9 : Fin 24) := rfl
@[local simp] theorem cl_val_38_0 : cl 38 0 = (0 : ℤ) := rfl
@[local simp] theorem cl_val_38_1 : cl 38 1 = (-2 : ℤ) := rfl
@[local simp] theorem cl_val_38_2 : cl 38 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_38_0_0 : A10 38 0 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_38_0_1 : A10 38 0 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_38_0_2 : A10 38 0 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_38_0 : b10 38 0 = (1 : ℤ) := rfl
@[local simp] theorem A10_val_38_1_0 : A10 38 1 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_38_1_1 : A10 38 1 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_38_1_2 : A10 38 1 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_38_1 : b10 38 1 = (-9 : ℤ) := rfl
@[local simp] theorem A10_val_38_2_0 : A10 38 2 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_38_2_1 : A10 38 2 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_38_2_2 : A10 38 2 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_38_2 : b10 38 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_38_3_0 : A10 38 3 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_38_3_1 : A10 38 3 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_38_3_2 : A10 38 3 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_38_3 : b10 38 3 = (5 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_38_0_0 : Work.Cusp.cubeXToKlein 38 0 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_38_0_1 : Work.Cusp.cubeXToKlein 38 0 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_38_0_2 : Work.Cusp.cubeXToKlein 38 0 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_38_0 : Work.Cusp.cubeXToKleinb 38 0 = ((1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_38_1_0 : Work.Cusp.cubeXToKlein 38 1 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_38_1_1 : Work.Cusp.cubeXToKlein 38 1 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_38_1_2 : Work.Cusp.cubeXToKlein 38 1 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_38_1 : Work.Cusp.cubeXToKleinb 38 1 = ((-9 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_38_2_0 : Work.Cusp.cubeXToKlein 38 2 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_38_2_1 : Work.Cusp.cubeXToKlein 38 2 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_38_2_2 : Work.Cusp.cubeXToKlein 38 2 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_38_2 : Work.Cusp.cubeXToKleinb 38 2 = ((-1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_38_3_0 : Work.Cusp.cubeXToKlein 38 3 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_38_3_1 : Work.Cusp.cubeXToKlein 38 3 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_38_3_2 : Work.Cusp.cubeXToKlein 38 3 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_38_3 : Work.Cusp.cubeXToKleinb 38 3 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeVert_val_39 : Work.RTOwed.cubeVert 39 = (12 : Fin 24) := rfl
@[local simp] theorem cl_val_39_0 : cl 39 0 = (1 : ℤ) := rfl
@[local simp] theorem cl_val_39_1 : cl 39 1 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_39_2 : cl 39 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_39_0_0 : A10 39 0 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_39_0_1 : A10 39 0 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_39_0_2 : A10 39 0 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_39_0 : b10 39 0 = (1 : ℤ) := rfl
@[local simp] theorem A10_val_39_1_0 : A10 39 1 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_39_1_1 : A10 39 1 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_39_1_2 : A10 39 1 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_39_1 : b10 39 1 = (1 : ℤ) := rfl
@[local simp] theorem A10_val_39_2_0 : A10 39 2 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_39_2_1 : A10 39 2 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_39_2_2 : A10 39 2 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_39_2 : b10 39 2 = (-9 : ℤ) := rfl
@[local simp] theorem A10_val_39_3_0 : A10 39 3 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_39_3_1 : A10 39 3 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_39_3_2 : A10 39 3 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_39_3 : b10 39 3 = (-5 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_39_0_0 : Work.Cusp.cubeXToKlein 39 0 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_39_0_1 : Work.Cusp.cubeXToKlein 39 0 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_39_0_2 : Work.Cusp.cubeXToKlein 39 0 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_39_0 : Work.Cusp.cubeXToKleinb 39 0 = ((1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_39_1_0 : Work.Cusp.cubeXToKlein 39 1 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_39_1_1 : Work.Cusp.cubeXToKlein 39 1 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_39_1_2 : Work.Cusp.cubeXToKlein 39 1 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_39_1 : Work.Cusp.cubeXToKleinb 39 1 = ((1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_39_2_0 : Work.Cusp.cubeXToKlein 39 2 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_39_2_1 : Work.Cusp.cubeXToKlein 39 2 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_39_2_2 : Work.Cusp.cubeXToKlein 39 2 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_39_2 : Work.Cusp.cubeXToKleinb 39 2 = ((-9 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_39_3_0 : Work.Cusp.cubeXToKlein 39 3 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_39_3_1 : Work.Cusp.cubeXToKlein 39 3 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_39_3_2 : Work.Cusp.cubeXToKlein 39 3 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_39_3 : Work.Cusp.cubeXToKleinb 39 3 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeVert_val_40 : Work.RTOwed.cubeVert 40 = (7 : Fin 24) := rfl
@[local simp] theorem cl_val_40_0 : cl 40 0 = (1 : ℤ) := rfl
@[local simp] theorem cl_val_40_1 : cl 40 1 = (-2 : ℤ) := rfl
@[local simp] theorem cl_val_40_2 : cl 40 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_40_0_0 : A10 40 0 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_40_0_1 : A10 40 0 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_40_0_2 : A10 40 0 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_40_0 : b10 40 0 = (3 : ℤ) := rfl
@[local simp] theorem A10_val_40_1_0 : A10 40 1 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_40_1_1 : A10 40 1 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_40_1_2 : A10 40 1 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_40_1 : b10 40 1 = (5 : ℤ) := rfl
@[local simp] theorem A10_val_40_2_0 : A10 40 2 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_40_2_1 : A10 40 2 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_40_2_2 : A10 40 2 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_40_2 : b10 40 2 = (5 : ℤ) := rfl
@[local simp] theorem A10_val_40_3_0 : A10 40 3 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_40_3_1 : A10 40 3 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_40_3_2 : A10 40 3 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_40_3 : b10 40 3 = (9 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_40_0_0 : Work.Cusp.cubeXToKlein 40 0 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_40_0_1 : Work.Cusp.cubeXToKlein 40 0 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_40_0_2 : Work.Cusp.cubeXToKlein 40 0 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_40_0 : Work.Cusp.cubeXToKleinb 40 0 = ((3 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_40_1_0 : Work.Cusp.cubeXToKlein 40 1 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_40_1_1 : Work.Cusp.cubeXToKlein 40 1 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_40_1_2 : Work.Cusp.cubeXToKlein 40 1 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_40_1 : Work.Cusp.cubeXToKleinb 40 1 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_40_2_0 : Work.Cusp.cubeXToKlein 40 2 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_40_2_1 : Work.Cusp.cubeXToKlein 40 2 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_40_2_2 : Work.Cusp.cubeXToKlein 40 2 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_40_2 : Work.Cusp.cubeXToKleinb 40 2 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_40_3_0 : Work.Cusp.cubeXToKlein 40 3 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_40_3_1 : Work.Cusp.cubeXToKlein 40 3 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_40_3_2 : Work.Cusp.cubeXToKlein 40 3 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_40_3 : Work.Cusp.cubeXToKleinb 40 3 = ((9 : ℚ)/10) := rfl
@[local simp] theorem cubeVert_val_41 : Work.RTOwed.cubeVert 41 = (10 : Fin 24) := rfl
@[local simp] theorem cl_val_41_0 : cl 41 0 = (1 : ℤ) := rfl
@[local simp] theorem cl_val_41_1 : cl 41 1 = (1 : ℤ) := rfl
@[local simp] theorem cl_val_41_2 : cl 41 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_41_0_0 : A10 41 0 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_41_0_1 : A10 41 0 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_41_0_2 : A10 41 0 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_41_0 : b10 41 0 = (-3 : ℤ) := rfl
@[local simp] theorem A10_val_41_1_0 : A10 41 1 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_41_1_1 : A10 41 1 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_41_1_2 : A10 41 1 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_41_1 : b10 41 1 = (-5 : ℤ) := rfl
@[local simp] theorem A10_val_41_2_0 : A10 41 2 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_41_2_1 : A10 41 2 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_41_2_2 : A10 41 2 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_41_2 : b10 41 2 = (5 : ℤ) := rfl
@[local simp] theorem A10_val_41_3_0 : A10 41 3 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_41_3_1 : A10 41 3 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_41_3_2 : A10 41 3 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_41_3 : b10 41 3 = (-9 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_41_0_0 : Work.Cusp.cubeXToKlein 41 0 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_41_0_1 : Work.Cusp.cubeXToKlein 41 0 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_41_0_2 : Work.Cusp.cubeXToKlein 41 0 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_41_0 : Work.Cusp.cubeXToKleinb 41 0 = ((-3 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_41_1_0 : Work.Cusp.cubeXToKlein 41 1 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_41_1_1 : Work.Cusp.cubeXToKlein 41 1 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_41_1_2 : Work.Cusp.cubeXToKlein 41 1 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_41_1 : Work.Cusp.cubeXToKleinb 41 1 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_41_2_0 : Work.Cusp.cubeXToKlein 41 2 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_41_2_1 : Work.Cusp.cubeXToKlein 41 2 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_41_2_2 : Work.Cusp.cubeXToKlein 41 2 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_41_2 : Work.Cusp.cubeXToKleinb 41 2 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_41_3_0 : Work.Cusp.cubeXToKlein 41 3 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_41_3_1 : Work.Cusp.cubeXToKlein 41 3 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_41_3_2 : Work.Cusp.cubeXToKlein 41 3 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_41_3 : Work.Cusp.cubeXToKleinb 41 3 = ((-9 : ℚ)/10) := rfl
@[local simp] theorem cubeVert_val_42 : Work.RTOwed.cubeVert 42 = (1 : Fin 24) := rfl
@[local simp] theorem cl_val_42_0 : cl 42 0 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_42_1 : cl 42 1 = (-2 : ℤ) := rfl
@[local simp] theorem cl_val_42_2 : cl 42 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_42_0_0 : A10 42 0 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_42_0_1 : A10 42 0 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_42_0_2 : A10 42 0 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_42_0 : b10 42 0 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_42_1_0 : A10 42 1 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_42_1_1 : A10 42 1 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_42_1_2 : A10 42 1 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_42_1 : b10 42 1 = (-9 : ℤ) := rfl
@[local simp] theorem A10_val_42_2_0 : A10 42 2 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_42_2_1 : A10 42 2 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_42_2_2 : A10 42 2 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_42_2 : b10 42 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_42_3_0 : A10 42 3 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_42_3_1 : A10 42 3 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_42_3_2 : A10 42 3 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_42_3 : b10 42 3 = (5 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_42_0_0 : Work.Cusp.cubeXToKlein 42 0 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_42_0_1 : Work.Cusp.cubeXToKlein 42 0 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_42_0_2 : Work.Cusp.cubeXToKlein 42 0 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_42_0 : Work.Cusp.cubeXToKleinb 42 0 = ((-1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_42_1_0 : Work.Cusp.cubeXToKlein 42 1 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_42_1_1 : Work.Cusp.cubeXToKlein 42 1 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_42_1_2 : Work.Cusp.cubeXToKlein 42 1 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_42_1 : Work.Cusp.cubeXToKleinb 42 1 = ((-9 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_42_2_0 : Work.Cusp.cubeXToKlein 42 2 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_42_2_1 : Work.Cusp.cubeXToKlein 42 2 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_42_2_2 : Work.Cusp.cubeXToKlein 42 2 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_42_2 : Work.Cusp.cubeXToKleinb 42 2 = ((-1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_42_3_0 : Work.Cusp.cubeXToKlein 42 3 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_42_3_1 : Work.Cusp.cubeXToKlein 42 3 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_42_3_2 : Work.Cusp.cubeXToKlein 42 3 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_42_3 : Work.Cusp.cubeXToKleinb 42 3 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeVert_val_43 : Work.RTOwed.cubeVert 43 = (4 : Fin 24) := rfl
@[local simp] theorem cl_val_43_0 : cl 43 0 = (-2 : ℤ) := rfl
@[local simp] theorem cl_val_43_1 : cl 43 1 = (-1 : ℤ) := rfl
@[local simp] theorem cl_val_43_2 : cl 43 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_43_0_0 : A10 43 0 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_43_0_1 : A10 43 0 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_43_0_2 : A10 43 0 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_43_0 : b10 43 0 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_43_1_0 : A10 43 1 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_43_1_1 : A10 43 1 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_43_1_2 : A10 43 1 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_43_1 : b10 43 1 = (1 : ℤ) := rfl
@[local simp] theorem A10_val_43_2_0 : A10 43 2 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_43_2_1 : A10 43 2 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_43_2_2 : A10 43 2 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_43_2 : b10 43 2 = (-9 : ℤ) := rfl
@[local simp] theorem A10_val_43_3_0 : A10 43 3 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_43_3_1 : A10 43 3 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_43_3_2 : A10 43 3 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_43_3 : b10 43 3 = (-5 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_43_0_0 : Work.Cusp.cubeXToKlein 43 0 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_43_0_1 : Work.Cusp.cubeXToKlein 43 0 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_43_0_2 : Work.Cusp.cubeXToKlein 43 0 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_43_0 : Work.Cusp.cubeXToKleinb 43 0 = ((-1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_43_1_0 : Work.Cusp.cubeXToKlein 43 1 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_43_1_1 : Work.Cusp.cubeXToKlein 43 1 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_43_1_2 : Work.Cusp.cubeXToKlein 43 1 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_43_1 : Work.Cusp.cubeXToKleinb 43 1 = ((1 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_43_2_0 : Work.Cusp.cubeXToKlein 43 2 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_43_2_1 : Work.Cusp.cubeXToKlein 43 2 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_43_2_2 : Work.Cusp.cubeXToKlein 43 2 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_43_2 : Work.Cusp.cubeXToKleinb 43 2 = ((-9 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_43_3_0 : Work.Cusp.cubeXToKlein 43 3 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_43_3_1 : Work.Cusp.cubeXToKlein 43 3 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_43_3_2 : Work.Cusp.cubeXToKlein 43 3 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_43_3 : Work.Cusp.cubeXToKleinb 43 3 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeVert_val_44 : Work.RTOwed.cubeVert 44 = (15 : Fin 24) := rfl
@[local simp] theorem cl_val_44_0 : cl 44 0 = (-2 : ℤ) := rfl
@[local simp] theorem cl_val_44_1 : cl 44 1 = (-2 : ℤ) := rfl
@[local simp] theorem cl_val_44_2 : cl 44 2 = (0 : ℤ) := rfl
@[local simp] theorem A10_val_44_0_0 : A10 44 0 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_44_0_1 : A10 44 0 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_44_0_2 : A10 44 0 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_44_0 : b10 44 0 = (-3 : ℤ) := rfl
@[local simp] theorem A10_val_44_1_0 : A10 44 1 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_44_1_1 : A10 44 1 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_44_1_2 : A10 44 1 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_44_1 : b10 44 1 = (5 : ℤ) := rfl
@[local simp] theorem A10_val_44_2_0 : A10 44 2 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_44_2_1 : A10 44 2 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_44_2_2 : A10 44 2 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_44_2 : b10 44 2 = (5 : ℤ) := rfl
@[local simp] theorem A10_val_44_3_0 : A10 44 3 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_44_3_1 : A10 44 3 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_44_3_2 : A10 44 3 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_44_3 : b10 44 3 = (9 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_44_0_0 : Work.Cusp.cubeXToKlein 44 0 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_44_0_1 : Work.Cusp.cubeXToKlein 44 0 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_44_0_2 : Work.Cusp.cubeXToKlein 44 0 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_44_0 : Work.Cusp.cubeXToKleinb 44 0 = ((-3 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_44_1_0 : Work.Cusp.cubeXToKlein 44 1 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_44_1_1 : Work.Cusp.cubeXToKlein 44 1 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_44_1_2 : Work.Cusp.cubeXToKlein 44 1 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_44_1 : Work.Cusp.cubeXToKleinb 44 1 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_44_2_0 : Work.Cusp.cubeXToKlein 44 2 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_44_2_1 : Work.Cusp.cubeXToKlein 44 2 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_44_2_2 : Work.Cusp.cubeXToKlein 44 2 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_44_2 : Work.Cusp.cubeXToKleinb 44 2 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_44_3_0 : Work.Cusp.cubeXToKlein 44 3 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_44_3_1 : Work.Cusp.cubeXToKlein 44 3 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_44_3_2 : Work.Cusp.cubeXToKlein 44 3 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_44_3 : Work.Cusp.cubeXToKleinb 44 3 = ((9 : ℚ)/10) := rfl
@[local simp] theorem cubeVert_val_45 : Work.RTOwed.cubeVert 45 = (2 : Fin 24) := rfl
@[local simp] theorem cl_val_45_0 : cl 45 0 = (-2 : ℤ) := rfl
@[local simp] theorem cl_val_45_1 : cl 45 1 = (1 : ℤ) := rfl
@[local simp] theorem cl_val_45_2 : cl 45 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_45_0_0 : A10 45 0 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_45_0_1 : A10 45 0 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_45_0_2 : A10 45 0 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_45_0 : b10 45 0 = (3 : ℤ) := rfl
@[local simp] theorem A10_val_45_1_0 : A10 45 1 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_45_1_1 : A10 45 1 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_45_1_2 : A10 45 1 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_45_1 : b10 45 1 = (-5 : ℤ) := rfl
@[local simp] theorem A10_val_45_2_0 : A10 45 2 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_45_2_1 : A10 45 2 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_45_2_2 : A10 45 2 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_45_2 : b10 45 2 = (5 : ℤ) := rfl
@[local simp] theorem A10_val_45_3_0 : A10 45 3 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_45_3_1 : A10 45 3 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_45_3_2 : A10 45 3 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_45_3 : b10 45 3 = (-9 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_45_0_0 : Work.Cusp.cubeXToKlein 45 0 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_45_0_1 : Work.Cusp.cubeXToKlein 45 0 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_45_0_2 : Work.Cusp.cubeXToKlein 45 0 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_45_0 : Work.Cusp.cubeXToKleinb 45 0 = ((3 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_45_1_0 : Work.Cusp.cubeXToKlein 45 1 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_45_1_1 : Work.Cusp.cubeXToKlein 45 1 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_45_1_2 : Work.Cusp.cubeXToKlein 45 1 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_45_1 : Work.Cusp.cubeXToKleinb 45 1 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_45_2_0 : Work.Cusp.cubeXToKlein 45 2 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_45_2_1 : Work.Cusp.cubeXToKlein 45 2 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_45_2_2 : Work.Cusp.cubeXToKlein 45 2 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_45_2 : Work.Cusp.cubeXToKleinb 45 2 = ((1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_45_3_0 : Work.Cusp.cubeXToKlein 45 3 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_45_3_1 : Work.Cusp.cubeXToKlein 45 3 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_45_3_2 : Work.Cusp.cubeXToKlein 45 3 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_45_3 : Work.Cusp.cubeXToKleinb 45 3 = ((-9 : ℚ)/10) := rfl
@[local simp] theorem cubeVert_val_46 : Work.RTOwed.cubeVert 46 = (8 : Fin 24) := rfl
@[local simp] theorem cl_val_46_0 : cl 46 0 = (1 : ℤ) := rfl
@[local simp] theorem cl_val_46_1 : cl 46 1 = (-2 : ℤ) := rfl
@[local simp] theorem cl_val_46_2 : cl 46 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_46_0_0 : A10 46 0 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_46_0_1 : A10 46 0 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_46_0_2 : A10 46 0 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_46_0 : b10 46 0 = (-3 : ℤ) := rfl
@[local simp] theorem A10_val_46_1_0 : A10 46 1 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_46_1_1 : A10 46 1 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_46_1_2 : A10 46 1 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_46_1 : b10 46 1 = (-5 : ℤ) := rfl
@[local simp] theorem A10_val_46_2_0 : A10 46 2 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_46_2_1 : A10 46 2 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_46_2_2 : A10 46 2 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_46_2 : b10 46 2 = (-5 : ℤ) := rfl
@[local simp] theorem A10_val_46_3_0 : A10 46 3 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_46_3_1 : A10 46 3 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_46_3_2 : A10 46 3 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_46_3 : b10 46 3 = (-9 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_46_0_0 : Work.Cusp.cubeXToKlein 46 0 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_46_0_1 : Work.Cusp.cubeXToKlein 46 0 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_46_0_2 : Work.Cusp.cubeXToKlein 46 0 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_46_0 : Work.Cusp.cubeXToKleinb 46 0 = ((-3 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_46_1_0 : Work.Cusp.cubeXToKlein 46 1 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_46_1_1 : Work.Cusp.cubeXToKlein 46 1 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_46_1_2 : Work.Cusp.cubeXToKlein 46 1 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_46_1 : Work.Cusp.cubeXToKleinb 46 1 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_46_2_0 : Work.Cusp.cubeXToKlein 46 2 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_46_2_1 : Work.Cusp.cubeXToKlein 46 2 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_46_2_2 : Work.Cusp.cubeXToKlein 46 2 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_46_2 : Work.Cusp.cubeXToKleinb 46 2 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_46_3_0 : Work.Cusp.cubeXToKlein 46 3 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_46_3_1 : Work.Cusp.cubeXToKlein 46 3 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_46_3_2 : Work.Cusp.cubeXToKlein 46 3 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_46_3 : Work.Cusp.cubeXToKleinb 46 3 = ((-9 : ℚ)/10) := rfl
@[local simp] theorem cubeVert_val_47 : Work.RTOwed.cubeVert 47 = (0 : Fin 24) := rfl
@[local simp] theorem cl_val_47_0 : cl 47 0 = (-2 : ℤ) := rfl
@[local simp] theorem cl_val_47_1 : cl 47 1 = (-2 : ℤ) := rfl
@[local simp] theorem cl_val_47_2 : cl 47 2 = (-1 : ℤ) := rfl
@[local simp] theorem A10_val_47_0_0 : A10 47 0 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_47_0_1 : A10 47 0 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_47_0_2 : A10 47 0 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_47_0 : b10 47 0 = (3 : ℤ) := rfl
@[local simp] theorem A10_val_47_1_0 : A10 47 1 0 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_47_1_1 : A10 47 1 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_47_1_2 : A10 47 1 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_47_1 : b10 47 1 = (-5 : ℤ) := rfl
@[local simp] theorem A10_val_47_2_0 : A10 47 2 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_47_2_1 : A10 47 2 1 = (2 : ℤ) := rfl
@[local simp] theorem A10_val_47_2_2 : A10 47 2 2 = (-2 : ℤ) := rfl
@[local simp] theorem b10_val_47_2 : b10 47 2 = (-5 : ℤ) := rfl
@[local simp] theorem A10_val_47_3_0 : A10 47 3 0 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_47_3_1 : A10 47 3 1 = (-2 : ℤ) := rfl
@[local simp] theorem A10_val_47_3_2 : A10 47 3 2 = (2 : ℤ) := rfl
@[local simp] theorem b10_val_47_3 : b10 47 3 = (-9 : ℤ) := rfl
@[local simp] theorem cubeXToKlein_val_47_0_0 : Work.Cusp.cubeXToKlein 47 0 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_47_0_1 : Work.Cusp.cubeXToKlein 47 0 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_47_0_2 : Work.Cusp.cubeXToKlein 47 0 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_47_0 : Work.Cusp.cubeXToKleinb 47 0 = ((3 : ℚ)/10) := rfl
@[local simp] theorem cubeXToKlein_val_47_1_0 : Work.Cusp.cubeXToKlein 47 1 0 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_47_1_1 : Work.Cusp.cubeXToKlein 47 1 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_47_1_2 : Work.Cusp.cubeXToKlein 47 1 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_47_1 : Work.Cusp.cubeXToKleinb 47 1 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_47_2_0 : Work.Cusp.cubeXToKlein 47 2 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_47_2_1 : Work.Cusp.cubeXToKlein 47 2 1 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_47_2_2 : Work.Cusp.cubeXToKlein 47 2 2 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_47_2 : Work.Cusp.cubeXToKleinb 47 2 = ((-1 : ℚ)/2) := rfl
@[local simp] theorem cubeXToKlein_val_47_3_0 : Work.Cusp.cubeXToKlein 47 3 0 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_47_3_1 : Work.Cusp.cubeXToKlein 47 3 1 = ((-1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKlein_val_47_3_2 : Work.Cusp.cubeXToKlein 47 3 2 = ((1 : ℚ)/5) := rfl
@[local simp] theorem cubeXToKleinb_val_47_3 : Work.Cusp.cubeXToKleinb 47 3 = ((-9 : ℚ)/10) := rfl

/-! ## The bridges to the rational data of `Work.Cusp.Data` -/

/-- `cubeXToKlein a i j` is `A10 a i j / 10`. -/
theorem hA10 : ∀ (a : Fin 48) (i : Fin 4) (j : Fin 3),
    ((Work.Cusp.cubeXToKlein a i j : ℚ) : ℝ) = ((A10 a i j : ℤ) : ℝ) / 10 := by
  intro a i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;> simp <;> norm_num

/-- `cubeXToKleinb a i` is `b10 a i / 10`. -/
theorem hb10 : ∀ (a : Fin 48) (i : Fin 4),
    ((Work.Cusp.cubeXToKleinb a i : ℚ) : ℝ) = ((b10 a i : ℤ) : ℝ) / 10 := by
  intro a i
  fin_cases a <;> fin_cases i <;> simp <;> norm_num

end Eval

/-- `cl` is the table `cubeCorner`. -/
theorem hclZ : ∀ (a : Fin 48) (j : Fin 3), cl a j = Work.Cusp.cubeCorner a j := by decide

/-- `cl` is the table `cubeCorner`, in `ℝ`. -/
theorem hclR : ∀ (a : Fin 48) (j : Fin 3),
    ((cl a j : ℤ) : ℝ) = ((Work.Cusp.cubeCorner a j : ℤ) : ℝ) := by
  intro a j
  rw [hclZ a j]


/-! ## The affine coefficients and the integral minimum

For `x = cl_a + t`, the affine function `10 · sideSlack S (kleinPt a ·)` is `KsideR a S + ∑_j EsideR a S j · t_j`,
and `20 · truncSlack w (kleinPt a ·)` is `KtruncR a w + ∑_j EtruncR a w j · t_j`.  The integral
versions `KsideZ`, `EsideZ`, ... are the same expressions in `ℤ`; only the *minimum over the box*
`K + ∑_j min(E_j,0)` of the affine function is needed below. -/

/-- The `j`-th coefficient of `10 · sideSlack S (kleinPt a ·)`. -/
def EsideR (a : Fin 48) (S : Fin 24) (j : Fin 3) : ℝ :=
  -(∑ i : Fin 4, (Work.FoldInst.sideNormal S i : ℝ) * ((A10 a i j : ℤ) : ℝ))

/-- The constant term of `10 · sideSlack S (kleinPt a (cl_a + ·))`. -/
def KsideR (a : Fin 48) (S : Fin 24) : ℝ :=
  10 - ∑ i : Fin 4, (Work.FoldInst.sideNormal S i : ℝ) *
        (∑ j : Fin 3, ((A10 a i j : ℤ) : ℝ) * ((cl a j : ℤ) : ℝ) + ((b10 a i : ℤ) : ℝ))

/-- The `j`-th coefficient of `20 · truncSlack w (kleinPt a ·)`. -/
def EtruncR (a : Fin 48) (w : Fin 24) (j : Fin 3) : ℝ :=
  -(∑ i : Fin 4, (Work.FoldInst.truncNormal2 w i : ℝ) * ((A10 a i j : ℤ) : ℝ))

/-- The constant term of `20 · truncSlack w (kleinPt a (cl_a + ·))`. -/
def KtruncR (a : Fin 48) (w : Fin 24) : ℝ :=
  16 - ∑ i : Fin 4, (Work.FoldInst.truncNormal2 w i : ℝ) *
        (∑ j : Fin 3, ((A10 a i j : ℤ) : ℝ) * ((cl a j : ℤ) : ℝ) + ((b10 a i : ℤ) : ℝ))

/-- The `j`-th coefficient of `10 · sideSlack S (kleinPt a ·)`, in `ℤ`. -/
def EsideZ (a : Fin 48) (S : Fin 24) (j : Fin 3) : ℤ :=
  -(∑ i : Fin 4, Work.FoldInst.sideNormal S i * A10 a i j)

/-- The constant term of `10 · sideSlack S (kleinPt a (cl_a + ·))`, in `ℤ`. -/
def KsideZ (a : Fin 48) (S : Fin 24) : ℤ :=
  10 - ∑ i : Fin 4, Work.FoldInst.sideNormal S i *
        (∑ j : Fin 3, A10 a i j * cl a j + b10 a i)

/-- The integral minimum of `10 · sideSlack S (kleinPt a ·)` over the cube. -/
def minSideZ (a : Fin 48) (S : Fin 24) : ℤ := KsideZ a S + ∑ j : Fin 3, min (EsideZ a S j) 0

/-- The `j`-th coefficient of `20 · truncSlack w (kleinPt a ·)`, in `ℤ`. -/
def EtruncZ (a : Fin 48) (w : Fin 24) (j : Fin 3) : ℤ :=
  -(∑ i : Fin 4, Work.FoldInst.truncNormal2 w i * A10 a i j)

/-- The constant term of `20 · truncSlack w (kleinPt a (cl_a + ·))`, in `ℤ`. -/
def KtruncZ (a : Fin 48) (w : Fin 24) : ℤ :=
  16 - ∑ i : Fin 4, Work.FoldInst.truncNormal2 w i *
        (∑ j : Fin 3, A10 a i j * cl a j + b10 a i)

/-- The integral minimum of `20 · truncSlack w (kleinPt a ·)` over the cube. -/
def minTruncZ (a : Fin 48) (w : Fin 24) : ℤ := KtruncZ a w + ∑ j : Fin 3, min (EtruncZ a w j) 0

/-! ## The finite checks

The 24 side and 24 truncation constraints of `Q̄` on the 48 cubes: 2304 integer inequalities,
decided by the kernel. -/

/-- **The side constraints hold on every cube.** -/
theorem minSideZ_nonneg : ∀ (a : Fin 48) (S : Fin 24), 0 ≤ minSideZ a S := by decide

/-- **The truncation constraints hold on every cube.** -/
theorem minTruncZ_nonneg : ∀ (a : Fin 48) (w : Fin 24), 0 ≤ minTruncZ a w := by decide

/-! ## The cast lemmas -/

/-- `KsideR` is the cast of `KsideZ`. -/
theorem KsideZ_cast (a : Fin 48) (S : Fin 24) : ((KsideZ a S : ℤ) : ℝ) = KsideR a S := by
  simp only [KsideZ, KsideR]
  push_cast
  ring

/-- `EsideR` is the cast of `EsideZ`. -/
theorem EsideZ_cast (a : Fin 48) (S : Fin 24) (j : Fin 3) :
    ((EsideZ a S j : ℤ) : ℝ) = EsideR a S j := by
  simp only [EsideZ, EsideR]
  push_cast
  ring

/-- `KtruncR` is the cast of `KtruncZ`. -/
theorem KtruncZ_cast (a : Fin 48) (w : Fin 24) : ((KtruncZ a w : ℤ) : ℝ) = KtruncR a w := by
  simp only [KtruncZ, KtruncR]
  push_cast
  ring

/-- `EtruncR` is the cast of `EtruncZ`. -/
theorem EtruncZ_cast (a : Fin 48) (w : Fin 24) (j : Fin 3) :
    ((EtruncZ a w j : ℤ) : ℝ) = EtruncR a w j := by
  simp only [EtruncZ, EtruncR]
  push_cast
  ring

/-- The `ℝ`-minimum of the side constraints is the cast of `minSideZ`. -/
theorem minSideZ_cast (a : Fin 48) (S : Fin 24) :
    ((minSideZ a S : ℤ) : ℝ) = KsideR a S + ∑ j : Fin 3, min (EsideR a S j) 0 := by
  simp only [minSideZ]
  push_cast
  simp only [KsideZ_cast, EsideZ_cast]

/-- The `ℝ`-minimum of the truncation constraints is the cast of `minTruncZ`. -/
theorem minTruncZ_cast (a : Fin 48) (w : Fin 24) :
    ((minTruncZ a w : ℤ) : ℝ) = KtruncR a w + ∑ j : Fin 3, min (EtruncR a w j) 0 := by
  simp only [minTruncZ]
  push_cast
  simp only [KtruncZ_cast, EtruncZ_cast]

/-! ## The general one-dimensional bound -/

/-- On `[0,1]`, `min λ 0 ≤ λ t`. -/
theorem min_le_mul (lam t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : min lam 0 ≤ lam * t := by
  rcases le_total lam 0 with h | h
  · rw [min_eq_left h]
    nlinarith [mul_le_mul_of_nonpos_left h1 h]
  · rw [min_eq_right h]
    exact mul_nonneg h h0

/-! ## The two affine identities -/

/-- `10 · sideSlack S (kleinPt a x)` as an affine function of `x - cl_a`. -/
theorem ten_sideSlack (a : Fin 48) (S : Fin 24) (x : CuspE3) :
    10 * Work.FoldInst.sideSlack S (Work.RTOwed.kleinPt a x)
      = KsideR a S + ∑ j : Fin 3, EsideR a S j * (x j - ((cl a j : ℤ) : ℝ)) := by
  simp only [Work.FoldInst.sideSlack, Work.RTOwed.kleinPt, PiLp.toLp_apply, KsideR, EsideR,
    Fin.sum_univ_four, Fin.sum_univ_three, hA10, hb10]
  ring

/-- `20 · truncSlack w (kleinPt a x)` as an affine function of `x - cl_a`. -/
theorem twenty_truncSlack (a : Fin 48) (w : Fin 24) (x : CuspE3) :
    20 * Work.FoldInst.truncSlack w (Work.RTOwed.kleinPt a x)
      = KtruncR a w + ∑ j : Fin 3, EtruncR a w j * (x j - ((cl a j : ℤ) : ℝ)) := by
  simp only [Work.FoldInst.truncSlack, Work.RTOwed.kleinPt, PiLp.toLp_apply, KtruncR, EtruncR,
    Fin.sum_univ_four, Fin.sum_univ_three, hA10, hb10]
  ring

/-- The side constraints hold on every cube. -/
theorem sideSlack_nonneg (a : Fin 48) (S : Fin 24) (x : CuspE3) (hx : x ∈ Work.RTOwed.cubeBox a) :
    0 ≤ Work.FoldInst.sideSlack S (Work.RTOwed.kleinPt a x) := by
  have hmin : (0 : ℝ) ≤ KsideR a S + ∑ j : Fin 3, min (EsideR a S j) 0 := by
    rw [← minSideZ_cast a S]
    exact_mod_cast minSideZ_nonneg a S
  have ht : ∀ j : Fin 3, 0 ≤ x j - ((cl a j : ℤ) : ℝ) ∧ x j - ((cl a j : ℤ) : ℝ) ≤ 1 := by
    intro j
    have h := hx j
    rw [← hclR a j] at h
    constructor <;> linarith [h.1, h.2]
  have hle : KsideR a S + ∑ j : Fin 3, min (EsideR a S j) 0
      ≤ KsideR a S + ∑ j : Fin 3, EsideR a S j * (x j - ((cl a j : ℤ) : ℝ)) :=
    add_le_add le_rfl (Finset.sum_le_sum fun j _ => min_le_mul _ _ (ht j).1 (ht j).2)
  have haff := ten_sideSlack a S x
  linarith [hmin, hle, haff]

/-- The truncation constraints hold on every cube. -/
theorem truncSlack_nonneg (a : Fin 48) (w : Fin 24) (x : CuspE3) (hx : x ∈ Work.RTOwed.cubeBox a) :
    0 ≤ Work.FoldInst.truncSlack w (Work.RTOwed.kleinPt a x) := by
  have hmin : (0 : ℝ) ≤ KtruncR a w + ∑ j : Fin 3, min (EtruncR a w j) 0 := by
    rw [← minTruncZ_cast a w]
    exact_mod_cast minTruncZ_nonneg a w
  have ht : ∀ j : Fin 3, 0 ≤ x j - ((cl a j : ℤ) : ℝ) ∧ x j - ((cl a j : ℤ) : ℝ) ≤ 1 := by
    intro j
    have h := hx j
    rw [← hclR a j] at h
    constructor <;> linarith [h.1, h.2]
  have hle : KtruncR a w + ∑ j : Fin 3, min (EtruncR a w j) 0
      ≤ KtruncR a w + ∑ j : Fin 3, EtruncR a w j * (x j - ((cl a j : ℤ) : ℝ)) :=
    add_le_add le_rfl (Finset.sum_le_sum fun j _ => min_le_mul _ _ (ht j).1 (ht j).2)
  have haff := twenty_truncSlack a w x
  linarith [hmin, hle, haff]

/-! ## The truncation facet of the cube's own ideal vertex -/

/-- The constant term of `20 · truncSlack w (kleinPt a ·)` in `x` (not in `x - cl_a`). -/
def KVg (a : Fin 48) (w : Fin 24) : ℤ :=
  16 - ∑ i : Fin 4, Work.FoldInst.truncNormal2 w i * b10 a i

/-- The `j`-th coefficient of `20 · truncSlack w (kleinPt a ·)` in `x`. -/
def EVg (a : Fin 48) (w : Fin 24) (j : Fin 3) : ℤ :=
  -∑ i : Fin 4, Work.FoldInst.truncNormal2 w i * A10 a i j

/-- `20 · truncSlack w (kleinPt a x)` as an affine function of `x`. -/
theorem twenty_truncSlack_x (a : Fin 48) (w : Fin 24) (x : CuspE3) :
    20 * Work.FoldInst.truncSlack w (Work.RTOwed.kleinPt a x)
      = ((KVg a w : ℤ) : ℝ) + ∑ j : Fin 3, ((EVg a w j : ℤ) : ℝ) * x j := by
  simp only [Work.FoldInst.truncSlack, Work.RTOwed.kleinPt, PiLp.toLp_apply, KVg, EVg,
    Fin.sum_univ_four, Fin.sum_univ_three, hA10, hb10]
  push_cast
  ring

/-- The constant term vanishes on the truncation facet of the cube's own ideal vertex. -/
theorem KVg_vert_zero : ∀ (a : Fin 48), KVg a (Work.RTOwed.cubeVert a) = 0 := by decide

/-- All the coefficients vanish on the truncation facet of the cube's own ideal vertex. -/
theorem EVg_vert_zero : ∀ (a : Fin 48) (j : Fin 3), EVg a (Work.RTOwed.cubeVert a) j = 0 := by decide

/-- **The cube lies on the truncation facet of its own ideal vertex.** -/
theorem twenty_truncSlack_vert (a : Fin 48) (x : CuspE3) :
    20 * Work.FoldInst.truncSlack (Work.RTOwed.cubeVert a) (Work.RTOwed.kleinPt a x) = 0 := by
  rw [twenty_truncSlack_x a (Work.RTOwed.cubeVert a) x]
  simp [KVg_vert_zero, EVg_vert_zero]

/-! ## The certificate -/

/-- **The cube certificate**: the affine image of each of the 48 cubes lies in `Q̄`, on the
truncation facet of its own ideal vertex. -/
theorem cube_quad :
    (∀ (a : Fin 48) (x : Work.RTOwed.CuspE3), x ∈ Work.RTOwed.cubeBox a →
      Work.RTOwed.kleinPt a x ∈ Work.FoldInst.Qbar) ∧
    (∀ (a : Fin 48) (x : Work.RTOwed.CuspE3), x ∈ Work.RTOwed.cubeBox a →
      Work.FoldInst.truncSlack (Work.RTOwed.cubeVert a) (Work.RTOwed.kleinPt a x) = 0) := by
  constructor
  · intro a x hx
    exact ⟨fun S => sideSlack_nonneg a S x hx, fun w => truncSlack_nonneg a w x hx⟩
  · intro a x hx
    have h := twenty_truncSlack_vert a x
    linarith

end Work.RTOwed.cuspCert
