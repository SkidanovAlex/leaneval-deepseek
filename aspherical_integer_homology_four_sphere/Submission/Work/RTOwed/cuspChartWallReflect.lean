/-
# The wall reflection certificate of the cusp cube charts (W1)

`Work.RTOwed.chartKlein_wall` identifies the charts of two neighbouring cubes *on* their common
wall.  This file proves the stronger identity, valid on the whole vertical hyperplane of the wall:
the chart of the neighbouring cube at the lattice translate `x - λ` is the reflected chart of `a`,
paired by the sign change `wallGamK a i side`:

  `chartKlein (wallNb a i side) (mkE4 (x - wallLamV a i side) s)
     = act (wallGamK a i side) (chartKlein a (mkE4 (reflWall i c x) s))`,  `c = cubeCorner a i + side`,

where `reflWall i c` reflects the `i`-th coordinate of the horizontal part of the UHS point in the
wall `x i = c` (`x i ↦ 2c - x i`).

The proof is the same homogenised-vector computation as in `chartKlein_wall`, but with the
reflection matrix `cwRefl i c` (the Lorentz matrix of the UHS reflection in the wall) in place of
the rank-one correction: the integer matrix identity

  `chartMat (wallNb a i side) * cwT2 (wallLam a i side)
     = 2 • (cwDiagZ (wallGamK a i side) * chartMat a * cwRefl i (cwC a i side))`

holds **exactly** (no correction term), and is a finite verification over the `48 × 3 × 2` walls,
proved by `decide`.
-/
import Mathlib
import Submission.Work.RTOwed.chartKlein_wall

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open scoped Matrix BigOperators
open Set Topology Function

namespace Work.RTOwed

noncomputable section

/-! ### The reflection of a horizontal coordinate in a wall -/

/-- **The reflection of the UHS point `x` in the wall `{x i = c}`**: the horizontal coordinate `i`
is replaced by `2c - x i`; the other coordinates (including the height) are unchanged. -/
def reflWall (i : Fin 3) (c : ℝ) (x : CuspE3) : CuspE3 :=
  WithLp.toLp 2 fun j => if j = i then 2 * c - x j else x j

lemma reflWall_apply (i : Fin 3) (c : ℝ) (x : CuspE3) (j : Fin 3) :
    reflWall i c x j = if j = i then 2 * c - x j else x j := rfl

@[simp] lemma reflWall_self (i : Fin 3) (c : ℝ) (x : CuspE3) :
    reflWall i c x i = 2 * c - x i := by
  rw [reflWall_apply, if_pos rfl]

lemma reflWall_of_ne {i j : Fin 3} (h : j ≠ i) (c : ℝ) (x : CuspE3) :
    reflWall i c x j = x j := by
  rw [reflWall_apply, if_neg h]

lemma reflWall_fix (i : Fin 3) (c : ℝ) {x : CuspE3} (hx : x i = c) : reflWall i c x = x := by
  apply PiLp.ext
  intro j
  rw [reflWall_apply]
  by_cases h : j = i
  · subst h; rw [if_pos rfl, hx]; ring
  · rw [if_neg h]

lemma reflWall_reflWall (i : Fin 3) (c : ℝ) (x : CuspE3) :
    reflWall i c (reflWall i c x) = x := by
  apply PiLp.ext
  intro j
  rw [reflWall_apply, reflWall_apply]
  by_cases h : j = i
  · subst h; rw [if_pos rfl, if_pos rfl]; ring
  · rw [if_neg h, if_neg h]

/-! ### The reflection matrix in the homogenised coordinates -/

/-- **The integer matrix of the reflection `reflWall i c` in the homogenised UHS coordinates**
(`cwU (reflWall i c x) s = cwRefl i c *ᵥ cwU x s`).

In the coordinates `cwU x s = (2x₀, 2x₁, 2x₂, ∑x²+s²-1, ∑x²+s²+1)` the reflection
`x i ↦ 2c - x i` is linear: the constant `2c` is `c (u₄ - u₃)` and the change of `∑x²` is
`4c² - 4c x i = 2c² (u₄ - u₃) - 2c u_i`. -/
def cwRefl (i : Fin 3) (c : ℤ) : Matrix (Fin 5) (Fin 5) ℤ :=
  Matrix.of fun k j =>
    if k = cwI5 i then
      (if j = cwI5 i then -1 else if (j : ℕ) = 3 then -2 * c else if (j : ℕ) = 4 then 2 * c
        else 0)
    else if (k : ℕ) = 3 then
      (if j = cwI5 i then -2 * c else if (j : ℕ) = 3 then 1 - 2 * c * c
        else if (j : ℕ) = 4 then 2 * c * c else 0)
    else if (k : ℕ) = 4 then
      (if j = cwI5 i then -2 * c else if (j : ℕ) = 3 then -(2 * c * c)
        else if (j : ℕ) = 4 then 1 + 2 * c * c else 0)
    else (if j = k then 1 else 0)

/-- The real form of the reflection matrix. -/
def cwReflR (i : Fin 3) (c : ℤ) : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of fun k j => ((cwRefl i c k j : ℤ) : ℝ)

/-- **The reflection matrix computes the reflection of the homogenised UHS vector.** -/
theorem cwReflR_cwU (i : Fin 3) (c : ℤ) (x : CuspE3) (s : ℝ) :
    cwU (reflWall i (c : ℝ) x) s = cwReflR i c *ᵥ cwU x s := by
  funext k
  fin_cases i <;> fin_cases k <;>
    (simp only [cwU, cwQ, cwReflR, cwRefl, cwI5, Matrix.of_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_five, Fin.sum_univ_three, reflWall_apply] <;>
     norm_num <;> ring)

/-! ### The wall reflection certificate of the chart matrices -/

/-- **The finite verification (W1)**: the chart matrix of the neighbouring cube is the reflected
chart matrix of `a`, paired by the sign change.  This is an identity of integer matrices, verified
over the `48 × 3 × 2` walls by `decide`. -/
theorem cwWallMat_refl_pt : ∀ (a : Fin 48) (i : Fin 3) (side : Fin 2) (k j : Fin 5),
    (chartMat (wallNb a i side) * cwT2 (wallLam a i side)) k j
      = ((2 : ℤ) •
          (cwDiagZ (wallGamK a i side) * chartMat a * cwRefl i (cwC a i side))) k j := by
  decide

/-- The real form of the finite verification, entrywise. -/
lemma cwWallR_refl (a : Fin 48) (i : Fin 3) (side : Fin 2) (k j : Fin 5) :
    (cwMat (wallNb a i side) * cwT2R (wallLam a i side)) k j
      = 2 * ((cwDiagR (wallGamK a i side) * cwMat a * cwReflR i (cwC a i side)) k j) := by
  rw [cwMat_mul_T2R_apply]
  have h := cwWallMat_refl_pt a i side k j
  rw [h, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.mul_apply]
  simp only [cwDiagR, cwMat, cwReflR, Matrix.of_apply, cwDiagZ, Matrix.diagonal_mul, cwSignZ,
    cwSignExt, Fin.sum_univ_five]
  push_cast
  ring

/-- The real matrix identity of the wall reflection certificate. -/
lemma cwWallMatR_refl (a : Fin 48) (i : Fin 3) (side : Fin 2) :
    cwMat (wallNb a i side) * cwT2R (wallLam a i side)
      = (2 : ℝ) •
        (cwDiagR (wallGamK a i side) * cwMat a * cwReflR i (cwC a i side)) := by
  ext k j
  rw [cwWallR_refl a i side k j, Matrix.smul_apply, smul_eq_mul]

/-- **The wall reflection on the chart vectors.** -/
theorem cwVec_wall_refl (a : Fin 48) (i : Fin 3) (side : Fin 2) (y : CuspE3) (s : ℝ) :
    cwVec (wallNb a i side) (y - wallLamV a i side) s
      = cwSignExt (wallGamK a i side) * cwVec a (reflWall i (cwC a i side : ℝ) y) s := by
  show cwMat (wallNb a i side) *ᵥ cwU (y - wallLamV a i side) s
      = cwSignExt (wallGamK a i side) * cwVec a (reflWall i (cwC a i side : ℝ) y) s
  have hstep : (1 / 2 : ℝ) •
        ((cwMat (wallNb a i side) * cwT2R (wallLam a i side)) *ᵥ cwU y s)
      = (cwDiagR (wallGamK a i side) * cwMat a * cwReflR i (cwC a i side)) *ᵥ cwU y s := by
    rw [cwWallMatR_refl, Matrix.smul_mulVec, smul_smul,
      show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]
  rw [cwU_sub_wall, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hstep, ← Matrix.mulVec_mulVec,
    ← cwReflR_cwU, cwDiagR_mulVec]
  rfl

/-- **The wall reflection certificate of the cusp cube charts (W1).**  On the whole vertical
hyperplane of the wall `{y i = c}`, the chart of the neighbouring cube at the lattice translate
`y - λ` is the reflected chart of `a`, paired by the sign change `wallGamK a i side`. -/
theorem chartKlein_wall_refl (a : Fin 48) (i : Fin 3) (side : Fin 2) {y : CuspE3}
    {s : ℝ} (hs : 0 < s) :
    chartKlein (wallNb a i side) (mkE4 (y - wallLamV a i side) s)
      = Work.FoldInst.act (wallGamK a i side)
          (chartKlein a (mkE4 (reflWall i (cwC a i side : ℝ) y) s)) := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  rw [cwChart _ _ _ hs0, cwChart _ _ _ hs0, cwVec_wall_refl, cwKlein_signExt]

/-- The wall value `cwC a i side` in terms of the cube corner: `cubeCorner a i + side`. -/
lemma cwC_eq_corner (a : Fin 48) (i : Fin 3) (side : Fin 2) :
    cwC a i side = Work.Cusp.cubeCorner a i + (if (side : ℕ) = 0 then 0 else 1) := rfl

end

end Work.RTOwed
