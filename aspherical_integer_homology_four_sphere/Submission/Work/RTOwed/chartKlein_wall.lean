import Mathlib
import Submission.Work.RTOwed.cuspChart

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

/-!
# The wall gluing certificate of the cusp cube charts

This file proves the certificate `Work.RTOwed.chartKlein_wall`: the Möbius chart of a cube of the
cusp development, evaluated at a point of a *wall* of the cube (a face `{y i = cubeCorner a i}` or
`{y i = cubeCorner a i + 1}`) at a height `s ≥ 11/10`, equals the sign change `wallGamK a i side` of
the chart of the neighbouring cube `wallNb a i side` at the lattice translate `y - wallLam a i side`.

## Method

`chartKlein a (mkE4 x s)` is the Klein coordinate of the Lorentz vector
`chartMat a *ᵥ hypOfUHS (mkE4 x s)`; writing `cwU x s = 2 s · hypOfUHS (mkE4 x s)` (the homogenised
upper half space vector) and `cwMat a = chartMat a` over `ℝ`, the chart is
`kleinOfHyp (cwMat a *ᵥ cwU x s)`.

The lattice translation in the upper half space model is *linear* in the homogenised vector:

  `cwU (x - λ) s = (1/2) • (cwT2 λ *ᵥ cwU x s)`   (`cwU_sub`)

with the integer matrix `cwT2 λ` (built from `λ` and `λ 0 ^ 2 + λ 1 ^ 2 + λ 2 ^ 2`).  Hence the wall
certificate reduces to an identity of integer matrices

  `chartMat (wallNb a i side) * cwT2 (wallLam a i side)
     = 2 • (cwDiagZ (wallGamK a i side) * chartMat a) + 𝟙 ⊗ g`   (`cwWallMat_pt`)

whose *correction* `g` vanishes on the wall: `Σ_j g_j (cwU y s)_j = g · 2 (y i - c)`.  The matrix
identity is a finite verification over the 48 cubes, proved by `decide`.
-/

def cwIntVec (l : Fin 3 → ℤ) : CuspE3 := WithLp.toLp 2 fun j => (l j : ℝ)

lemma cwIntVec_apply (l : Fin 3 → ℤ) (j : Fin 3) : cwIntVec l j = (l j : ℝ) := rfl

lemma wallLamV_eq (a : Fin 48) (i : Fin 3) (side : Fin 2) :
    wallLamV a i side = cwIntVec (wallLam a i side) := rfl

/-! ### The homogenised upper half space vector -/

/-- The squared radius `∑ x_j² + s²` of `mkE4 x s`. -/
def cwQ (x : CuspE3) (s : ℝ) : ℝ := ∑ j : Fin 3, x j ^ 2 + s ^ 2

/-- `2 s · hypOfUHS (mkE4 x s)`, the homogenised upper half space vector. -/
def cwU (x : CuspE3) (s : ℝ) : Fin 5 → ℝ :=
  ![2 * x 0, 2 * x 1, 2 * x 2, cwQ x s - 1, cwQ x s + 1]

lemma cwU_zero (x : CuspE3) (s : ℝ) : cwU x s 0 = 2 * x 0 := rfl
lemma cwU_one (x : CuspE3) (s : ℝ) : cwU x s 1 = 2 * x 1 := rfl
lemma cwU_two (x : CuspE3) (s : ℝ) : cwU x s 2 = 2 * x 2 := rfl
lemma cwU_three (x : CuspE3) (s : ℝ) : cwU x s 3 = cwQ x s - 1 := rfl
lemma cwU_four (x : CuspE3) (s : ℝ) : cwU x s 4 = cwQ x s + 1 := rfl

/-- `chartMat a` with real entries. -/
def cwMat (a : Fin 48) : Matrix (Fin 5) (Fin 5) ℝ := Matrix.of fun k j => (chartMat a k j : ℝ)

/-- The chart vector of the cube `a` at `(x, s)`. -/
def cwVec (a : Fin 48) (x : CuspE3) (s : ℝ) : Fin 5 → ℝ := cwMat a *ᵥ cwU x s

lemma cwMat_eq (a : Fin 48) : cwMat a = (chartMat a).map (Int.castRingHom ℝ) := by
  ext k j
  simp [cwMat, Matrix.map_apply]

lemma cwMkE4_zero (x : CuspE3) (s : ℝ) : mkE4 x s 0 = x 0 := rfl
lemma cwMkE4_one (x : CuspE3) (s : ℝ) : mkE4 x s 1 = x 1 := rfl
lemma cwMkE4_two (x : CuspE3) (s : ℝ) : mkE4 x s 2 = x 2 := rfl
lemma cwMkE4_three (x : CuspE3) (s : ℝ) : mkE4 x s 3 = s := rfl

lemma cwNorm (x : CuspE3) (s : ℝ) : ‖mkE4 x s‖ ^ 2 = cwQ x s := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [mkE4, cwQ, Fin.sum_univ_four, Fin.sum_univ_three]
  norm_num

/-- `hypOfUHS (mkE4 x s) = (2 s)⁻¹ • cwU x s`. -/
lemma cwHyp (x : CuspE3) (s : ℝ) :
    Work.HypModel.hypOfUHS (mkE4 x s) = (2 * s)⁻¹ • cwU x s := by
  have c0 : Work.HypModel.hypOfUHS (mkE4 x s) 0 = (2 * s)⁻¹ * cwU x s 0 := by
    rw [Work.HypModel.hypOfUHS_apply_zero, cwMkE4_three, cwMkE4_zero, cwU_zero]
    field_simp
  have c1 : Work.HypModel.hypOfUHS (mkE4 x s) 1 = (2 * s)⁻¹ * cwU x s 1 := by
    rw [Work.HypModel.hypOfUHS_apply_one, cwMkE4_three, cwMkE4_one, cwU_one]
    field_simp
  have c2 : Work.HypModel.hypOfUHS (mkE4 x s) 2 = (2 * s)⁻¹ * cwU x s 2 := by
    rw [Work.HypModel.hypOfUHS_apply_two, cwMkE4_three, cwMkE4_two, cwU_two]
    field_simp
  have c3 : Work.HypModel.hypOfUHS (mkE4 x s) 3 = (2 * s)⁻¹ * cwU x s 3 := by
    rw [Work.HypModel.hypOfUHS_apply_three, cwMkE4_three, cwNorm, cwU_three]
    field_simp
  have c4 : Work.HypModel.hypOfUHS (mkE4 x s) 4 = (2 * s)⁻¹ * cwU x s 4 := by
    rw [Work.HypModel.hypOfUHS_apply_four, cwMkE4_three, cwNorm, cwU_four]
    field_simp
  funext i
  fin_cases i
  · exact c0
  · exact c1
  · exact c2
  · exact c3
  · exact c4

/-- `kleinOfHyp` is invariant under a nonzero scaling. -/
lemma cwKlein_smul {c : ℝ} (hc : c ≠ 0) (P : Work.HypModel.V5) :
    Work.HypModel.kleinOfHyp (c • P) = Work.HypModel.kleinOfHyp P := by
  ext i
  fin_cases i <;>
    simp [Work.HypModel.kleinOfHyp, Work.HypModel.proj4, Pi.smul_apply, smul_eq_mul] <;>
    field_simp

/-- The cube chart is the Klein map of the chart vector. -/
lemma cwChart (a : Fin 48) (x : CuspE3) (s : ℝ) (hs : s ≠ 0) :
    chartKlein a (mkE4 x s) = Work.HypModel.kleinOfHyp (cwVec a x s) := by
  have h2s : (2 * s)⁻¹ ≠ 0 := by
    have : (2 : ℝ) * s ≠ 0 := by positivity
    exact inv_ne_zero this
  have h1 : Work.HypModel.kleinOfHyp
        ((chartMat a).map (Int.castRingHom ℝ) *ᵥ Work.HypModel.hypOfUHS (mkE4 x s))
      = Work.HypModel.kleinOfHyp (cwVec a x s) := by
    rw [cwHyp x s, Matrix.mulVec_smul, ← cwMat_eq a]
    exact cwKlein_smul h2s (cwMat a *ᵥ cwU x s)
  rw [chartKlein]
  exact h1

/-! ### The lattice translation as a linear map -/

/-- `λ 0 ^ 2 + λ 1 ^ 2 + λ 2 ^ 2`. -/
def cwLamSq (l : Fin 3 → ℤ) : ℤ := l 0 * l 0 + l 1 * l 1 + l 2 * l 2

/-- The matrix of the (doubled) lattice translation in the homogenised UHS coordinates. -/
def cwT2 (l : Fin 3 → ℤ) : Matrix (Fin 5) (Fin 5) ℤ :=
  ![
    ![2, 0, 0, 2 * l 0, -2 * l 0],
    ![0, 2, 0, 2 * l 1, -2 * l 1],
    ![0, 0, 2, 2 * l 2, -2 * l 2],
    ![-2 * l 0, -2 * l 1, -2 * l 2, 2 - cwLamSq l, cwLamSq l],
    ![-2 * l 0, -2 * l 1, -2 * l 2, -cwLamSq l, 2 + cwLamSq l]
  ]

/-- `cwT2` with real entries. -/
def cwT2R (l : Fin 3 → ℤ) : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of fun k j => ((cwT2 l k j : ℤ) : ℝ)

/-- **The homogenised UHS vector of a lattice translate is a linear function of the original.** -/
theorem cwU_sub (x : CuspE3) (s : ℝ) (l : Fin 3 → ℤ) :
    cwU (x - cwIntVec l) s = (1 / 2 : ℝ) • (cwT2R l *ᵥ cwU x s) := by
  funext k
  fin_cases k <;>
  · simp only [cwU, cwQ, cwT2R, cwT2, cwLamSq, cwIntVec, Fin.sum_univ_three,
      Pi.sub_apply, PiLp.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
      Pi.smul_apply, smul_eq_mul]
    simp
    ring

/-- The form of `cwU_sub` at a wall lattice vector. -/
lemma cwU_sub_wall (a : Fin 48) (i : Fin 3) (side : Fin 2) (y : CuspE3) (s : ℝ) :
    cwU (y - wallLamV a i side) s
      = (1 / 2 : ℝ) • (cwT2R (wallLam a i side) *ᵥ cwU y s) :=
  cwU_sub y s (wallLam a i side)

/-! ### The sign change on the fifth coordinate -/

/-- The `ℤ`-valued sign pattern of a `Gg`-element, extended to `Fin 5`. -/
def cwSignZ (g : Fin 4 → ZMod 2) : Fin 5 → ℤ :=
  fun k => if h : (k : ℕ) < 4 then Work.FoldInst.signVec g ⟨k, h⟩ else 1

/-- The real-valued sign pattern. -/
def cwSignExt (g : Fin 4 → ZMod 2) : Fin 5 → ℝ := fun k => (cwSignZ g k : ℝ)

lemma cwAct_apply (g : Fin 4 → ZMod 2) (z : CuspE4) (k : Fin 4) :
    Work.FoldInst.act g z k = (Work.FoldInst.signVec g k : ℝ) * z k := by
  simp only [Work.FoldInst.act, Work.HypModel.rot4]
  fin_cases k <;> simp [Matrix.diagonal, Fin.sum_univ_four]

/-- **The sign change commutes with the Klein map.** -/
lemma cwKlein_signExt (g : Fin 4 → ZMod 2) (P : Work.HypModel.V5) :
    Work.HypModel.kleinOfHyp (cwSignExt g * P)
      = Work.FoldInst.act g (Work.HypModel.kleinOfHyp P) := by
  ext k
  fin_cases k <;>
  · simp only [Work.HypModel.kleinOfHyp, Work.HypModel.proj4, Pi.mul_apply, Pi.smul_apply,
      smul_eq_mul, cwSignExt, cwSignZ, cwAct_apply]
    norm_num
    ring

/-! ### The diagonal action on matrices -/

/-- The `ℤ`-valued diagonal sign matrix. -/
def cwDiagZ (g : Fin 4 → ZMod 2) : Matrix (Fin 5) (Fin 5) ℤ := Matrix.diagonal (cwSignZ g)

/-- The real-valued diagonal sign matrix. -/
def cwDiagR (g : Fin 4 → ZMod 2) : Matrix (Fin 5) (Fin 5) ℝ := Matrix.diagonal (cwSignExt g)

lemma cwDiagZ_mul_apply (g : Fin 4 → ZMod 2) (a : Fin 48) (k j : Fin 5) :
    (cwDiagZ g * chartMat a) k j = cwSignZ g k * chartMat a k j := by
  rw [cwDiagZ, Matrix.diagonal_mul]

lemma cwDiagR_mul_apply (g : Fin 4 → ZMod 2) (a : Fin 48) (k j : Fin 5) :
    (cwDiagR g * cwMat a) k j = cwSignExt g k * (chartMat a k j : ℝ) := by
  rw [cwDiagR, Matrix.diagonal_mul]
  rfl

lemma cwMat_mul_T2R_apply (a : Fin 48) (l : Fin 3 → ℤ) (k j : Fin 5) :
    (cwMat a * cwT2R l) k j = ((chartMat a * cwT2 l) k j : ℝ) := by
  simp only [cwMat, cwT2R, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_five]
  push_cast
  ring

lemma cwDiagR_mulVec (g : Fin 4 → ZMod 2) (a : Fin 48) (W : Fin 5 → ℝ) :
    (cwDiagR g * cwMat a) *ᵥ W = cwSignExt g * (cwMat a *ᵥ W) := by
  have hmat : cwDiagR g * cwMat a
      = Matrix.of (fun k j => cwSignExt g k * (chartMat a k j : ℝ)) := by
    ext k j
    rw [cwDiagR_mul_apply, Matrix.of_apply]
  rw [hmat]
  funext k
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, cwMat, Pi.mul_apply, Fin.sum_univ_five]
  ring

lemma cwRankOne_mulVec (G F W : Fin 5 → ℝ) (k : Fin 5) :
    (Matrix.of (fun k j => G k * F j) *ᵥ W) k = G k * ∑ j, F j * W j := by
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_five]
  ring

/-! ### The correction term -/

/-- `i` as an element of `Fin 5`. -/
def cwI5 (i : Fin 3) : Fin 5 := ⟨i, by omega⟩

/-- The wall value `cubeCorner a i + (0,1)` as an integer. -/
def cwC (a : Fin 48) (i : Fin 3) (side : Fin 2) : ℤ :=
  (Work.Cusp.cubeCorner a i : ℤ) + (if (side : ℕ) = 0 then 0 else 1)

lemma cwC_eq (a : Fin 48) (i : Fin 3) (side : Fin 2) :
    (cwC a i side : ℝ)
      = (Work.Cusp.cubeCorner a i : ℝ) + (if (side : ℕ) = 0 then 0 else 1) := by
  rw [cwC]
  push_cast
  split <;> norm_num

/-- The coefficients of the correction functional on the wall. -/
def cwFv (a : Fin 48) (i : Fin 3) (side : Fin 2) : Fin 5 → ℤ :=
  fun j => if (j : ℕ) = (i : ℕ) then 1
    else if (j : ℕ) = 3 then cwC a i side
    else if (j : ℕ) = 4 then -cwC a i side
    else 0

/-- The correction functional applied to the homogenised UHS vector is `2 (y i - c)`. -/
lemma cwFv_sum (a : Fin 48) (i : Fin 3) (side : Fin 2) (y : CuspE3) (s : ℝ) :
    ∑ j : Fin 5, (cwFv a i side j : ℝ) * cwU y s j
      = 2 * (y i - (cwC a i side : ℝ)) := by
  fin_cases i <;>
  · simp only [cwFv, cwU, cwQ, Fin.sum_univ_five, Fin.sum_univ_three, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four]
    norm_num
    ring

/-- The integer matrix of the correction: `chartMat b · cwT2 λ - 2 · (D · chartMat a)`. -/
def cwA2 (a : Fin 48) (i : Fin 3) (side : Fin 2) : Matrix (Fin 5) (Fin 5) ℤ :=
  chartMat (wallNb a i side) * cwT2 (wallLam a i side)
    - (2 : ℤ) • (cwDiagZ (wallGamK a i side) * chartMat a)

/-- **The finite verification**: the wall relation of the chart matrices, with a rank-one
correction whose rows are multiples of the correction functional `cwFv`. -/
theorem cwWallMat_pt : ∀ (a : Fin 48) (i : Fin 3) (side : Fin 2) (k j : Fin 5),
    (chartMat (wallNb a i side) * cwT2 (wallLam a i side)) k j
      = ((2 : ℤ) • (cwDiagZ (wallGamK a i side) * chartMat a)) k j
        + cwA2 a i side k (cwI5 i) * cwFv a i side j := by
  decide +kernel

/-- The real form of the finite verification. -/
lemma cwWallR (a : Fin 48) (i : Fin 3) (side : Fin 2) (k j : Fin 5) :
    (cwMat (wallNb a i side) * cwT2R (wallLam a i side)) k j
      = 2 * (cwDiagR (wallGamK a i side) * cwMat a) k j
        + (cwA2 a i side k (cwI5 i) : ℝ) * (cwFv a i side j : ℝ) := by
  rw [cwMat_mul_T2R_apply, cwDiagR_mul_apply, cwWallMat_pt a i side k j]
  simp only [Matrix.smul_apply, smul_eq_mul, cwDiagZ_mul_apply, cwSignExt]
  push_cast
  ring

/-- **The wall relation on the chart vectors.** -/
theorem cwVec_wall (a : Fin 48) (i : Fin 3) (side : Fin 2) (y : CuspE3) (s : ℝ)
    (hy : y i = (Work.Cusp.cubeCorner a i : ℝ) + (if (side : ℕ) = 0 then 0 else 1)) :
    cwVec (wallNb a i side) (y - wallLamV a i side) s
      = cwSignExt (wallGamK a i side) * cwVec a y s := by
  have hcy : y i - (cwC a i side : ℝ) = 0 := by
    rw [cwC_eq]; linarith
  have hmat : cwMat (wallNb a i side) * cwT2R (wallLam a i side)
      = (2 : ℝ) • (cwDiagR (wallGamK a i side) * cwMat a)
        + Matrix.of (fun k j => (cwA2 a i side k (cwI5 i) : ℝ)
            * (cwFv a i side j : ℝ)) := by
    ext k j
    rw [cwWallR a i side k j, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  funext k
  calc cwVec (wallNb a i side) (y - wallLamV a i side) s k
      = (cwMat (wallNb a i side) *ᵥ cwU (y - wallLamV a i side) s) k := rfl
    _ = (cwMat (wallNb a i side) *ᵥ
          ((1 / 2 : ℝ) • (cwT2R (wallLam a i side) *ᵥ cwU y s))) k := by
          rw [cwU_sub_wall]
    _ = ((1 / 2 : ℝ) •
          ((cwMat (wallNb a i side) * cwT2R (wallLam a i side)) *ᵥ cwU y s)) k := by
          rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    _ = cwSignExt (wallGamK a i side) k * cwVec a y s k := by
          rw [hmat, Matrix.add_mulVec, Matrix.smul_mulVec]
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rw [cwDiagR_mulVec,
            cwRankOne_mulVec (fun k => (cwA2 a i side k (cwI5 i) : ℝ))
              (fun j => (cwFv a i side j : ℝ)) (cwU y s) k,
            cwFv_sum a i side y s, hcy]
          simp only [Pi.mul_apply, cwVec, mul_zero, add_zero, mul_one]
          ring
    _ = (cwSignExt (wallGamK a i side) * cwVec a y s) k := by rw [Pi.mul_apply]

/-- **The wall gluing certificate of the cusp cube charts.** -/
theorem chartKlein_wall (a : Fin 48) (i : Fin 3) (side : Fin 2) {y : Work.RTOwed.CuspE3}
    (hy : y i = (Work.Cusp.cubeCorner a i : ℝ) + (if (side : ℕ) = 0 then 0 else 1))
    (hz : ∀ j : Fin 3, (Work.Cusp.cubeCorner a j : ℝ) ≤ y j ∧
      y j ≤ (Work.Cusp.cubeCorner a j : ℝ) + 1)
    {s : ℝ} (hs : 11 / 10 ≤ s) :
    Work.RTOwed.chartKlein (Work.RTOwed.wallNb a i side)
        (Work.RTOwed.mkE4 (y - Work.RTOwed.wallLamV a i side) s) =
      Work.FoldInst.act (Work.RTOwed.wallGamK a i side)
        (Work.RTOwed.chartKlein a (Work.RTOwed.mkE4 y s)) := by
  have hs0 : s ≠ 0 := by linarith
  rw [cwChart _ _ _ hs0, cwChart _ _ _ hs0, cwVec_wall a i side y s hy, cwKlein_signExt]

end

end Work.RTOwed
