import Mathlib
import Submission.Work.RTOwed.cuspChart
import Submission.Work.RTOwed.chartKlein_image_open
import Submission.Work.RTOwed.chartKlein_mem
import Submission.Work.HypModel.Main
import Submission.Work.FoldInst.isOpen_foldTheta_image

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.RTOwed

noncomputable section

open scoped Matrix BigOperators
open Matrix Set Topology Function

/-! ## The integer transition matrix `tP` -/

/-- The integer transition matrix of the two cube charts: `Jz · (chartMat b)ᵀ · Jz · chartMat a`.
Its real version, divided by `chartScale a * chartScale b`, is `(chartK b)⁻¹ * chartK a`. -/
def tP (a b : Fin 48) : Matrix (Fin 5) (Fin 5) ℤ := Jz * (chartMat b)ᵀ * Jz * chartMat a

/-- The embedding `Fin 3 → Fin 5` of the horizontal coordinates. -/
def t3to5 (i : Fin 3) : Fin 5 := ⟨(i : ℕ), by omega⟩

@[simp] lemma t3to5_zero : t3to5 0 = (0 : Fin 5) := rfl
@[simp] lemma t3to5_one : t3to5 1 = (1 : Fin 5) := rfl
@[simp] lemma t3to5_two : t3to5 2 = (2 : Fin 5) := rfl

/-- The quadratic coefficient of the transition height functional `tDel`. -/
def tCp (a b : Fin 48) : ℤ := tP a b 4 3 - tP a b 3 3 + tP a b 4 4 - tP a b 3 4

/-- The linear coefficients of the transition height functional `tDel`. -/
def tLp (a b : Fin 48) (i : Fin 3) : ℤ := tP a b 4 (t3to5 i) - tP a b 3 (t3to5 i)

/-- The constant of the transition height functional `tDel`. -/
def tEp (a b : Fin 48) : ℤ := -(tP a b 4 3 - tP a b 3 3) + (tP a b 4 4 - tP a b 3 4)

lemma Jz_mul_self : Jz * Jz = (1 : Matrix (Fin 5) (Fin 5) ℤ) := by decide

/-- **The transposed Gram identity of the chart matrix**: `chartMat b · Jz · (chartMat b)ᵀ`
is `(chartScaleZ b)² · Jz`. -/
theorem chartMat_gramT : ∀ b : Fin 48,
    chartMat b * Jz * (chartMat b)ᵀ = (chartScaleZ b)^2 • Jz := by
  decide +revert

/-- The integer identity underlying `tM_spec`: `chartMat b · tP a b = (chartScaleZ b)² · chartMat a`. -/
theorem tP_mul_aux (a b : Fin 48) : chartMat b * tP a b = (chartScaleZ b)^2 • chartMat a := by
  rw [tP]
  rw [show chartMat b * (Jz * (chartMat b)ᵀ * Jz * chartMat a)
      = (chartMat b * Jz * (chartMat b)ᵀ) * (Jz * chartMat a) from by noncomm_ring]
  rw [chartMat_gramT b, Matrix.smul_mul]
  rw [show Jz * (Jz * chartMat a) = (Jz * Jz) * chartMat a from by rw [Matrix.mul_assoc]]
  rw [Jz_mul_self, one_mul]

/-! ## The real transition matrix `tM` -/

/-- The (real) transition matrix `(chartK b)⁻¹ · chartK a`, in explicit form. -/
def tM (a b : Fin 48) : Matrix (Fin 5) (Fin 5) ℝ :=
  (1 / (chartScale a * chartScale b)) • (tP a b).map (Int.castRingHom ℝ)

lemma chartScaleZ_sq_cast (b : Fin 48) :
    (((chartScaleZ b)^2 : ℤ) : ℝ) = (chartScale b)^2 := by
  rw [chartScale]; push_cast; ring

/-- **The transition matrix is the product of the two charts**: `chartK b · tM a b = chartK a`. -/
theorem tM_spec (a b : Fin 48) : chartK b * tM a b = chartK a := by
  have hka : chartScale a ≠ 0 := ne_of_gt (chartScale_pos a)
  have hkb : chartScale b ≠ 0 := ne_of_gt (chartScale_pos b)
  rw [tM, chartK, chartK, chartMatR, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul,
    tP_mul_aux a b, map_smul_int]
  simp only [smul_smul]
  rw [chartScaleZ_sq_cast]
  congr 1
  field_simp

/-! ## `tM` is a Lorentz matrix -/

/-- **A Lorentz matrix has unit determinant**, hence its determinant is a unit. -/
lemma isUnit_det_of_isLorentzMat {A : Matrix (Fin 5) (Fin 5) ℝ}
    (hA : Work.HypModel.IsLorentzMat A) : IsUnit A.det := by
  have h := congrArg Matrix.det hA.1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  have hJ : Work.HypModel.J.det = (-1 : ℝ) := by
    rw [Work.HypModel.J, Matrix.det_diagonal]; simp
  rw [hJ] at h
  have h2 : A.det * A.det = 1 := by nlinarith [h]
  exact IsUnit.of_mul_eq_one A.det h2

/-- **`tM a b` is `(chartK b)⁻¹ · chartK a`.** -/
theorem tM_eq (a b : Fin 48) : tM a b = (chartK b)⁻¹ * chartK a := by
  have h1 : (chartK b)⁻¹ * chartK b = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_det_of_isLorentzMat (chartK_isLorentz b))
  calc tM a b = 1 * tM a b := (one_mul _).symm
    _ = ((chartK b)⁻¹ * chartK b) * tM a b := by rw [h1]
    _ = (chartK b)⁻¹ * (chartK b * tM a b) := by rw [Matrix.mul_assoc]
    _ = (chartK b)⁻¹ * chartK a := by rw [tM_spec a b]

/-- **The transition matrix is a Lorentz matrix.** -/
theorem tM_lorentz (a b : Fin 48) : Work.HypModel.IsLorentzMat (tM a b) := by
  rw [tM_eq]
  exact (Work.FoldInst.isLorentzMat_inv (chartK_isLorentz b)).mul (chartK_isLorentz a)

/-! ## The height functional `tDel` -/

/-- The transition vector: `tP a b` applied to the homogenised UHS vector. -/
def tW (a b : Fin 48) (x : CuspE3) (s : ℝ) (j : Fin 5) : ℝ :=
  ∑ l : Fin 5, ((tP a b) j l : ℝ) * chartKleinMem.uhsVec x s l

/-- The height functional: the `(4,3)`-difference of the transition vector. -/
def tDel (a b : Fin 48) (x : CuspE3) (s : ℝ) : ℝ := tW a b x s 4 - tW a b x s 3

/-- **`tDel` as a quadratic form** with integer coefficients `tCp, tLp, tEp`. -/
theorem tDel_eq (a b : Fin 48) (x : CuspE3) (s : ℝ) :
    tDel a b x s = (tCp a b : ℝ) * chartKleinMem.qsq x s
      + ∑ i : Fin 3, (2 * (tLp a b i : ℝ)) * x i + (tEp a b : ℝ) := by
  simp only [tDel, tW, tCp, tLp, tEp, chartKleinMem.qsq, Fin.sum_univ_five,
    Fin.sum_univ_three, chartKleinMem.uhsVec_zero, chartKleinMem.uhsVec_one,
    chartKleinMem.uhsVec_two, chartKleinMem.uhsVec_three, chartKleinMem.uhsVec_four,
    t3to5_zero, t3to5_one, t3to5_two]
  push_cast
  ring

/-- **`tM` applied to the homogenised UHS vector.** -/
theorem tM_mulVec_aux (a b : Fin 48) (x : CuspE3) (s : ℝ) :
    tM a b *ᵥ chartKleinMem.uhsVec x s
      = (chartScale a * chartScale b)⁻¹ • (fun j => tW a b x s j) := by
  ext j
  simp only [tM, tW, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.smul_apply,
    Fin.sum_univ_five, Pi.smul_apply, smul_eq_mul, Int.coe_castRingHom]
  ring

/-- **`tM` applied to the hyperboloid point**. -/
theorem tM_mulVec (a b : Fin 48) (x : CuspE3) (s : ℝ) :
    tM a b *ᵥ Work.HypModel.hypOfUHS (mkE4 x s)
      = ((2 * s)⁻¹ * (chartScale a * chartScale b)⁻¹) • (fun j => tW a b x s j) := by
  rw [chartKleinMem.hypOfUHS_mkE4, Matrix.mulVec_smul, tM_mulVec_aux, smul_smul]

/-- **The `(4,3)`-difference of the transition vector.** -/
theorem tM_mulVec_43 (a b : Fin 48) (x : CuspE3) (s : ℝ) :
    (tM a b *ᵥ Work.HypModel.hypOfUHS (mkE4 x s)) 4
        - (tM a b *ᵥ Work.HypModel.hypOfUHS (mkE4 x s)) 3
      = (2 * s)⁻¹ * (chartScale a * chartScale b)⁻¹ * tDel a b x s := by
  rw [tM_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul, tDel]
  ring

end

end Work.RTOwed
