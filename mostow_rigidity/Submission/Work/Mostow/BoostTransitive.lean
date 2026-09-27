import Mathlib
import Submission.Work.Mostow.poAux

/-!
# Transitivity of the `PO(n,1)`-action on hyperbolic space (assisting area T1)

Assuming `POActionProp n` (the group-action interface of the lead), the isometry group
`PO(n,1)` acts transitively on the hyperboloid chart `E n` of hyperbolic space.  The only
substantive input is an explicit family of *boosts*: for every unit vector `e : E n` and real
numbers `r`, `t` with `t ^ 2 - r ^ 2 = 1`, `t > 0` the matrix

  `boostMat e r t = fromBlocks (1 + (t-1) • (e eᵀ)) (r e) (r eᵀ) (t)`

lies in `O(n,1)` and sends the base point `0` to `r • e`.  Varying `r` and `e` gives
transitivity; the rest is bookkeeping with the action laws in `POActionProp`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open Matrix

noncomputable section

variable {n : ℕ}

/-- A column vector `c` with a single column, entries `e i`. -/
def colVec (e : E n) : Matrix (Fin n) (Fin 1) ℝ := fun i _ => e i

@[simp] lemma colVec_apply (e : E n) (i : Fin n) (j : Fin 1) : colVec e i j = e i := rfl

/-- The `n×n` block of a boost in direction `e`, with parameter `t`. -/
def boostP (e : E n) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 + (t - 1) • (colVec e * (colVec e)ᵀ)

/-- The `1×1` (time) block of a boost. -/
def boostD (t : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := t • 1

/-- The boost matrix in direction `e` with parameters `r`, `t`:
`(x, x₀) ↦ (x + ((t-1)⟪e,x⟫ + r x₀) e, r ⟪e,x⟫ + t x₀)`. -/
def boostMat (e : E n) (r t : ℝ) : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks (boostP e t) (r • colVec e) (r • (colVec e)ᵀ) (boostD t)

lemma boostP_transpose (e : E n) (t : ℝ) : (boostP e t)ᵀ = boostP e t := by simp [boostP]
lemma boostD_transpose (t : ℝ) : (boostD t)ᵀ = boostD t := by simp [boostD]

lemma boostMat_transpose (e : E n) (r t : ℝ) : (boostMat e r t)ᵀ = boostMat e r t := by
  rw [boostMat, Matrix.fromBlocks_transpose, boostP_transpose, boostD_transpose]
  simp [Matrix.transpose_smul]

lemma colVec_gram (e : E n) (he : ‖e‖ = 1) : (colVec e)ᵀ * colVec e = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, colVec_apply, Matrix.one_apply_eq,
    ← pow_two, ← norm_sq_eq_sum, he]
  norm_num

lemma boost_outer_sq (e : E n) (he : ‖e‖ = 1) :
    (colVec e * (colVec e)ᵀ) * (colVec e * (colVec e)ᵀ) = colVec e * (colVec e)ᵀ := by
  rw [← Matrix.mul_assoc (colVec e * (colVec e)ᵀ) (colVec e) (colVec e)ᵀ,
      Matrix.mul_assoc (colVec e) (colVec e)ᵀ (colVec e), colVec_gram e he, Matrix.mul_one]

lemma boostP_sq (e : E n) (t : ℝ) (he : ‖e‖ = 1) :
    boostP e t * boostP e t = 1 + (2 * (t - 1) + (t - 1) ^ 2) • (colVec e * (colVec e)ᵀ) := by
  simp only [boostP, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, boost_outer_sq e he, smul_add, add_smul, smul_smul]
  module

lemma boost_block11 (e : E n) (r t : ℝ) (he : ‖e‖ = 1) (htr : t ^ 2 - r ^ 2 = 1) :
    boostP e t * boostP e t - (r • colVec e) * (r • (colVec e)ᵀ) = 1 := by
  rw [boostP_sq e t he]
  have hr : r * r = r ^ 2 := by ring
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hr, add_sub_assoc, ← sub_smul]
  have hcoef : 2 * (t - 1) + ((t - 1) ^ 2 - r ^ 2) = 0 := by nlinarith [htr]
  rw [hcoef, zero_smul, add_zero]

lemma boost_block12 (e : E n) (r t : ℝ) (he : ‖e‖ = 1) :
    boostP e t * (r • colVec e) - (r • colVec e) * boostD t = 0 := by
  have hSc : (colVec e * (colVec e)ᵀ) * colVec e = colVec e := by
    rw [Matrix.mul_assoc, colVec_gram e he, Matrix.mul_one]
  simp only [boostP, boostD, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
    hSc, Matrix.mul_one, smul_smul, sub_eq_zero]
  module

lemma boost_block21 (e : E n) (r t : ℝ) (he : ‖e‖ = 1) :
    (r • (colVec e)ᵀ) * boostP e t - boostD t * (r • (colVec e)ᵀ) = 0 := by
  have hcS : (colVec e)ᵀ * (colVec e * (colVec e)ᵀ) = (colVec e)ᵀ := by
    rw [← Matrix.mul_assoc, colVec_gram e he, Matrix.one_mul]
  simp only [boostP, boostD, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    hcS, Matrix.one_mul, smul_smul, sub_eq_zero]
  module

lemma boost_block22 (e : E n) (r t : ℝ) (he : ‖e‖ = 1) (htr : t ^ 2 - r ^ 2 = 1) :
    (r • (colVec e)ᵀ) * (r • colVec e) - boostD t * boostD t = -1 := by
  have hr : r * r = r ^ 2 := by ring
  have ht : t * t = t ^ 2 := by ring
  simp only [boostD, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hr, ht,
    colVec_gram e he, ← sub_smul]
  have hcoef : r ^ 2 - t ^ 2 = -1 := by nlinarith [htr]
  rw [hcoef]
  simp

/-- The boost matrix lies in `O(n,1)`: `Mᵀ J M = J`. -/
lemma boostMat_mem (e : E n) (r t : ℝ) (he : ‖e‖ = 1) (htr : t ^ 2 - r ^ 2 = 1) :
    boostMat e r t * pmOneMat * boostMat e r t = pmOneMat := by
  have h11 := boost_block11 e r t he htr
  have h12 := boost_block12 e r t he
  have h21 := boost_block21 e r t he
  have h22 := boost_block22 e r t he htr
  have hMJ : boostMat e r t * pmOneMat
      = Matrix.fromBlocks (boostP e t) (-(r • colVec e)) (r • (colVec e)ᵀ) (-(boostD t)) := by
    rw [boostMat, pmOneMat, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Matrix.mul_neg]
  rw [show boostMat e r t * pmOneMat * boostMat e r t
        = (boostMat e r t * pmOneMat) * boostMat e r t from rfl, hMJ, boostMat, pmOneMat,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Matrix.neg_mul, Matrix.mul_neg, sub_eq_add_neg] using h11
  · simpa only [Matrix.neg_mul, Matrix.mul_neg, sub_eq_add_neg] using h12
  · simpa only [Matrix.neg_mul, Matrix.mul_neg, sub_eq_add_neg] using h21
  · simpa only [Matrix.neg_mul, Matrix.mul_neg, sub_eq_add_neg] using h22

/-- The boost as an element of `O(n,1)`. -/
def boostO (e : E n) (r t : ℝ) (he : ‖e‖ = 1) (htr : t ^ 2 - r ^ 2 = 1) : O1 n :=
  O1.ofMatrix (boostMat e r t)
    ⟨by rw [boostMat_transpose]; exact boostMat_mem e r t he htr,
     by rw [boostMat_transpose]; exact boostMat_mem e r t he htr⟩

@[simp] lemma mat_boostO (e : E n) (r t : ℝ) (he : ‖e‖ = 1) (htr : t ^ 2 - r ^ 2 = 1) :
    mat (boostO e r t he htr) = boostMat e r t := by
  simp [boostO]

lemma tsign_boostO (e : E n) (r t : ℝ) (he : ‖e‖ = 1) (htr : t ^ 2 - r ^ 2 = 1) (ht : 0 < t) :
    tsign (boostO e r t he htr) = 1 := by
  rw [tsign_eq_one_iff, mat_boostO, boostMat, Matrix.fromBlocks_apply₂₂, boostD]
  simpa using ht

/-- The boost sends the base point `0` to `r • e`. -/
lemma actO_boostO_zero (e : E n) (r t : ℝ) (he : ‖e‖ = 1) (htr : t ^ 2 - r ^ 2 = 1)
    (ht : 0 < t) : actO (boostO e r t he htr) (0 : E n) = r • e := by
  rw [actO, tsign_boostO e r t he htr ht, mat_boostO]
  simp only [one_mul]
  rw [hlift_zero, Matrix.mulVec_single_one]
  ext i
  simp [Matrix.col_apply, boostMat, colVec, smul_eq_mul]

theorem BoostTransitive (n : ℕ) (hA : Submission.Mostow.POActionProp n) :
    (∀ u : Submission.Mostow.E n, ∃ g : LeanEval.Geometry.MostowRigidity.PO n 1, g • 0 = u) ∧
    (∀ u v : Submission.Mostow.E n, ∃ g : LeanEval.Geometry.MostowRigidity.PO n 1, g • u = v) := by
  have key : ∀ u : E n, ∃ g : PO n 1, g • 0 = u := by
    intro u
    by_cases hu : u = 0
    · exact ⟨1, by rw [hA.2.2.2.1, hu]⟩
    · have hr : 0 < ‖u‖ := norm_pos_iff.2 hu
      have he : ‖(‖u‖⁻¹ : ℝ) • u‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), inv_mul_cancel₀ hr.ne']
      have htr : (tpart u) ^ 2 - ‖u‖ ^ 2 = 1 := by rw [tpart_sq]; ring
      have ht : 0 < tpart u := tpart_pos u
      refine ⟨(boostO (‖u‖⁻¹ • u) ‖u‖ (tpart u) he htr : O1 n), ?_⟩
      rw [hA.2.1, actO_boostO_zero (‖u‖⁻¹ • u) ‖u‖ (tpart u) he htr ht]
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  refine ⟨key, ?_⟩
  intro u v
  obtain ⟨g1, hg1⟩ := key u
  obtain ⟨g2, hg2⟩ := key v
  have hinv : ∀ (g : PO n 1) (w : E n), g⁻¹ • (g • w) = w := by
    intro g w
    rw [← hA.2.2.2.2.1, inv_mul_cancel, hA.2.2.2.1]
  refine ⟨g2 * g1⁻¹, ?_⟩
  rw [hA.2.2.2.2.1, show g1⁻¹ • u = 0 from by rw [← hg1, hinv], hg2]

end

end Work.Mostow
