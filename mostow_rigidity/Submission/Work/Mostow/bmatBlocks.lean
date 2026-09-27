import Mathlib
import Submission.Work.Mostow.HaarBase

/-!
# Block decomposition of the hyperbolic boost `bmat v`

The matrix `bmat v` (see `HaarBase`) is the hyperbolic boost sending `e₀ = hlift 0` to
`hlift v`.  It is displayed in `2 × 2` blocks

* `bA v = 1 + (1 + tpart v)⁻¹ • v vᵀ`  (`n × n`),
* `bB v = v` as a column (`n × 1`),
* `bC v = vᵀ` as a row (`1 × n`),
* `bD v = tpart v • 1` (`1 × 1`),

and the elementary identities collected here reduce the verification that `bmat v` lies in
`O(n,1)` — i.e. that `(bmat v)ᵀ J (bmat v) = J` with `J = diag(1, …, 1, -1)` — to four block
computations.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity Matrix
open scoped ENNReal Topology

noncomputable section

variable {n : ℕ}

/-- The rank-one symmetric matrix `v vᵀ`. -/
def bvv (v : E n) : Matrix (Fin n) (Fin n) ℝ := Matrix.vecMulVec v v

/-- The scalar `‖v‖²`, written as a sum. -/
def bN (v : E n) : ℝ := ∑ i, v i * v i

/-- The `(1,1)` block of `bmat v`. -/
def bA (v : E n) : Matrix (Fin n) (Fin n) ℝ := 1 + (1 + tpart v)⁻¹ • bvv v

/-- The `(1,2)` block of `bmat v`. -/
def bB (v : E n) : Matrix (Fin n) (Fin 1) ℝ := Matrix.replicateCol (Fin 1) (fun i => v i)

/-- The `(2,1)` block of `bmat v`. -/
def bC (v : E n) : Matrix (Fin 1) (Fin n) ℝ := Matrix.replicateRow (Fin 1) (fun i => v i)

/-- The `(2,2)` block of `bmat v`. -/
def bD (v : E n) : Matrix (Fin 1) (Fin 1) ℝ := tpart v • 1

@[simp] lemma bvv_apply (v : E n) (i j : Fin n) : bvv v i j = v i * v j := by
  rw [bvv, Matrix.vecMulVec_apply]

@[simp] lemma bB_apply (v : E n) (i : Fin n) (j : Fin 1) : bB v i j = v i := by
  rw [bB, Matrix.replicateCol_apply]

@[simp] lemma bC_apply (v : E n) (i : Fin 1) (j : Fin n) : bC v i j = v j := by
  rw [bC, Matrix.replicateRow_apply]

@[simp] lemma bD_apply (v : E n) (i j : Fin 1) : bD v i j = tpart v * (1 : Matrix (Fin 1) (Fin 1) ℝ) i j := by
  rw [bD, Matrix.smul_apply, smul_eq_mul]

/-! ## Elementary products -/

@[simp] lemma bvv_mul_self (v : E n) : bvv v * bvv v = bN v • bvv v := by
  rw [bvv, bN]
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
  rw [show (∑ k, v i * v k * (v k * v j)) = (∑ k, v k * v k) * (v i * v j) from by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring]

lemma bB_mul_bC (v : E n) : bB v * bC v = bvv v := by
  rw [bB, bC, bvv]
  ext i j
  simp [Matrix.mul_apply, Matrix.vecMulVec_apply]

lemma bC_mul_bB (v : E n) :
    bC v * bB v = bN v • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  rw [bC, bB, bN]
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.replicateRow_apply, Matrix.replicateCol_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  rw [Subsingleton.elim i j]
  simp

lemma bvv_mul_bB (v : E n) : bvv v * bB v = bN v • bB v := by
  rw [bvv, bB, bN]
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.replicateCol_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma bC_mul_bvv (v : E n) : bC v * bvv v = bN v • bC v := by
  rw [bvv, bC, bN]
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.replicateRow_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ## Transposes -/

@[simp] lemma transpose_bvv (v : E n) : (bvv v)ᵀ = bvv v := by
  rw [bvv, Matrix.transpose_vecMulVec]

@[simp] lemma transpose_bA (v : E n) : (bA v)ᵀ = bA v := by
  rw [bA, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, transpose_bvv]

@[simp] lemma transpose_bB (v : E n) : (bB v)ᵀ = bC v := by
  ext i j
  simp [Matrix.transpose_apply]

@[simp] lemma transpose_bC (v : E n) : (bC v)ᵀ = bB v := by
  ext i j
  simp [Matrix.transpose_apply]

@[simp] lemma transpose_bD (v : E n) : (bD v)ᵀ = bD v := by
  rw [bD, Matrix.transpose_smul, Matrix.transpose_one]

/-! ## The block products -/

lemma bA_mul_self (v : E n) :
    bA v * bA v = 1 + (2 * (1 + tpart v)⁻¹ + ((1 + tpart v)⁻¹) ^ 2 * bN v) • bvv v := by
  simp only [bA, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, bvv_mul_self]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, bvv,
    Matrix.vecMulVec_apply]
  ring

lemma bA_mul_bB (v : E n) : bA v * bB v = (1 + (1 + tpart v)⁻¹ * bN v) • bB v := by
  simp only [bA, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, bvv_mul_bB]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, bB, Matrix.replicateCol_apply]
  ring

lemma bC_mul_bA (v : E n) : bC v * bA v = (1 + (1 + tpart v)⁻¹ * bN v) • bC v := by
  simp only [bA, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, bC_mul_bvv]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, bC, Matrix.replicateRow_apply]
  ring

lemma bB_mul_bD (v : E n) : bB v * bD v = tpart v • bB v := by
  simp only [bD, Matrix.mul_smul, Matrix.mul_one]

lemma bD_mul_bC (v : E n) : bD v * bC v = tpart v • bC v := by
  simp only [bD, Matrix.smul_mul, Matrix.one_mul]

lemma bD_mul_bD (v : E n) : bD v * bD v = tpart v ^ 2 • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  rw [bD, Matrix.smul_mul, Matrix.one_mul, smul_smul, pow_two]

/-! ## Scalar identities -/

lemma bN_eq_norm_sq (v : E n) : bN v = ‖v‖ ^ 2 := by
  rw [bN, ← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial]

lemma tpart_sq' (v : E n) : tpart v ^ 2 = 1 + bN v := by
  rw [tpart, Real.sq_sqrt (by positivity), bN_eq_norm_sq]

lemma one_add_inv_mul_bN (v : E n) : 1 + (1 + tpart v)⁻¹ * bN v = tpart v := by
  have h : (1 + tpart v) ≠ 0 := by
    have := tpart_pos v; positivity
  have hsq := tpart_sq' v
  field_simp
  nlinarith [hsq]

lemma two_inv_add_inv_sq_mul_bN (v : E n) :
    2 * (1 + tpart v)⁻¹ + ((1 + tpart v)⁻¹) ^ 2 * bN v = 1 := by
  have h : (1 + tpart v) ≠ 0 := by
    have := tpart_pos v; positivity
  have hsq := tpart_sq' v
  field_simp
  nlinarith [hsq]


/-! ## The four block identities for `(bmat v)ᵀ J (bmat v) = J` -/

section BlockIdentities

variable (v : E n)

theorem bA_gram :
    (bA v)ᵀ * bA v - (bC v)ᵀ * bC v = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [transpose_bA, transpose_bC, bB_mul_bC, bA_mul_self, two_inv_add_inv_sq_mul_bN]
  simp

theorem bA_bB_orth :
    (bA v)ᵀ * bB v - (bC v)ᵀ * bD v = (0 : Matrix (Fin n) (Fin 1) ℝ) := by
  rw [transpose_bA, transpose_bC, bA_mul_bB, bB_mul_bD, one_add_inv_mul_bN, sub_self]

theorem bB_bA_orth :
    (bB v)ᵀ * bA v - (bD v)ᵀ * bC v = (0 : Matrix (Fin 1) (Fin n) ℝ) := by
  rw [transpose_bB, transpose_bD, bC_mul_bA, bD_mul_bC, one_add_inv_mul_bN, sub_self]

theorem bB_gram :
    (bB v)ᵀ * bB v - (bD v)ᵀ * bD v = (-1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  rw [transpose_bB, transpose_bD, bC_mul_bB, bD_mul_bD, tpart_sq', ← sub_smul]
  norm_num

end BlockIdentities

/-! ## The block decomposition of `bmat` -/

lemma replicateCol_mul_replicateRow (v : E n) :
    Matrix.replicateCol (Fin 1) (fun i => v i) * Matrix.replicateRow (Fin 1) (fun i => v i)
      = Matrix.vecMulVec v v := by
  ext i j
  simp [Matrix.mul_apply, Matrix.vecMulVec_apply]

theorem bmat_eq_blocks (v : E n) :
    bmat v = Matrix.fromBlocks (bA v) (bB v) (bC v) (bD v) := by
  rw [bmat, bA, bB, bC, bD, one_div, bvv, replicateCol_mul_replicateRow]

end

end Work.Mostow
