import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Avalanche.dframe

/-!
# Row norms of a `2×2` complex matrix

For the proof of the avalanche principle we need the *Euclidean* norms of the two rows of a
`2×2` matrix (the norm on the plain function type `Fin 2 → ℂ` is the sup norm, which is not
what is wanted).  We package a row as an element of `EuclideanSpace ℂ (Fin 2)`, where the
whole normed-space API (triangle inequality, `norm_smul`, …) is available.

The main content is that left multiplication by `W` acts on the row vector as the linear
combination `W i 0 • row₀ + W i 1 • row₁`, so row norms obey the triangle (and reverse
triangle) inequalities; for unitary `W` these give the step estimates used in the induction.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

noncomputable section

namespace Work.TMC7Core.Avalanche

/-- The `i`-th row of a `2×2` matrix, as a vector of `ℂ²` with the Euclidean norm. -/
def rowE (N : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) : EuclideanSpace ℂ (Fin 2) :=
  (WithLp.equiv 2 (Fin 2 → ℂ)).symm (fun j => N i j)

@[simp] lemma rowE_ofLp (N : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    (rowE N i).ofLp j = N i j := by
  simp [rowE]

lemma rowE_norm (N : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) :
    ‖rowE N i‖ = Real.sqrt (‖N i 0‖ ^ 2 + ‖N i 1‖ ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [rowE_ofLp, Fin.sum_univ_two]

lemma rowE_sq (N : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) :
    ‖rowE N i‖ ^ 2 = ‖N i 0‖ ^ 2 + ‖N i 1‖ ^ 2 := by
  rw [rowE_norm, Real.sq_sqrt (by positivity)]

lemma frob_sq_eq_rowE (N : Matrix (Fin 2) (Fin 2) ℂ) :
    frob N ^ 2 = ‖rowE N 0‖ ^ 2 + ‖rowE N 1‖ ^ 2 := by
  rw [frob_sq, rowE_sq, rowE_sq]
  ring

lemma rowE_mul_row0 (W N : Matrix (Fin 2) (Fin 2) ℂ) :
    rowE (W * N) 0 = W 0 0 • rowE N 0 + W 0 1 • rowE N 1 := by
  ext j
  simp only [rowE_ofLp, Matrix.mul_apply, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply,
    WithLp.ofLp_add, WithLp.ofLp_smul]
  ring

lemma rowE_mul_row1 (W N : Matrix (Fin 2) (Fin 2) ℂ) :
    rowE (W * N) 1 = W 1 0 • rowE N 0 + W 1 1 • rowE N 1 := by
  ext j
  simp only [rowE_ofLp, Matrix.mul_apply, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply,
    WithLp.ofLp_add, WithLp.ofLp_smul]
  ring

lemma rowE_mul_row0_le (W N : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖rowE (W * N) 0‖ ≤ ‖W 0 0‖ * ‖rowE N 0‖ + ‖W 0 1‖ * ‖rowE N 1‖ := by
  rw [rowE_mul_row0]
  calc ‖W 0 0 • rowE N 0 + W 0 1 • rowE N 1‖
      ≤ ‖W 0 0 • rowE N 0‖ + ‖W 0 1 • rowE N 1‖ := norm_add_le _ _
    _ = ‖W 0 0‖ * ‖rowE N 0‖ + ‖W 0 1‖ * ‖rowE N 1‖ := by rw [norm_smul, norm_smul]

lemma rowE_mul_row0_ge (W N : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖W 0 0‖ * ‖rowE N 0‖ - ‖W 0 1‖ * ‖rowE N 1‖ ≤ ‖rowE (W * N) 0‖ := by
  have h := norm_add_le (W 0 0 • rowE N 0 + W 0 1 • rowE N 1) (-(W 0 1 • rowE N 1))
  have h2 : (W 0 0 • rowE N 0 + W 0 1 • rowE N 1) + -(W 0 1 • rowE N 1)
      = W 0 0 • rowE N 0 := by abel
  rw [h2, norm_neg, norm_smul, norm_smul] at h
  rw [rowE_mul_row0]
  linarith [h]

lemma rowE_mul_row1_le (W N : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖rowE (W * N) 1‖ ≤ ‖W 1 0‖ * ‖rowE N 0‖ + ‖W 1 1‖ * ‖rowE N 1‖ := by
  rw [rowE_mul_row1]
  calc ‖W 1 0 • rowE N 0 + W 1 1 • rowE N 1‖
      ≤ ‖W 1 0 • rowE N 0‖ + ‖W 1 1 • rowE N 1‖ := norm_add_le _ _
    _ = ‖W 1 0‖ * ‖rowE N 0‖ + ‖W 1 1‖ * ‖rowE N 1‖ := by rw [norm_smul, norm_smul]

/-! ## The diagonal scaling `Dm` -/

lemma rowE_Dm_mul_row0 (s : ℝ) (N : Matrix (Fin 2) (Fin 2) ℂ) :
    rowE (Dm s * N) 0 = ((s : ℝ) : ℂ) • rowE N 0 := by
  ext j
  simp only [rowE_ofLp, Matrix.mul_apply, Fin.sum_univ_two, Pi.smul_apply, WithLp.ofLp_smul, Dm,
    Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne]
  simp [Fin.isValue]

lemma rowE_Dm_mul_row1 (s : ℝ) (N : Matrix (Fin 2) (Fin 2) ℂ) :
    rowE (Dm s * N) 1 = ((s⁻¹ : ℝ) : ℂ) • rowE N 1 := by
  ext j
  simp only [rowE_ofLp, Matrix.mul_apply, Fin.sum_univ_two, Pi.smul_apply, WithLp.ofLp_smul, Dm,
    Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne]
  simp [Fin.isValue]

lemma norm_rowE_Dm_mul_row0 (s : ℝ) (hs : 0 ≤ s) (N : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖rowE (Dm s * N) 0‖ = s * ‖rowE N 0‖ := by
  rw [rowE_Dm_mul_row0, norm_smul]
  have : ‖((s : ℝ) : ℂ)‖ = s := by
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hs]
  rw [this]

lemma norm_rowE_Dm_mul_row1 (s : ℝ) (hs : 0 ≤ s) (N : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖rowE (Dm s * N) 1‖ = s⁻¹ * ‖rowE N 1‖ := by
  rw [rowE_Dm_mul_row1, norm_smul]
  have : ‖((s⁻¹ : ℝ) : ℂ)‖ = s⁻¹ := by
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (inv_nonneg.mpr hs)]
  rw [this]

/-! ## The entries of a unitary `2×2` matrix -/

lemma star_mul_self (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm (star z) z, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma mul_star_self (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- For unitary `W` (`Wᴴ · W = 1`), `‖W 1 0‖ ^ 2 = 1 - ‖W 0 0‖ ^ 2`. -/
lemma unitary_entry10_sq (W : Matrix (Fin 2) (Fin 2) ℂ) (hW : W.conjTranspose * W = 1) :
    ‖W 1 0‖ ^ 2 = 1 - ‖W 0 0‖ ^ 2 := by
  have h00 : (W.conjTranspose * W) 0 0
      = ((‖W 0 0‖ ^ 2 : ℝ) : ℂ) + ((‖W 1 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.conjTranspose_apply]
    rw [star_mul_self, star_mul_self]
  have h : ((‖W 0 0‖ ^ 2 : ℝ) : ℂ) + ((‖W 1 0‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h00, hW, Matrix.one_apply_eq]
  have h3 := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re] at h3
  linarith

/-- For unitary `W` (`W · Wᴴ = 1`), `‖W 0 1‖ ^ 2 = 1 - ‖W 0 0‖ ^ 2`. -/
lemma unitary_entry01_sq (W : Matrix (Fin 2) (Fin 2) ℂ) (hW : W * W.conjTranspose = 1) :
    ‖W 0 1‖ ^ 2 = 1 - ‖W 0 0‖ ^ 2 := by
  have h00 : (W * W.conjTranspose) 0 0
      = ((‖W 0 0‖ ^ 2 : ℝ) : ℂ) + ((‖W 0 1‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.conjTranspose_apply]
    rw [mul_star_self, mul_star_self]
  have h : ((‖W 0 0‖ ^ 2 : ℝ) : ℂ) + ((‖W 0 1‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h00, hW, Matrix.one_apply_eq]
  have h3 := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re] at h3
  linarith

/-- For unitary `W`, `‖W 1 1‖ ^ 2 = ‖W 0 0‖ ^ 2`. -/
lemma unitary_entry11_sq (W : Matrix (Fin 2) (Fin 2) ℂ)
    (hW : W.conjTranspose * W = 1) (hW' : W * W.conjTranspose = 1) :
    ‖W 1 1‖ ^ 2 = ‖W 0 0‖ ^ 2 := by
  have h11 : (W.conjTranspose * W) 1 1
      = ((‖W 0 1‖ ^ 2 : ℝ) : ℂ) + ((‖W 1 1‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.conjTranspose_apply]
    rw [star_mul_self, star_mul_self]
  have h : ((‖W 0 1‖ ^ 2 : ℝ) : ℂ) + ((‖W 1 1‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h11, hW, Matrix.one_apply_eq]
  have h3 := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re] at h3
  have h4 := unitary_entry01_sq W hW'
  linarith

end Work.TMC7Core.Avalanche
