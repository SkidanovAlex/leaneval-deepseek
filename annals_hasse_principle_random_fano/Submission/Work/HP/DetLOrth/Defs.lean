import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.Lat.det_inv_compl_block

/-!
# Reciprocal covolume of `orthLat K` for saturated `K ⊆ ℤ^ι` — shared notions

This file sets up the basis/dual-basis/adjacency-matrix technology used by the
delegated lemmas feeding `Work.HP.detgam_orthLat_detL`.

Fix a `ℤ`-basis `b : Basis ι ℤ (ι → ℤ)` of `ℤ^ι` (thought of as the standard lattice with its
Euclidean inner product `⟨x,y⟩ = ∑ᵢ xᵢ yᵢ`).

* `coordMat b` is the integer matrix whose `j`-th *column* is the vector `b j` (rows are standard
  coordinates).
* `dualVec b i` is the `i`-th *dual* basis vector, characterised by `⟨dualVec b i, b j⟩ = δᵢⱼ`:
  it is the integer vector whose `x`-th coordinate is the `i`-th coordinate of the standard basis
  vector `eₓ` of `ℤ^ι`.
* `dualMat b` is the matrix whose `i`-th *row* is `dualVec b i`.
* `gramR b` is the Gram matrix (over `ℝ`) of `b`: `gramR b i j = ⟨b i, b j⟩`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Matrix

namespace Work.HP.DetLOrth

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The integer matrix whose `j`-th column is the `j`-th vector of the `ℤ`-basis `b` of `ℤ^ι`. -/
def coordMat (b : Module.Basis ι ℤ (ι → ℤ)) : Matrix ι ι ℤ := Matrix.of fun x j => (b j) x

/-- The `i`-th element of the dual basis of `b`, characterised by `⟨dualVec b i, b j⟩ = δᵢⱼ`. -/
def dualVec (b : Module.Basis ι ℤ (ι → ℤ)) (i : ι) : ι → ℤ :=
  fun x => b.coord i (Pi.basisFun ℤ ι x)

/-- The matrix whose `i`-th row is the `i`-th dual vector. -/
def dualMat (b : Module.Basis ι ℤ (ι → ℤ)) : Matrix ι ι ℤ := Matrix.of (dualVec b)

/-- The real Gram matrix of the basis `b`, for the standard Euclidean inner product. -/
def gramR (b : Module.Basis ι ℤ (ι → ℤ)) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ∑ x, ((b i) x : ℝ) * ((b j) x : ℝ)

@[simp] lemma coordMat_apply (b : Module.Basis ι ℤ (ι → ℤ)) (x j : ι) :
    coordMat b x j = (b j) x := rfl

@[simp] lemma dualVec_apply (b : Module.Basis ι ℤ (ι → ℤ)) (i x : ι) :
    dualVec b i x = b.coord i (Pi.basisFun ℤ ι x) := rfl

@[simp] lemma dualMat_apply (b : Module.Basis ι ℤ (ι → ℤ)) (i x : ι) :
    dualMat b i x = dualVec b i x := rfl

@[simp] lemma gramR_apply (b : Module.Basis ι ℤ (ι → ℤ)) (i j : ι) :
    gramR b i j = ∑ x, ((b i) x : ℝ) * ((b j) x : ℝ) := rfl


/-- The realisation of `coordMat b` over `ℝ`. -/
def coordMatR (b : Module.Basis ι ℤ (ι → ℤ)) : Matrix ι ι ℝ :=
  (coordMat b).map fun x => (x : ℝ)

/-- The realisation of `dualMat b` over `ℝ`. -/
def dualMatR (b : Module.Basis ι ℤ (ι → ℤ)) : Matrix ι ι ℝ :=
  (dualMat b).map fun x => (x : ℝ)

@[simp] lemma coordMatR_apply (b : Module.Basis ι ℤ (ι → ℤ)) (x j : ι) :
    coordMatR b x j = ((b j) x : ℝ) := by
  simp [coordMatR, coordMat]

@[simp] lemma dualMatR_apply (b : Module.Basis ι ℤ (ι → ℤ)) (i x : ι) :
    dualMatR b i x = ((dualVec b i) x : ℝ) := by
  simp [dualMatR, dualMat]

lemma map_mul_intCastR (M N : Matrix ι ι ℤ) :
    (M * N).map (fun x => (x : ℝ)) =
      (M.map fun x => (x : ℝ)) * (N.map fun x => (x : ℝ)) := by
  simpa using Matrix.map_mul (f := Int.castRingHom ℝ) (L := M) (M := N)

lemma map_one_intCastR : (1 : Matrix ι ι ℤ).map (fun x => (x : ℝ)) = 1 := by
  ext i j
  simp [Matrix.map_apply, Matrix.one_apply]

/-! ## The dual basis -/

/-- The `i`-th dual vector pairs to the Kronecker delta with the `j`-th basis vector. -/
theorem dualVec_pairing (b : Module.Basis ι ℤ (ι → ℤ)) (i j : ι) :
    ∑ x, dualVec b i x * (b j) x = if i = j then 1 else 0 := by
  have hsum : (∑ x, (b j) x • (Pi.basisFun ℤ ι x)) = b j := by
    have h := (Pi.basisFun ℤ ι).sum_repr (b j)
    simpa [Pi.basisFun_repr] using h
  have hcoord : b.coord i (b j) = ∑ x, dualVec b i x * (b j) x := by
    conv_lhs => rw [← hsum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun x _ => by
      rw [map_smul, dualVec, smul_eq_mul]
      exact mul_comm _ _
  rw [← hcoord, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- `dualMat b` is a left inverse of `coordMat b`. -/
theorem dualMat_mul_coordMat (b : Module.Basis ι ℤ (ι → ℤ)) : dualMat b * coordMat b = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [dualMat_apply, coordMat_apply]
  exact dualVec_pairing b i j

/-- `dualMat b` is a right inverse of `coordMat b`. -/
theorem coordMat_mul_dualMat (b : Module.Basis ι ℤ (ι → ℤ)) : coordMat b * dualMat b = 1 := by
  ext x j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have h2 : ((Pi.basisFun ℤ ι j) x : ℤ) = ∑ i, (b i) x * dualMat b i j := by
    conv_lhs => rw [← b.sum_repr (Pi.basisFun ℤ ι j)]
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Pi.smul_apply, smul_eq_mul, dualMat_apply, dualVec, Module.Basis.coord_apply]
      ring
  simp only [coordMat_apply]
  rw [← h2, Pi.basisFun_apply, Pi.single_apply]

/-- The dual basis is `ℤ`-linearly independent. -/
theorem dualVec_linearIndependent (b : Module.Basis ι ℤ (ι → ℤ)) :
    LinearIndependent ℤ (dualVec b) := by
  have hcomp : ((coordMat b)ᵀ).mulVecLin ∘ (dualVec b) = (Pi.basisFun ℤ ι) := by
    funext i
    ext j
    simp only [Function.comp_apply, Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_apply_eq_sum]
    simp only [Matrix.transpose_apply, coordMat_apply]
    rw [Finset.sum_congr rfl (fun x _ => mul_comm ((b j) x) (dualVec b i x)), dualVec_pairing,
      Pi.basisFun_apply, Pi.single_apply]
    by_cases h : j = i
    · simp [h]
    · simp [h, Ne.symm h]
  refine LinearIndependent.of_comp ((coordMat b)ᵀ).mulVecLin ?_
  rw [hcomp]
  exact (Pi.basisFun ℤ ι).linearIndependent

/-- Expansion of a vector in the dual basis: `y = ∑ᵢ ⟨y, bᵢ⟩ • dualVec b i`. -/
theorem sum_dualVec_smul (b : Module.Basis ι ℤ (ι → ℤ)) (y : ι → ℤ) :
    ∑ i, (∑ x, y x * (b i) x) • dualVec b i = y := by
  funext k
  have key : ∀ i, (∑ x, y x * (b i) x) * dualVec b i k
      = ∑ x, y x * (coordMat b x i * dualMat b i k) := by
    intro i
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [coordMat_apply, dualMat_apply]
    ring
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_comm]
  have key2 : ∀ x, (∑ i, y x * (coordMat b x i * dualMat b i k))
      = y x * (if x = k then 1 else 0) := by
    intro x
    rw [← Finset.mul_sum]
    congr 1
    rw [← Matrix.mul_apply, coordMat_mul_dualMat b, Matrix.one_apply]
  rw [Finset.sum_congr rfl (fun x _ => key2 x), Finset.sum_eq_single k]
  · simp
  · intro x _ hxk
    simp [hxk]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-! ## The Gram matrix -/

/-- `gramR b` is the product of the coordinate matrix with its transpose. -/
theorem gramR_eq_mul (b : Module.Basis ι ℤ (ι → ℤ)) :
    gramR b = (coordMatR b)ᵀ * coordMatR b := by
  ext i j
  simp [gramR, coordMatR, Matrix.mul_apply]

/-- The Gram determinant of a `ℤ`-basis of `ℤ^ι` is `1`. -/
theorem gramR_det (b : Module.Basis ι ℤ (ι → ℤ)) : (gramR b).det = 1 := by
  have h1 : (coordMat b * dualMat b) = 1 := coordMat_mul_dualMat b
  have hdet : (coordMat b).det * (dualMat b).det = 1 := by
    rw [← Matrix.det_mul, h1, Matrix.det_one]
  have hcast : (coordMatR b).det = ((coordMat b).det : ℝ) := by
    rw [show coordMatR b = (coordMat b).map (fun x => (x : ℝ)) from rfl]
    exact (Int.cast_det (coordMat b)).symm
  rw [gramR_eq_mul, Matrix.det_mul, Matrix.det_transpose, hcast]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h <;> rw [h] <;> norm_num

/-- The inverse of the Gram matrix is the Gram matrix of the dual basis. -/
theorem gramR_inv (b : Module.Basis ι ℤ (ι → ℤ)) :
    (gramR b)⁻¹ = dualMatR b * (dualMatR b)ᵀ := by
  have hTD : coordMatR b * dualMatR b = 1 := by
    simp only [coordMatR, dualMatR]
    rw [← map_mul_intCastR, coordMat_mul_dualMat b, map_one_intCastR]
  have hDT : dualMatR b * coordMatR b = 1 := by
    simp only [coordMatR, dualMatR]
    rw [← map_mul_intCastR, dualMat_mul_coordMat b, map_one_intCastR]
  have hM : gramR b * (dualMatR b * (dualMatR b)ᵀ) = 1 := by
    rw [gramR_eq_mul]
    calc (coordMatR b)ᵀ * coordMatR b * (dualMatR b * (dualMatR b)ᵀ)
        = (coordMatR b)ᵀ * (coordMatR b * dualMatR b) * (dualMatR b)ᵀ := by noncomm_ring
      _ = 1 := by
          rw [hTD, mul_one, ← Matrix.transpose_mul, hDT, Matrix.transpose_one]
  exact Matrix.inv_eq_right_inv hM

/-- Entries of the inverse Gram matrix are inner products of dual basis vectors. -/
theorem gramR_inv_apply (b : Module.Basis ι ℤ (ι → ℤ)) (i j : ι) :
    (gramR b)⁻¹ i j = ∑ x, ((dualVec b i) x : ℝ) * ((dualVec b j) x : ℝ) := by
  rw [gramR_inv, Matrix.mul_apply]
  simp [Matrix.transpose_apply]

/-- The Gram matrix of a `ℤ`-basis of `ℤ^ι` is positive definite. -/
theorem gramR_posDef (b : Module.Basis ι ℤ (ι → ℤ)) : (gramR b).PosDef := by
  have h1 : (coordMat b * dualMat b) = 1 := coordMat_mul_dualMat b
  have hdet : (coordMat b).det = 1 ∨ (coordMat b).det = -1 :=
    Int.eq_one_or_neg_one_of_mul_eq_one (by rw [← Matrix.det_mul, h1, Matrix.det_one])
  have hcast : (coordMatR b).det = ((coordMat b).det : ℝ) := by
    rw [show coordMatR b = (coordMat b).map (fun x => (x : ℝ)) from rfl]
    exact (Int.cast_det (coordMat b)).symm
  have hne : (coordMatR b).det ≠ 0 := by
    rw [hcast]
    rcases hdet with h | h <;> rw [h] <;> norm_num
  have hinj : Function.Injective (coordMatR b).mulVec := by
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hne
  have h := Matrix.PosDef.conjTranspose_mul_self (coordMatR b) hinj
  have hconj : (coordMatR b)ᴴ = (coordMatR b)ᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rwa [hconj, ← gramR_eq_mul] at h

/-- Every principal block of the Gram matrix of a `ℤ`-basis of `ℤ^ι` is invertible. -/
theorem gramR_block_det_ne_zero (b : Module.Basis ι ℤ (ι → ℤ)) (p : ι → Prop) [DecidablePred p] :
    ((gramR b).toSquareBlockProp p).det ≠ 0 := by
  have hsub : ((gramR b).submatrix (fun i : {i // p i} => (i : ι))
      (fun i : {i // p i} => (i : ι))).PosDef :=
    (gramR_posDef b).submatrix fun _ _ h => Subtype.ext h
  have hEq : (gramR b).submatrix (fun i : {i // p i} => (i : ι))
      (fun i : {i // p i} => (i : ι)) = (gramR b).toSquareBlockProp p := by
    ext i j
    simp [Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.submatrix_apply]
  rw [hEq] at hsub
  exact ne_of_gt hsub.det_pos

end Work.HP.DetLOrth
