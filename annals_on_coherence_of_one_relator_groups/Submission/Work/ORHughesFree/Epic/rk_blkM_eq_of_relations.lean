import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.RankAPI.rk_mul_eq_of_maxRank
import Submission.Work.ORHughesFree.RankAPI.rk_one_fin
import Submission.Work.ORHughesFree.RankAPI.rk_reindex
import Submission.Work.ORHughesFree.Epic.rk_blkM_defs
import Submission.Work.ORHughesFree.Epic.cokerEquiv_of_relations
import Submission.Work.ORHughesFree.Epic.exists_unit_of_coker_iso

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.ORHughesFree.Epic

open Matrix

variable {R : Type*} [Ring R]

/-! ## The row map of a matrix

The following few lemmas are copied from `Epic/fpDim_eq_of_presentation.lean`, which cannot be
imported here since it imports *this* file.  They set up the linear map `v ↦ v ᵥ* M` attached
to a matrix, the matrix attached to a linear map, and the fact that the Sylvester rank of a
matrix depends only on its row space. -/

theorem rowMulLin_single {a b : ℕ} (M : Matrix (Fin a) (Fin b) R) (i : Fin a) :
    rowMulLin M (Pi.single i 1) = M i := by
  ext j
  show (∑ l, (Pi.single i (1 : R) : Fin a → R) l * M l j) = M i j
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [Pi.single_apply, if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem rowMulLin_mul {a b c : ℕ} (M : Matrix (Fin a) (Fin b) R) (N : Matrix (Fin b) (Fin c) R) :
    rowMulLin (M * N) = (rowMulLin N).comp (rowMulLin M) := by
  refine LinearMap.ext fun v => ?_
  refine funext fun j => ?_
  show (∑ i, v i * (∑ k, M i k * N k j)) = ∑ k, (∑ i, v i * M i k) * N k j
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc]

/-- The expansion of a vector in the standard basis. -/
theorem eq_sum_smul_single {a : ℕ} (v : Fin a → R) :
    v = ∑ i, v i • (Pi.single i (1 : R) : Fin a → R) := by
  ext j
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [Pi.single_apply, if_neg (Ne.symm hb), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- The matrix of a linear map `(Fin a → R) →ₗ (Fin b → R)`: its `i`-th row is the image of
the `i`-th standard basis vector. -/
noncomputable def matOf {a b : ℕ} (f : (Fin a → R) →ₗ[R] (Fin b → R)) :
    Matrix (Fin a) (Fin b) R :=
  fun i j => f (Pi.single i 1) j

theorem rowMulLin_matOf {a b : ℕ} (f : (Fin a → R) →ₗ[R] (Fin b → R)) :
    rowMulLin (matOf f) = f := by
  refine LinearMap.ext fun v => ?_
  refine funext fun j => ?_
  show (∑ i, v i * f (Pi.single i (1 : R)) j) = f v j
  conv_rhs => rw [eq_sum_smul_single v]
  rw [map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem matOf_rowMulLin {a b : ℕ} (M : Matrix (Fin a) (Fin b) R) :
    matOf (rowMulLin M) = M := by
  ext i j
  simp only [matOf]
  rw [rowMulLin_single]

theorem matOf_sub {a b : ℕ} (f g : (Fin a → R) →ₗ[R] (Fin b → R)) :
    matOf (f - g) = matOf f - matOf g := by
  ext i j
  simp [matOf, LinearMap.sub_apply, Matrix.sub_apply]

theorem matOf_id (b : ℕ) :
    matOf (LinearMap.id : (Fin b → R) →ₗ[R] (Fin b → R)) = 1 := by
  ext i j
  simp [matOf, Matrix.one_apply, Pi.single_apply, eq_comm]

/-- If the range of `f` is contained in the range of `rowMulLin M`, then `f` is given by right
multiplication by `M` composed with a matrix. -/
theorem exists_eq_mul_of_range_le {a b c : ℕ} (f : (Fin a → R) →ₗ[R] (Fin c → R))
    (M : Matrix (Fin b) (Fin c) R) (h : LinearMap.range f ≤ LinearMap.range (rowMulLin M)) :
    ∃ Z : Matrix (Fin a) (Fin b) R, matOf f = Z * M := by
  have hz : ∀ i : Fin a, ∃ z : Fin b → R, rowMulLin M z = f (Pi.single i 1) := fun i =>
    LinearMap.mem_range.mp (h (LinearMap.mem_range.mpr ⟨Pi.single i 1, rfl⟩))
  choose z hz' using hz
  refine ⟨fun i => z i, ?_⟩
  ext i j
  simp only [matOf]
  rw [← congrFun (hz' i) j]
  rfl

/-- The Sylvester rank of a matrix depends only on its row space. -/
theorem rk_eq_of_range_eq {a b c : ℕ} (rk : SylvesterRank R)
    (A : Matrix (Fin a) (Fin c) R) (B : Matrix (Fin b) (Fin c) R)
    (h : LinearMap.range (rowMulLin A) = LinearMap.range (rowMulLin B)) :
    rk.rk a c A = rk.rk b c B := by
  refine le_antisymm ?_ ?_
  · obtain ⟨Z, hZ⟩ := exists_eq_mul_of_range_le (rowMulLin A) B h.le
    have hA : A = Z * B := by rw [← hZ, matOf_rowMulLin]
    rw [hA]
    exact rk.rk_mul_le_right Z B
  · obtain ⟨Z, hZ⟩ := exists_eq_mul_of_range_le (rowMulLin B) A h.ge
    have hB : B = Z * A := by rw [← hZ, matOf_rowMulLin]
    rw [hB]
    exact rk.rk_mul_le_right Z A

/-! ## Block matrices: multiplication and shears

`RankAPI.blk A B C D` is the block matrix `[[A, B], [C, D]]` with block rows/columns
normalised to `Fin`; it coincides definitionally with `RankAPI.blkG`, for which the block
multiplication `blkG_mul` is already available. -/

theorem blk_mul {a b c d e f : ℕ}
    (A : Matrix (Fin a) (Fin b) R) (B : Matrix (Fin a) (Fin d) R)
    (C : Matrix (Fin c) (Fin b) R) (D : Matrix (Fin c) (Fin d) R)
    (A' : Matrix (Fin b) (Fin e) R) (B' : Matrix (Fin b) (Fin f) R)
    (C' : Matrix (Fin d) (Fin e) R) (D' : Matrix (Fin d) (Fin f) R) :
    Work.ORHughesFree.RankAPI.blk A B C D * Work.ORHughesFree.RankAPI.blk A' B' C' D' =
      Work.ORHughesFree.RankAPI.blk (A * A' + B * C') (A * B' + B * D')
        (C * A' + D * C') (C * B' + D * D') :=
  Work.ORHughesFree.RankAPI.blkG_mul A B C D A' B' C' D'

/-- The "shear" decomposition of the block matrix `[[A, 0], [P, 1]]`. -/
theorem blk_shear {m n n' : ℕ} (A : Matrix (Fin m) (Fin n) R) (P : Matrix (Fin n') (Fin n) R) :
    Work.ORHughesFree.RankAPI.blk A 0 P (1 : Matrix (Fin n') (Fin n') R) =
      Work.ORHughesFree.RankAPI.blk A 0 0 (1 : Matrix (Fin n') (Fin n') R) *
        Work.ORHughesFree.RankAPI.blk (1 : Matrix (Fin n) (Fin n) R) 0 P
          (1 : Matrix (Fin n') (Fin n') R) := by
  rw [blk_mul]
  congr 1 <;> simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add]

/-- The shear matrix `[[1, 0], [P, 1]]` is invertible, with inverse `[[1, 0], [-P, 1]]`. -/
theorem blk_shear_mul_inv {n n' : ℕ} (P : Matrix (Fin n') (Fin n) R) :
    Work.ORHughesFree.RankAPI.blk (1 : Matrix (Fin n) (Fin n) R) 0 P
        (1 : Matrix (Fin n') (Fin n') R) *
      Work.ORHughesFree.RankAPI.blk (1 : Matrix (Fin n) (Fin n) R) 0 (-P)
        (1 : Matrix (Fin n') (Fin n') R) = 1 := by
  rw [blk_mul]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg,
    neg_zero, add_zero, zero_add, add_neg_cancel]
  exact Work.ORHughesFree.RankAPI.blkG_one (R := R) n n'

theorem rk_blockDiagFin_eq (rk : SylvesterRank R) {m n m' n' : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin m') (Fin n') R) :
    rk.rk (m + m') (n + n')
        (Work.ORHughesFree.RankAPI.blk A 0 0 B) = rk.rk m n A + rk.rk m' n' B :=
  rk.rk_blockDiag A B

/-- The Sylvester rank of the shear matrix `[[1, 0], [P, 1]]` is `n + n'`. -/
theorem rk_blk_shear (rk : SylvesterRank R) {n n' : ℕ} (P : Matrix (Fin n') (Fin n) R) :
    rk.rk (n + n') (n + n')
        (Work.ORHughesFree.RankAPI.blk (1 : Matrix (Fin n) (Fin n) R) 0 P
          (1 : Matrix (Fin n') (Fin n') R)) = ((n + n' : ℕ) : ℝ) := by
  refine le_antisymm (Work.ORHughesFree.RankAPI.rk_le_left rk _) ?_
  have h := rk.rk_mul_le_left
    (Work.ORHughesFree.RankAPI.blk (1 : Matrix (Fin n) (Fin n) R) 0 P
      (1 : Matrix (Fin n') (Fin n') R))
    (Work.ORHughesFree.RankAPI.blk (1 : Matrix (Fin n) (Fin n) R) 0 (-P)
      (1 : Matrix (Fin n') (Fin n') R))
  rw [blk_shear_mul_inv, Work.ORHughesFree.RankAPI.rk_one_fin rk (n + n')] at h
  exact_mod_cast h

/-- `rk [[A, 0], [P, 1]] = rk A + n'`. -/
theorem rk_blk_A_0_P_1 (rk : SylvesterRank R) {m n n' : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (P : Matrix (Fin n') (Fin n) R) :
    rk.rk (m + n') (n + n')
        (Work.ORHughesFree.RankAPI.blk A 0 P (1 : Matrix (Fin n') (Fin n') R))
      = rk.rk m n A + (n' : ℝ) := by
  rw [blk_shear, Work.ORHughesFree.RankAPI.rk_mul_eq_of_maxRank rk _ _
    (rk_blk_shear rk P), rk_blockDiagFin_eq, Work.ORHughesFree.RankAPI.rk_one_fin rk n']

/-- `blkB B` is a reindexing of the block diagonal matrix `[[B, 0], [0, 1_n]]`, hence
`rk (blkB B) = rk B + n`. -/
theorem rk_blkB (rk : SylvesterRank R) {m' n n' : ℕ} (B : Matrix (Fin m') (Fin n') R) :
    rk.rk (m' + n) (n + n') (blkB B) = rk.rk m' n' B + (n : ℝ) := by
  have hre : blkB B =
      Matrix.reindex (Equiv.refl (Fin (m' + n))) (Work.ORHughesFree.RankAPI.swapFin n n').symm
        (Work.ORHughesFree.RankAPI.blk B 0 0 (1 : Matrix (Fin n) (Fin n) R)) := by
    ext i j
    simp only [blkB, Work.ORHughesFree.RankAPI.blk, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.refl_symm, Equiv.coe_refl, id_eq, Equiv.symm_symm]
  rw [hre, Work.ORHughesFree.RankAPI.rk_reindex rk _ _ _,
    rk_blockDiagFin_eq rk B (1 : Matrix (Fin n) (Fin n) R),
    Work.ORHughesFree.RankAPI.rk_one_fin rk n]

/-- The main step: `rk [[A, 0], [P, 1]] = rk B + n`. -/
theorem rk_blk_A_0_P_1_eq (rk : SylvesterRank R) {m n m' n' : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin m') (Fin n') R)
    (P : Matrix (Fin n') (Fin n) R) (G : Matrix (Fin n) (Fin n') R)
    (h1 : ∃ W : Matrix (Fin m') (Fin m) R, B * P = W * A)
    (h2 : ∃ Z : Matrix (Fin n) (Fin m) R, G * P = 1 + Z * A)
    (h3 : ∃ X : Matrix (Fin m) (Fin m') R, A * G = X * B)
    (h4 : ∃ Z' : Matrix (Fin n') (Fin m') R, P * G = 1 + Z' * B) :
    rk.rk (m + n') (n + n')
        (Work.ORHughesFree.RankAPI.blk A 0 P (1 : Matrix (Fin n') (Fin n') R))
      = rk.rk m' n' B + (n : ℝ) := by
  obtain ⟨e⟩ := cokerEquiv_of_relations A B P G h1 h2 h3 h4
  obtain ⟨U, U', hUU', hU'U, hrange⟩ := exists_unit_of_coker_iso A B ⟨e⟩
  rw [blk_shear, Work.ORHughesFree.RankAPI.rk_mul_eq_of_maxRank rk _ _ (rk_blk_shear rk P)]
  calc rk.rk (m + n') (n + n')
        (Work.ORHughesFree.RankAPI.blk A 0 0 (1 : Matrix (Fin n') (Fin n') R))
      = rk.rk (m + n') (n + n')
        (Work.ORHughesFree.RankAPI.blk A 0 0 (1 : Matrix (Fin n') (Fin n') R) * U) :=
        (SylvesterRank.rk_eq_of_mul_right_inverse rk _ U U' hUU').symm
    _ = rk.rk (m' + n) (n + n') (blkB B) := rk_eq_of_range_eq rk _ _ hrange
    _ = rk.rk m' n' B + (n : ℝ) := rk_blkB rk B

theorem rk_blkM_eq_of_relations {R : Type*} [Ring R] (rk : Work.ORHughesFree.SylvesterRank R)
    {m n m' n' : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin m') (Fin n') R)
    (P : Matrix (Fin n') (Fin n) R) (G : Matrix (Fin n) (Fin n') R)
    (h1 : ∃ W : Matrix (Fin m') (Fin m) R, B * P = W * A)
    (h2 : ∃ Z : Matrix (Fin n) (Fin m) R, G * P = 1 + Z * A)
    (h3 : ∃ X : Matrix (Fin m) (Fin m') R, A * G = X * B)
    (h4 : ∃ Z' : Matrix (Fin n') (Fin m') R, P * G = 1 + Z' * B) :
    rk.rk (m + n') (n + n')
        ((Matrix.fromBlocks A 0 P (1 : Matrix (Fin n') (Fin n') R)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm)
      = rk.rk (m' + n) (n' + n)
        ((Matrix.fromBlocks B 0 G (1 : Matrix (Fin n) (Fin n) R)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm) := by
  change rk.rk (m + n') (n + n')
        (Work.ORHughesFree.RankAPI.blk A 0 P (1 : Matrix (Fin n') (Fin n') R))
      = rk.rk (m' + n) (n' + n)
        (Work.ORHughesFree.RankAPI.blk B 0 G (1 : Matrix (Fin n) (Fin n) R))
  rw [rk_blk_A_0_P_1_eq rk A B P G h1 h2 h3 h4, rk_blk_A_0_P_1 rk B G]

end Work.ORHughesFree.Epic

