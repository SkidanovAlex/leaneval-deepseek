/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A Sylvester rank function on a division ring

Every division ring `D` carries a Sylvester matrix rank function: the rank of a matrix over
`D`, well defined because `D` is a division ring, i.e. the dimension of the range of the
associated (row-vector) linear map `D^n → D^m`.

We build this rank function from scratch.  The underlying numerical invariant is `mrank`,
the `D`-dimension of the range of `A.vecMulLinear : (m → D) →ₗ[D] (n → D)`, and we verify
the four Sylvester axioms `(SMat1)`–`(SMat4)` for it.  The two block axioms are reduced,
via the linear equivalences `(m₁ ⊕ m₂ → D) ≃ₗ (m₁ → D) × (m₂ → D)`, to statements about
block matrices `Matrix.fromBlocks`.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.DivisionRank.finrank_prod_submodule
import Submission.Work.ORHughesFree.DivisionRank.finrank_range_prod_le

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.DivisionRank

open Matrix

/-- The rank of a matrix over a division ring `D`: the dimension of the range of the
row-vector action `x ↦ x ᵥ* A`, viewed as a linear map `(m → D) →ₗ[D] (n → D)`. -/
noncomputable def mrank {D : Type u} [DivisionRing D] {m n : Type*} [Fintype m]
    (A : Matrix m n D) : ℕ :=
  Module.finrank D (LinearMap.range A.vecMulLinear)

/-- Left multiplication of row vectors commutes with matrix multiplication: the linear map
attached to `A * B` is the composite of the linear maps attached to `A` and `B`. -/
theorem vecMulLinear_mul {D : Type u} [Semiring D] {l m n : Type*} [Fintype l] [Fintype m]
    (A : Matrix l m D) (B : Matrix m n D) :
    (A * B).vecMulLinear = B.vecMulLinear.comp A.vecMulLinear := by
  ext x
  simp [Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul]

/-- (SMat2), left half: `mrank (A * B) ≤ mrank A`. -/
theorem mrank_mul_le_left {D : Type u} [DivisionRing D] {l m n : Type*}
    [Fintype l] [Fintype m] [Fintype n] (A : Matrix l m D) (B : Matrix m n D) :
    mrank (A * B) ≤ mrank A := by
  rw [mrank, mrank, vecMulLinear_mul, LinearMap.range_comp]
  exact Submodule.finrank_map_le _ _

/-- (SMat2), right half: `mrank (A * B) ≤ mrank B`. -/
theorem mrank_mul_le_right {D : Type u} [DivisionRing D] {l m n : Type*}
    [Fintype l] [Fintype m] [Fintype n] (A : Matrix l m D) (B : Matrix m n D) :
    mrank (A * B) ≤ mrank B := by
  rw [mrank, mrank, vecMulLinear_mul]
  exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

/-- (SMat1): the rank of the zero matrix is zero. -/
@[simp]
theorem mrank_zero {D : Type u} [DivisionRing D] {m n : Type*} [Fintype m] :
    mrank (0 : Matrix m n D) = 0 := by
  rw [mrank, show (0 : Matrix m n D).vecMulLinear = 0 by
    ext x; simp [Matrix.vecMulLinear_apply], LinearMap.range_zero, finrank_bot]

/-- (SMat1): the rank of the `1 × 1` identity matrix is one. -/
theorem mrank_one_one {D : Type u} [DivisionRing D] :
    mrank (1 : Matrix (Fin 1) (Fin 1) D) = 1 := by
  rw [mrank, show (1 : Matrix (Fin 1) (Fin 1) D).vecMulLinear = LinearMap.id by
    ext x; simp [Matrix.vecMulLinear_apply], LinearMap.range_id, finrank_top,
    Module.finrank_fin_fun]

/-- Rank is invariant under left multiplication by a matrix with a left inverse. -/
theorem mrank_eq_of_left_inverse_mul {D : Type u} [DivisionRing D] {l m n : Type*}
    [Fintype l] [Fintype m] [Fintype n] [DecidableEq l] (X : Matrix m l D) (X' : Matrix l m D)
    (hX : X' * X = 1) (A : Matrix l n D) : mrank (X * A) = mrank A := by
  refine le_antisymm (mrank_mul_le_right X A) ?_
  have h : X' * (X * A) = A := by rw [← Matrix.mul_assoc, hX, Matrix.one_mul]
  calc mrank A = mrank (X' * (X * A)) := by rw [h]
    _ ≤ mrank (X * A) := mrank_mul_le_right X' (X * A)

/-- Rank is invariant under right multiplication by a matrix with a right inverse. -/
theorem mrank_eq_of_mul_right_inverse {D : Type u} [DivisionRing D] {l m n : Type*}
    [Fintype l] [Fintype m] [Fintype n] [DecidableEq m] (A : Matrix l m D) (Y : Matrix m n D)
    (Y' : Matrix n m D) (hY : Y * Y' = 1) : mrank (A * Y) = mrank A := by
  refine le_antisymm (mrank_mul_le_left A Y) ?_
  have h : A * Y * Y' = A := by rw [Matrix.mul_assoc, hY, Matrix.mul_one]
  calc mrank A = mrank (A * Y * Y') := by rw [h]
    _ ≤ mrank (A * Y) := mrank_mul_le_left (A * Y) Y'

/-! ### Reindexing

Reindexing a matrix by equivalences does not change its rank. -/

/-- The product of one-sided-inverse permutation-type matrices is the identity. -/
theorem submatrix_one_mul_submatrix_symm_one {D : Type u} [Ring D] {l m : Type*}
    [Fintype l] [Fintype m] [DecidableEq l] [DecidableEq m]
    (e : l ≃ m) :
    ((1 : Matrix m m D).submatrix e id) * ((1 : Matrix l l D).submatrix e.symm id) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply, id_eq]
  rw [Finset.sum_eq_single (e i)]
  · simp [Equiv.apply_symm_apply]
  · intro k _ hk
    rw [if_neg (Ne.symm hk), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The other product of one-sided-inverse permutation-type matrices is the identity. -/
theorem submatrix_symm_one_mul_submatrix_one {D : Type u} [Ring D] {l m : Type*}
    [Fintype l] [Fintype m] [DecidableEq l]
    (e : l ≃ m) :
    ((1 : Matrix l l D).submatrix id e.symm) * ((1 : Matrix l l D).submatrix e.symm id) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply, id_eq]
  rw [Finset.sum_eq_single (e i)]
  · simp [Equiv.apply_symm_apply]
  · intro k _ hk
    have hik : i ≠ e.symm k := fun h => hk (by rw [h, Equiv.apply_symm_apply])
    rw [if_neg hik, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Reindexing a matrix is a product with permutation-type matrices. -/
theorem reindex_eq_mul {D : Type u} [Ring D] {l l' n n' : Type*}
    [Fintype l] [Fintype n] [DecidableEq l] [DecidableEq n]
    (e : l ≃ l') (f : n ≃ n') (A : Matrix l n D) :
    Matrix.reindex e f A
      = ((1 : Matrix l l D).submatrix e.symm id) * A * ((1 : Matrix n n D).submatrix id f.symm) := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply]

/-- Reindexing a matrix by equivalences does not change its rank. -/
theorem mrank_reindex {D : Type u} [DivisionRing D] {l l' n n' : Type*}
    [Fintype l] [Fintype l'] [Fintype n] [Fintype n']
    [DecidableEq l] [DecidableEq l'] [DecidableEq n] [DecidableEq n']
    (e : l ≃ l') (f : n ≃ n')
    (A : Matrix l n D) : mrank (Matrix.reindex e f A) = mrank A := by
  set P : Matrix l' l D := (1 : Matrix l l D).submatrix e.symm id with hP
  set P' : Matrix l l' D := (1 : Matrix l' l' D).submatrix e id with hP'
  set Q : Matrix n n' D := (1 : Matrix n n D).submatrix id f.symm with hQ
  set Q' : Matrix n' n D := (1 : Matrix n n D).submatrix f.symm id with hQ'
  have hA : Matrix.reindex e f A = P * A * Q := by
    rw [hP, hQ]; exact reindex_eq_mul e f A
  have hPP' : P' * P = 1 := by rw [hP', hP]; exact submatrix_one_mul_submatrix_symm_one e
  have hQQ' : Q * Q' = 1 := by rw [hQ, hQ']; exact submatrix_symm_one_mul_submatrix_one f
  have h2 : mrank (P * A * Q) = mrank (P * A) :=
    mrank_eq_of_mul_right_inverse (P * A) Q Q' hQQ'
  have h3 : mrank (P * A) = mrank A := mrank_eq_of_left_inverse_mul P P' hPP' A
  rw [hA, h2, h3]

/-! ### The block axioms

We reduce `(SMat3)` and `(SMat4)` to statements about `Matrix.fromBlocks`, using the linear
equivalence `(α ⊕ β → D) ≃ₗ[D] (α → D) × (β → D)`. -/

/-- The range of a product of linear maps is the product of the ranges. -/
theorem range_prodMap {D : Type u} [DivisionRing D] {M M₂ M₃ M₄ : Type*}
    [AddCommGroup M] [Module D M] [AddCommGroup M₂] [Module D M₂]
    [AddCommGroup M₃] [Module D M₃] [AddCommGroup M₄] [Module D M₄]
    (f : M →ₗ[D] M₃) (g : M₂ →ₗ[D] M₄) :
    LinearMap.range (LinearMap.prodMap f g) = (LinearMap.range f).prod (LinearMap.range g) := by
  rw [LinearMap.range_eq_map, ← Submodule.prod_top, LinearMap.prodMap_map_prod,
    Submodule.map_top, Submodule.map_top]

/-- The `vecMulLinear` map of a block-diagonal matrix, expressed through the product
decomposition `(α ⊕ β → D) ≃ₗ (α → D) × (β → D)`. -/
theorem vecMulLinear_fromBlocks_diag {D : Type u} [DivisionRing D] {m₁ m₂ n₁ n₂ : Type*}
    [Fintype m₁] [Fintype m₂] [Fintype n₁] [Fintype n₂]
    (A : Matrix m₁ n₁ D) (B : Matrix m₂ n₂ D) :
    (Matrix.fromBlocks A 0 0 B).vecMulLinear
      = (LinearEquiv.sumArrowLequivProdArrow n₁ n₂ D D).symm.toLinearMap.comp
        ((LinearMap.prodMap A.vecMulLinear B.vecMulLinear).comp
          (LinearEquiv.sumArrowLequivProdArrow m₁ m₂ D D).toLinearMap) := by
  apply LinearMap.ext
  intro x
  apply (LinearEquiv.sumArrowLequivProdArrow n₁ n₂ D D).injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  have hx1 : ((LinearEquiv.sumArrowLequivProdArrow m₁ m₂ D D) x).1 = x ∘ Sum.inl := by
    funext k; exact LinearEquiv.sumArrowLequivProdArrow_apply_fst x k
  have hx2 : ((LinearEquiv.sumArrowLequivProdArrow m₁ m₂ D D) x).2 = x ∘ Sum.inr := by
    funext k; exact LinearEquiv.sumArrowLequivProdArrow_apply_snd x k
  refine Prod.ext ?_ ?_
  · ext i
    rw [Matrix.vecMulLinear_apply, Matrix.vecMul_fromBlocks, LinearMap.prodMap_apply, hx1]
    simp
  · ext j
    rw [Matrix.vecMulLinear_apply, Matrix.vecMul_fromBlocks, LinearMap.prodMap_apply, hx2]
    simp

/-- (SMat3) for block matrices: the rank of a block-diagonal matrix is the sum of the ranks. -/
theorem mrank_fromBlocks_diag {D : Type u} [DivisionRing D] {m₁ m₂ n₁ n₂ : Type*}
    [Fintype m₁] [Fintype m₂] [Fintype n₁] [Fintype n₂]
    (A : Matrix m₁ n₁ D) (B : Matrix m₂ n₂ D) :
    mrank (Matrix.fromBlocks A 0 0 B) = mrank A + mrank B := by
  have h1 := vecMulLinear_fromBlocks_diag A B
  rw [mrank, h1, LinearMap.range_comp, LinearEquiv.finrank_map_eq, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top, range_prodMap, finrank_prod_submodule]
  simp [mrank]

/-- The `vecMulLinear` map of a block upper-triangular matrix, expressed through the product
decomposition `(α ⊕ β → D) ≃ₗ (α → D) × (β → D)`. -/
theorem vecMulLinear_fromBlocks_upper {D : Type u} [DivisionRing D] {m₁ m₂ n₁ n₂ : Type*}
    [Fintype m₁] [Fintype m₂] [Fintype n₁] [Fintype n₂]
    (A : Matrix m₁ n₁ D) (B : Matrix m₂ n₂ D) (C : Matrix m₁ n₂ D) :
    (Matrix.fromBlocks A C 0 B).vecMulLinear
      = (LinearEquiv.sumArrowLequivProdArrow n₁ n₂ D D).symm.toLinearMap.comp
        ((LinearMap.prod (A.vecMulLinear.comp (LinearMap.fst D (m₁ → D) (m₂ → D)))
          ((C.vecMulLinear.comp (LinearMap.fst D (m₁ → D) (m₂ → D)))
            + (B.vecMulLinear.comp (LinearMap.snd D (m₁ → D) (m₂ → D))))).comp
          (LinearEquiv.sumArrowLequivProdArrow m₁ m₂ D D).toLinearMap) := by
  apply LinearMap.ext
  intro x
  apply (LinearEquiv.sumArrowLequivProdArrow n₁ n₂ D D).injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  have hx1 : ((LinearEquiv.sumArrowLequivProdArrow m₁ m₂ D D) x).1 = x ∘ Sum.inl := by
    funext k; exact LinearEquiv.sumArrowLequivProdArrow_apply_fst x k
  have hx2 : ((LinearEquiv.sumArrowLequivProdArrow m₁ m₂ D D) x).2 = x ∘ Sum.inr := by
    funext k; exact LinearEquiv.sumArrowLequivProdArrow_apply_snd x k
  refine Prod.ext ?_ ?_
  · ext i
    simp only [LinearEquiv.sumArrowLequivProdArrow_apply_fst, Matrix.vecMulLinear_apply,
      Matrix.vecMul_fromBlocks, LinearMap.prod_apply, Function.prod_apply]
    simp [LinearMap.comp_apply, LinearMap.fst_apply, hx1]
  · ext j
    simp only [LinearEquiv.sumArrowLequivProdArrow_apply_snd, Matrix.vecMulLinear_apply,
      Matrix.vecMul_fromBlocks, LinearMap.prod_apply, Function.prod_apply]
    simp [LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, hx1, hx2]

/-- (SMat4) for block matrices: the sum of the ranks of the diagonal blocks of an upper
triangular block matrix is at most its rank. -/
theorem mrank_fromBlocks_upper {D : Type u} [DivisionRing D] {m₁ m₂ n₁ n₂ : Type*}
    [Fintype m₁] [Fintype m₂] [Fintype n₁] [Fintype n₂]
    (A : Matrix m₁ n₁ D) (B : Matrix m₂ n₂ D) (C : Matrix m₁ n₂ D) :
    mrank A + mrank B ≤ mrank (Matrix.fromBlocks A C 0 B) := by
  have h1 := vecMulLinear_fromBlocks_upper A B C
  rw [mrank, mrank, mrank, h1, LinearMap.range_comp, LinearEquiv.finrank_map_eq,
    LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  exact finrank_range_prod_le A.vecMulLinear B.vecMulLinear C.vecMulLinear

/-! ### The `Fin`-indexed block axioms -/

/-- `blockDiagFin` agrees with `Matrix.fromBlocks` up to reindexing. -/
theorem blockDiagFin_eq_reindex {D : Type u} [Zero D] {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) D) (B : Matrix (Fin p) (Fin q) D) :
    blockDiagFin A B
      = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B) := rfl

/-- `blockUpperFin` agrees with `Matrix.fromBlocks` up to reindexing. -/
theorem blockUpperFin_eq_reindex {D : Type u} [Zero D] {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) D) (B : Matrix (Fin p) (Fin q) D)
    (C : Matrix (Fin n) (Fin q) D) :
    blockUpperFin A B C
      = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A C 0 B) := rfl

/-- (SMat3) in the form required by the `SylvesterRank` structure. -/
theorem mrank_blockDiagFin {D : Type u} [DivisionRing D] {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) D) (B : Matrix (Fin p) (Fin q) D) :
    mrank (blockDiagFin A B) = mrank A + mrank B := by
  rw [blockDiagFin_eq_reindex, mrank_reindex, mrank_fromBlocks_diag]

/-- (SMat4) in the form required by the `SylvesterRank` structure. -/
theorem mrank_blockUpperFin {D : Type u} [DivisionRing D] {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) D) (B : Matrix (Fin p) (Fin q) D)
    (C : Matrix (Fin n) (Fin q) D) :
    mrank A + mrank B ≤ mrank (blockUpperFin A B C) := by
  rw [blockUpperFin_eq_reindex, mrank_reindex]
  exact mrank_fromBlocks_upper A B C

/-! ### The rank function -/

/-- The matrix rank function on a division ring, packaged as a Sylvester rank function. -/
noncomputable def sylvRankDivisionRing (D : Type u) [DivisionRing D] : SylvesterRank D where
  rk _ _ A := (mrank A : ℝ)
  rk_nonneg n m A := Nat.cast_nonneg _
  rk_zero n m := by rw [mrank_zero]; norm_num
  rk_one := by rw [mrank_one_one]; norm_num
  rk_mul_le_left := by intro n m k A B; exact_mod_cast mrank_mul_le_left A B
  rk_mul_le_right := by intro n m k A B; exact_mod_cast mrank_mul_le_right A B
  rk_blockDiag := by
    intro n m p q A B
    rw [mrank_blockDiagFin]
    push_cast
    ring
  rk_blockUpper := by
    intro n m p q A B C
    exact_mod_cast mrank_blockUpperFin A B C

theorem exists_sylvesterRank_divisionRing (D : Type*) [DivisionRing D] :
    Nonempty (SylvesterRank D) :=
  ⟨sylvRankDivisionRing D⟩

end Work.ORHughesFree.DivisionRank
