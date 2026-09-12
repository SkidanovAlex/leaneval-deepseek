import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Submission.Commons.LinearAlgebra.Matrix.exists_det_ne_zero_of_rank_ge

namespace Commons.LinearAlgebra.Matrix

/-- For an embedding `f : Fin n ↪ Fin N` and a matrix `B : Matrix (Fin n) (Fin N) ℤ`,
multiplying `B` on the right by the `N × n` matrix consisting of the corresponding
standard basis vectors produces exactly the submatrix of `B` determined by `f`. -/
theorem mul_submatrix_one_eq_submatrix {n N : ℕ} (B : Matrix (Fin n) (Fin N) ℤ)
    (f : Fin n ↪ Fin N) :
    B * ((1 : Matrix (Fin N) (Fin N) ℤ).submatrix (id : Fin N → Fin N) f) =
      B.submatrix (id : Fin n → Fin n) f := by
  ext l j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply, id_eq]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

/-- **The image lattice of an integer matrix of full row rank has rank `n`.** If the rows of
`B : Matrix (Fin n) (Fin N) ℤ` are linearly independent over `ℚ`, then the range of the
associated `ℤ`-linear map `B.mulVecLin : (Fin N → ℤ) →ₗ[ℤ] (Fin n → ℤ)` is a free `ℤ`-module
of rank `n`. Two possible proof routes: (a) `ℚ`-row-independence gives a nonzero maximal
`n x n` minor (e.g. via
`Commons.LinearAlgebra.Matrix.exists_submatrix_det_ne_zero_of_cols_linearIndependent` applied
to `B.transpose`, after converting `ℚ`-independence to `ℤ`-independence of the integer
vectors), and Cramer's rule (`Matrix.mul_adjugate`) then shows `d • ℤ^n ⊆ range B.mulVecLin`
for a suitable nonzero integer `d`, so the range has rank `n`; or (b) use rank-nullity over
`ℤ`. -/
theorem finrank_range_mulVecLin_eq {n N : ℕ} (B : Matrix (Fin n) (Fin N) ℤ)
    (h : LinearIndependent ℚ (fun l : Fin n => fun k : Fin N => ((B l k : ℤ) : ℚ))) :
    Module.finrank ℤ (LinearMap.range B.mulVecLin) = n := by
  classical
  -- Work with the rational matrix.
  let A : Matrix (Fin n) (Fin N) ℚ := B.map (fun z : ℤ => (z : ℚ))
  have hArow : A.row = fun l : Fin n => fun k : Fin N => ((B l k : ℤ) : ℚ) := by
    ext l k; simp [A, Matrix.row_apply]
  have hli : LinearIndependent ℚ A.row := by rw [hArow]; exact h
  -- Its rank is `n`.
  have hrank : A.rank = n := by
    rw [Matrix.rank_eq_finrank_span_row]
    rw [finrank_span_eq_card hli]
    simp
  -- Hence the column space has dimension `n`, so there are `n` independent columns.
  have hcol : n ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range A.col)) := by
    rw [← Matrix.rank_eq_finrank_span_cols]
    exact hrank.ge
  obtain ⟨f, hf⟩ := exists_linearIndependent_comp_fin A.col hcol
  let C : Matrix (Fin n) (Fin n) ℤ := B.submatrix (id : Fin n → Fin n) f
  -- The corresponding integer `n × n` minor has nonzero determinant.
  have hCcol : LinearIndependent ℚ (A.submatrix (id : Fin n → Fin n) f).col := by
    have h1 : (A.submatrix (id : Fin n → Fin n) f).col = A.col ∘ f := by
      ext j i; simp [Matrix.col_apply]
    rw [h1]; exact hf
  have hdetQ : (A.submatrix (id : Fin n → Fin n) f).det ≠ 0 := by
    have hunit := (Matrix.linearIndependent_cols_iff_isUnit
      (A := A.submatrix (id : Fin n → Fin n) f)).mp hCcol
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
  have hmap : C.map (fun z : ℤ => (z : ℚ)) = A.submatrix (id : Fin n → Fin n) f := by
    simp [C, A, Matrix.submatrix_map]
  have hdetC : C.det ≠ 0 := by
    intro h0
    apply hdetQ
    have : (A.submatrix (id : Fin n → Fin n) f).det = 0 := by
      rw [← hmap, ← Int.cast_det C, h0]; simp
    exact this
  -- Cramer's rule: `det C` times any integer vector lies in the range of `C.mulVecLin`.
  have hCramer : ∀ y : Fin n → ℤ, C.det • y = C.mulVec (C.adjugate.mulVec y) := by
    intro y
    rw [Matrix.mulVec_mulVec y C C.adjugate, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  -- The range of `C.mulVecLin` sits inside the range of `B.mulVecLin`.
  have hMm : B * ((1 : Matrix (Fin N) (Fin N) ℤ).submatrix (id : Fin N → Fin N) f) = C :=
    mul_submatrix_one_eq_submatrix B f
  have hsuble : LinearMap.range C.mulVecLin ≤ LinearMap.range B.mulVecLin := by
    have heq : C.mulVecLin = B.mulVecLin.comp
        ((1 : Matrix (Fin N) (Fin N) ℤ).submatrix (id : Fin N → Fin N) f).mulVecLin := by
      rw [← hMm, Matrix.mulVecLin_mul]
    rw [heq]
    exact LinearMap.range_comp_le_range _ _
  set d : ℤ := C.det with hd
  -- Multiplication by `d` is injective on `ℤ^n`, so its range has rank `n`.
  have hinj : Function.Injective
      (d • (LinearMap.id : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ))) := by
    intro x y hxy
    funext i
    have hi : d * x i = d * y i := by
      have := congrFun hxy i
      simpa [LinearMap.smul_apply] using this
    exact mul_left_cancel₀ hdetC hi
  have hfinS : Module.finrank ℤ
      (LinearMap.range (d • (LinearMap.id : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ)))) = n := by
    rw [LinearMap.finrank_range_of_inj hinj]
    exact Module.finrank_fin_fun ℤ
  -- Its range is contained in `range B.mulVecLin`.
  have hSle : LinearMap.range (d • (LinearMap.id : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ)))
      ≤ LinearMap.range B.mulVecLin := by
    rintro x ⟨y, rfl⟩
    have hxy : d • y = C.mulVecLin (C.adjugate.mulVec y) := by
      rw [Matrix.mulVecLin_apply]; exact hCramer y
    rw [LinearMap.smul_apply, LinearMap.id_apply] at *
    rw [hxy]
    exact hsuble ⟨C.adjugate.mulVec y, rfl⟩
  have hle1 := Submodule.finrank_mono hSle
  have hle2 : Module.finrank ℤ ↥(LinearMap.range B.mulVecLin) ≤ n := by
    have h := Submodule.finrank_le (LinearMap.range B.mulVecLin : Submodule ℤ (Fin n → ℤ))
    rwa [Module.finrank_fin_fun ℤ] at h
  omega

end Commons.LinearAlgebra.Matrix