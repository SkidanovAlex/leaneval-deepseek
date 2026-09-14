import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open scoped Matrix

namespace Commons.LinearAlgebra.Matrix

/-- Cramer's rule for row replacement: replacing row `i` of an invertible square matrix `M`
by the row-vector `w` changes the determinant by `det M` times the `i`-th entry of `w ᵥ* M⁻¹`. -/
lemma det_updateRow_eq_det_mul_vecMul_inv {K : Type*} [Field K] {r : ℕ}
    (M : Matrix (Fin r) (Fin r) K) (hM : IsUnit M.det) (i : Fin r) (w : Fin r → K) :
    (M.updateRow i w).det = M.det * (w ᵥ* M⁻¹) i := by
  rw [← Matrix.cramer_transpose_apply]
  rw [← Matrix.det_smul_inv_vecMul_eq_cramer_transpose M w hM]
  simp

/-- Updating an injective function at one coordinate keeps it injective, provided the new value
is outside its range. -/
lemma inj_update_embedding {r n : ℕ} (e₀ : Fin r ↪ Fin n) (t : Fin n) (i : Fin r)
    (ht : t ∉ Set.range e₀) : Function.Injective (Function.update e₀ i t) := by
  intro a b hab
  by_cases ha : a = i
  · subst a
    by_cases hb : b = i
    · exact hb.symm
    · exfalso
      apply ht
      refine ⟨b, ?_⟩
      simpa [Function.update, hb] using hab.symm
  · by_cases hb : b = i
    · subst b
      exfalso
      apply ht
      refine ⟨a, ?_⟩
      simpa [Function.update, ha] using hab
    · have : e₀ a = e₀ b := by
        simpa [Function.update, ha, hb] using hab
      exact e₀.injective this

/-- A single-row change of the rows selected by `e₀` is again a submatrix (by an embedding). -/
lemma submatrix_updateRow_eq {K : Type*} [Field K] {r n : ℕ} (X : Matrix (Fin n) (Fin r) K)
    (e₀ : Fin r ↪ Fin n) (t : Fin n) (i : Fin r) :
    X.submatrix (Function.update e₀ i t) (fun j : Fin r => j) =
      (X.submatrix e₀ (fun j : Fin r => j)).updateRow i (X t) := by
  ext a b
  by_cases ha : a = i
  · subst a
    simp [Function.update]
  · simp [Function.update, ha]

theorem span_eq_of_minors_eq {n r : ℕ} (A B : Matrix (Fin n) (Fin r) ℚ)
    (hrankA : ∃ e : Fin r ↪ Fin n, (A.submatrix e (fun j : Fin r => j)).det ≠ 0)
    (hmin : ∀ e : Fin r ↪ Fin n,
      (A.submatrix e (fun j : Fin r => j)).det = (B.submatrix e (fun j : Fin r => j)).det) :
    Submodule.span ℚ (Set.range A.col) = Submodule.span ℚ (Set.range B.col) := by
  rcases hrankA with ⟨e₀, hMdet0⟩
  let M : Matrix (Fin r) (Fin r) ℚ := A.submatrix e₀ (fun j : Fin r => j)
  let N : Matrix (Fin r) (Fin r) ℚ := B.submatrix e₀ (fun j : Fin r => j)
  have hNdet0 : N.det ≠ 0 := by
    change (B.submatrix e₀ (fun j : Fin r => j)).det ≠ 0
    rw [← hmin e₀]
    exact hMdet0
  have hMunit : IsUnit M.det := IsUnit.mk0 M.det hMdet0
  have hNunit : IsUnit N.det := IsUnit.mk0 N.det hNdet0
  have hMdet_eq_Ndet : M.det = N.det := by
    change (A.submatrix e₀ (fun j : Fin r => j)).det = (B.submatrix e₀ (fun j : Fin r => j)).det
    exact hmin e₀
  have htop : M * (M⁻¹ * N) = N := by
    calc M * (M⁻¹ * N) = (M * M⁻¹) * N := by rw [mul_assoc]
      _ = 1 * N := by simp [Matrix.mul_nonsing_inv M hMunit]
      _ = N := by simp
  -- For every row `t` outside the image of `e₀`, the `t`-rows of `B` and `A * (M⁻¹ * N)` agree.
  have hrow_out : ∀ t : Fin n, t ∉ Set.range e₀ → (A * (M⁻¹ * N)) t = B t := by
    intro t ht
    have hvec : A t ᵥ* M⁻¹ = B t ᵥ* N⁻¹ := by
      funext i
      let φ : Fin r ↪ Fin n := ⟨Function.update e₀ i t, inj_update_embedding e₀ t i ht⟩
      have hφA : (A.submatrix φ (fun j : Fin r => j)).det = (M.updateRow i (A t)).det := by
        simpa [φ, M] using congrArg Matrix.det (submatrix_updateRow_eq A e₀ t i)
      have hφB : (B.submatrix φ (fun j : Fin r => j)).det = (N.updateRow i (B t)).det := by
        simpa [φ, N] using congrArg Matrix.det (submatrix_updateRow_eq B e₀ t i)
      have hdets : (M.updateRow i (A t)).det = (N.updateRow i (B t)).det := by
        calc
          (M.updateRow i (A t)).det = (A.submatrix φ (fun j : Fin r => j)).det := hφA.symm
          _ = (B.submatrix φ (fun j : Fin r => j)).det := hmin φ
          _ = (N.updateRow i (B t)).det := hφB
      have h1 := det_updateRow_eq_det_mul_vecMul_inv M hMunit i (A t)
      have h2 := det_updateRow_eq_det_mul_vecMul_inv N hNunit i (B t)
      have hmul : M.det * (A t ᵥ* M⁻¹) i = M.det * (B t ᵥ* N⁻¹) i := by
        rw [← h1]
        rw [hMdet_eq_Ndet]
        rw [← h2]
        rw [hdets]
      exact mul_left_cancel₀ hMdet0 hmul
    calc
      (A * (M⁻¹ * N)) t = A t ᵥ* (M⁻¹ * N) := by rw [Matrix.mul_apply_eq_vecMul]
      _ = (A t ᵥ* M⁻¹) ᵥ* N := by rw [Matrix.vecMul_vecMul]
      _ = (B t ᵥ* N⁻¹) ᵥ* N := by rw [hvec]
      _ = B t ᵥ* (N⁻¹ * N) := by rw [Matrix.vecMul_vecMul]
      _ = B t ᵥ* 1 := by rw [Matrix.nonsing_inv_mul N hNunit]
      _ = B t := by simp
  have hB_eq : B = A * (M⁻¹ * N) := by
    ext t j
    by_cases ht : t ∈ Set.range e₀
    · rcases ht with ⟨i, rfl⟩
      have hrow : (A * (M⁻¹ * N)) (e₀ i) = B (e₀ i) := by
        calc
          (A * (M⁻¹ * N)) (e₀ i) = A (e₀ i) ᵥ* (M⁻¹ * N) := by rw [Matrix.mul_apply_eq_vecMul]
          _ = M i ᵥ* (M⁻¹ * N) := by rfl
          _ = (M * (M⁻¹ * N)) i := by rw [Matrix.mul_apply_eq_vecMul]
          _ = N i := by rw [htop]
          _ = B (e₀ i) := by rfl
      exact (congrFun hrow j).symm
    · exact (congrFun (hrow_out t ht) j).symm
  have hCC : (M⁻¹ * N) * (N⁻¹ * M) = 1 := by
    calc
      (M⁻¹ * N) * (N⁻¹ * M) = M⁻¹ * (N * (N⁻¹ * M)) := by rw [mul_assoc]
      _ = M⁻¹ * ((N * N⁻¹) * M) := by
        congr 1
        rw [← mul_assoc]
      _ = M⁻¹ * (1 * M) := by rw [Matrix.mul_nonsing_inv N hNunit]
      _ = M⁻¹ * M := by rw [one_mul]
      _ = 1 := by rw [Matrix.nonsing_inv_mul M hMunit]
  have hA_eq : A = B * (N⁻¹ * M) := by
    calc
      A = A * ((M⁻¹ * N) * (N⁻¹ * M)) := by
        rw [hCC, Matrix.mul_one]
      _ = (A * (M⁻¹ * N)) * (N⁻¹ * M) := by
        exact (Matrix.mul_assoc A (M⁻¹ * N) (N⁻¹ * M)).symm
      _ = B * (N⁻¹ * M) := by
        rw [← hB_eq]
  have hB_le_A : LinearMap.range A.mulVecLin ≤ LinearMap.range B.mulVecLin := by
    rw [hA_eq, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range (N⁻¹ * M).mulVecLin B.mulVecLin
  have hA_le_B : LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin := by
    rw [hB_eq, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range (M⁻¹ * N).mulVecLin A.mulVecLin
  rw [← Matrix.range_mulVecLin A, ← Matrix.range_mulVecLin B]
  exact le_antisymm hB_le_A hA_le_B

end Commons.LinearAlgebra.Matrix