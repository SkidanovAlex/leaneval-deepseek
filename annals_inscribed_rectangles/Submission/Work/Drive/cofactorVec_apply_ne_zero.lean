import Mathlib
import Submission.Work.Drive.BoxParityDefs

/-!
# The `i`-th cofactor is nonzero when `T` is surjective away from the `i`-th face

For `T : ℝ^{m+1} → ℝ^m` whose restriction to the coordinate hyperplane `{v | v i = 0}` is
surjective, the `i`-th component of the cofactor vector `cofactorVec T` is nonzero.

The `i`-th component of `cofactorVec T` is, up to sign, the determinant of the maximal minor of
`cofactorMatrix T` obtained by deleting the `i`-th row.  We package that minor as the determinant of
the square matrix `augN T i` whose first column is the `i`-th standard basis vector and whose
remaining columns are those of `cofactorMatrix T`; Laplace expansion along the first column shows
`(augN T i).det = cofactorVec T i`.

Now `augN T i` is the matrix of the linear map `v ↦ (v i, T v)`, so it is invertible exactly when
`ker T ∩ {v | v i = 0} = 0`.  That is precisely the injectivity of the restriction of `T` to the
hyperplane, which follows from the hypothesis by rank–nullity: the hyperplane has dimension `m`,
equal to the dimension of the target.
-/

namespace Work.Drive

noncomputable section

/-- The `i`-th coordinate functional `v ↦ v i` on `ℝ^{m+1}`. -/
private def evalAt {m : ℕ} (i : Fin (m + 1)) : Work.Drive.Amb m →ₗ[ℝ] ℝ where
  toFun v := v i
  map_add' u v := by simp
  map_smul' c v := by simp

/-- The square matrix whose first column is the `i`-th standard basis vector of `ℝ^{m+1}` and whose
remaining columns are the columns of `cofactorMatrix T`. -/
private def augN {m : ℕ} (T : Work.Drive.Amb m →L[ℝ] Work.Drive.Tgt m) (i : Fin (m + 1)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun k j => Fin.cases (if j = i then (1 : ℝ) else 0) (fun k' => Work.Drive.cofactorMatrix T j k') k

private lemma evalAt_ne_zero {m : ℕ} (i : Fin (m + 1)) : evalAt (m := m) i ≠ 0 := by
  intro h
  have hval : evalAt (m := m) i (EuclideanSpace.single i 1) = 1 := by
    show (EuclideanSpace.single i 1 : Work.Drive.Amb m) i = 1
    simp
  rw [h] at hval
  simp at hval

private lemma finrank_ker_evalAt {m : ℕ} (i : Fin (m + 1)) :
    Module.finrank ℝ (LinearMap.ker (evalAt (m := m) i)) =
      Module.finrank ℝ (Work.Drive.Tgt m) := by
  have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero (f := evalAt (m := m) i)
    (evalAt_ne_zero i)
  have h2 : Module.finrank ℝ (Work.Drive.Amb m) = m + 1 := finrank_euclideanSpace_fin
  have h3 : Module.finrank ℝ (Work.Drive.Tgt m) = m := finrank_euclideanSpace_fin
  omega

/-- Laplace expansion along the first column: the determinant of the augmented matrix is the
`i`-th cofactor. -/
private lemma augN_det {m : ℕ} (T : Work.Drive.Amb m →L[ℝ] Work.Drive.Tgt m) (i : Fin (m + 1)) :
    (augN T i).det = Work.Drive.cofactorVec T i := by
  have hsub : (augN T i).submatrix (Fin.succ (n := m)) i.succAbove =
      Matrix.transpose ((Work.Drive.cofactorMatrix T).submatrix i.succAbove id) := by
    ext a b
    simp [augN, Matrix.submatrix_apply, Matrix.transpose_apply]
  rw [Work.Drive.cofactorVec, WithLp.ofLp_toLp]
  rw [Matrix.det_succ_row_zero]
  rw [Finset.sum_eq_single i]
  · rw [hsub, Matrix.det_transpose]
    simp [augN]
  · intro b _ hb
    simp [augN, if_neg hb]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The `j`-th coordinate of `∑ j, v j • single j 1` is `v j`. -/
private lemma ofLp_sum_single {m : ℕ} (v : Fin (m + 1) → ℝ) :
    WithLp.ofLp (∑ j, v j • EuclideanSpace.single j 1 : Work.Drive.Amb m) = v := by
  funext l
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    PiLp.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb
    rw [if_neg (show ¬ (l = b) from fun h => hb h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ l) h

theorem cofactorVec_apply_ne_zero {m : ℕ} (T : Work.Drive.Amb m →L[ℝ] Work.Drive.Tgt m)
    (i : Fin (m+1))
    (hT : Function.Surjective (fun v : {v : Work.Drive.Amb m // v i = 0} => T v.1)) :
    Work.Drive.cofactorVec T i ≠ 0 := by
  -- `T` is injective on the hyperplane `{v | v i = 0}`.
  have hker : ∀ u : Work.Drive.Amb m, u i = 0 → T u = 0 → u = 0 := by
    intro u hu hTu
    have hsurj : Function.Surjective
        ((T : Work.Drive.Amb m →ₗ[ℝ] Work.Drive.Tgt m).domRestrict
          (LinearMap.ker (evalAt (m := m) i))) := by
      intro w
      obtain ⟨v, hv⟩ := hT w
      exact ⟨⟨v.1, v.2⟩, hv⟩
    have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_ker_evalAt i)).mpr hsurj
    have h0 : (⟨u, hu⟩ : LinearMap.ker (evalAt (m := m) i)) = 0 := by
      apply hinj
      simp [hTu]
    simpa using congrArg Subtype.val h0
  -- hence `augN T i` is nonsingular
  have hne : (augN T i).det ≠ 0 := by
    intro hzero
    obtain ⟨v, hvne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hzero
    have h0 : v i = 0 := by
      have h := congrFun hv (0 : Fin (m + 1))
      simpa [Matrix.mulVec, dotProduct, augN] using h
    have hk : ∀ k' : Fin m, ∑ j, v j * Work.Drive.cofactorMatrix T j k' = 0 := by
      intro k'
      have h := congrFun hv (Fin.succ k')
      have h2 : ∑ j, Work.Drive.cofactorMatrix T j k' * v j = 0 := by
        simpa [Matrix.mulVec, dotProduct, augN] using h
      rw [← h2]
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    set u : Work.Drive.Amb m := ∑ j, v j • EuclideanSpace.single j 1 with hu
    have h1u : WithLp.ofLp u = v := by rw [hu]; exact ofLp_sum_single v
    have hui : u i = 0 := by
      rw [show u i = (WithLp.ofLp u) i from rfl, h1u]; exact h0
    have hTu0 : T u = 0 := by
      rw [← WithLp.ofLp_eq_zero]
      funext k'
      have h1 : WithLp.ofLp (T u) k' = ∑ j, v j * Work.Drive.cofactorMatrix T j k' := by
        rw [hu]
        simp only [map_sum, map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl (fun x _ => by rw [Work.Drive.cofactorMatrix])
      rw [h1, hk k']
      simp
    have hun : u ≠ 0 := by
      intro h
      apply hvne
      have h1 : WithLp.ofLp u = v := h1u
      rw [h, WithLp.ofLp_zero] at h1
      exact h1.symm
    exact hun (hker u hui hTu0)
  intro h
  exact hne ((augN_det T i).trans h)

end

end Work.Drive
