import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.gram_det_shear_orthogonal
import Submission.Commons.Analysis.InnerProductSpace.det_le_det_of_posSemidef_le

set_option linter.unnecessarySimpa false

open scoped BigOperators

namespace Commons.Analysis.InnerProductSpace

open Matrix exteriorPower

/-- `gram (Sum.elim u v)` is the reindexing of `gram (Fin.append u v)`, so the two
determinants agree. -/
private lemma det_gram_append_eq_det_gram_sum_elim {p q : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : Fin p → E) (v : Fin q → E) :
    (Matrix.gram ℝ (Fin.append u v)).det = (Matrix.gram ℝ (Sum.elim u v)).det := by
  classical
  let e : Fin p ⊕ Fin q ≃ Fin (p + q) := finSumFinEquiv
  have hse : (Matrix.gram ℝ (Sum.elim u v)) =
      (Matrix.gram ℝ (Fin.append u v)).submatrix e e := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [Matrix.gram_apply, e, finSumFinEquiv_apply_left, Fin.append_left]
      | inr j =>
        simp [Matrix.gram_apply, e, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          Fin.append_left, Fin.append_right]
    | inr i =>
      cases j with
      | inl j =>
        simp [Matrix.gram_apply, e, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          Fin.append_left, Fin.append_right]
      | inr j => simp [Matrix.gram_apply, e, finSumFinEquiv_apply_right, Fin.append_right]
  calc
    (Matrix.gram ℝ (Fin.append u v)).det
        = ((Matrix.gram ℝ (Fin.append u v)).submatrix e e).det := by
            rw [Matrix.det_submatrix_equiv_self]
    _ = (Matrix.gram ℝ (Sum.elim u v)).det := by rw [hse]

/-- The squared norm of an exterior product is the determinant of the Gram matrix. -/
private lemma normSq_ιMulti_eq_gram_det {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (w : Fin k → E) :
    ‖exteriorPower.ιMulti ℝ k w‖ ^ 2 = (Matrix.gram ℝ w).det := by
  calc
    ‖exteriorPower.ιMulti ℝ k w‖ ^ 2 =
        inner ℝ (exteriorPower.ιMulti ℝ k w) (exteriorPower.ιMulti ℝ k w) := by
          exact (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (exteriorPower.ιMulti ℝ k w)).symm
    _ = (Matrix.gram ℝ w).det := by
          rw [exteriorPower.inner_ιMulti_self]

/-- If the family `c` is orthogonal to the family `r`, the Gram matrix of the pointwise
sum is the sum of the two Gram matrices. -/
private lemma gram_of_sum_of_orth {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (r c : Fin k → E)
    (hcross : ∀ i j : Fin k, inner ℝ (r i) (c j) = 0) :
    Matrix.gram ℝ (fun j => r j + c j) = Matrix.gram ℝ r + Matrix.gram ℝ c := by
  ext i j
  simp only [Matrix.gram_apply, Matrix.add_apply]
  rw [inner_add_left, inner_add_right, inner_add_right]
  rw [hcross i j]
  have hcr : inner ℝ (c i) (r j) = 0 := by
    rw [real_inner_comm (r j) (c i)]
    exact hcross j i
  rw [hcr]
  ring

/-- The norm of the exterior product of a concatenation of two families is at most the
product of the norms of the exterior products of the two families. -/
lemma exteriorPower_norm_concat_le {p q : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (u : Fin p → E) (v : Fin q → E) :
    ‖exteriorPower.ιMulti ℝ (p + q) (Fin.append u v)‖ ≤
      ‖exteriorPower.ιMulti ℝ p u‖ * ‖exteriorPower.ιMulti ℝ q v‖ := by
  classical
  let z := exteriorPower.ιMulti ℝ (p + q) (Fin.append u v)
  let x := exteriorPower.ιMulti ℝ p u
  let y := exteriorPower.ιMulti ℝ q v
  let U : Submodule ℝ E := Submodule.span ℝ (Set.range u)
  let r : Fin q → E := fun j => v j - U.starProjection (v j)
  have hxw : ∀ j : Fin q, v j - r j ∈ U := by
    intro j
    dsimp [r, U]
    simpa using (Submodule.starProjection_apply_mem (U := U) (v j))
  have hr : ∀ j : Fin q, r j ∈ Uᗮ := by
    intro j
    dsimp [r, U]
    simpa using (Submodule.sub_starProjection_mem_orthogonal (K := U) (v j))
  have hcU : ∀ j : Fin q, v j - r j ∈ U := hxw
  -- `gram v = gram r + gram (v - r)`: the two summands are mutually orthogonal.
  have hcross : ∀ i j : Fin q, inner ℝ (r i) ((fun t : Fin q => v t - r t) j) = 0 := by
    intro i j
    have hrw : inner ℝ (v j - r j) (r i) = 0 :=
      (Submodule.mem_orthogonal U (r i)).mp (hr i) (v j - r j) (hcU j)
    exact inner_eq_zero_symm.mp hrw
  have hgr : Matrix.gram ℝ v = Matrix.gram ℝ r + Matrix.gram ℝ (fun j => v j - r j) := by
    calc
      Matrix.gram ℝ v = Matrix.gram ℝ (fun j => r j + (v j - r j)) := by
            congr 1
            funext j
            simp [r]
      _ = Matrix.gram ℝ r + Matrix.gram ℝ (fun j => v j - r j) := by
            exact gram_of_sum_of_orth r (fun j => v j - r j) hcross
  -- shearing `v` into the part orthogonal to `span u` does not change the Gram determinant
  have hdetShear :
      (Matrix.gram ℝ (Fin.append u v)).det =
        (Matrix.gram ℝ u).det * (Matrix.gram ℝ r).det := by
    calc
      (Matrix.gram ℝ (Fin.append u v)).det = (Matrix.gram ℝ (Sum.elim u v)).det :=
            det_gram_append_eq_det_gram_sum_elim u v
      _ = (Matrix.gram ℝ (Sum.elim u r)).det := by
            exact gram_det_eq_of_span_diff (E := E) (ι := Fin p) (κ := Fin q) u v r hxw
      _ = (Matrix.gram ℝ u).det * (Matrix.gram ℝ r).det := by
            exact gram_det_sum_elim_mul_of_orthogonal (E := E) (ι := Fin p) (κ := Fin q)
              u r hr
  -- `det (gram r) ≤ det (gram v)`, since `gram v - gram r = gram (v - r)` is PSD
  have hBpsd : (Matrix.gram ℝ r).PosSemidef := Matrix.posSemidef_gram ℝ r
  have hApsd : (Matrix.gram ℝ v).PosSemidef := Matrix.posSemidef_gram ℝ v
  have hsubpsd : ((Matrix.gram ℝ v) - (Matrix.gram ℝ r)).PosSemidef := by
    rw [hgr]
    simp
    exact Matrix.posSemidef_gram ℝ (fun j => v j - r j)
  have hdetGr_le : (Matrix.gram ℝ r).det ≤ (Matrix.gram ℝ v).det :=
    det_le_det_of_posSemidef_le (A := Matrix.gram ℝ v) (B := Matrix.gram ℝ r)
      hApsd hBpsd hsubpsd
  have hGu_nonneg : 0 ≤ (Matrix.gram ℝ u).det := (Matrix.posSemidef_gram ℝ u).det_nonneg
  have hdet_le : (Matrix.gram ℝ (Fin.append u v)).det ≤
      (Matrix.gram ℝ u).det * (Matrix.gram ℝ v).det := by
    rw [hdetShear]
    exact mul_le_mul_of_nonneg_left hdetGr_le hGu_nonneg
  -- now read the inequality of norms off the determinant inequality
  have hsq : ‖z‖ ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by
    calc
      ‖z‖ ^ 2 = (Matrix.gram ℝ (Fin.append u v)).det := by
            dsimp [z]
            exact normSq_ιMulti_eq_gram_det (Fin.append u v)
      _ ≤ (Matrix.gram ℝ u).det * (Matrix.gram ℝ v).det := hdet_le
      _ = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
            rw [normSq_ιMulti_eq_gram_det u, normSq_ιMulti_eq_gram_det v]
      _ = (‖x‖ * ‖y‖) ^ 2 := by ring
  have hnonnegZ : 0 ≤ ‖z‖ := norm_nonneg z
  have hnonnegXY : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg x) (norm_nonneg y)
  have habsZ : |‖z‖| = ‖z‖ := abs_of_nonneg hnonnegZ
  have habsXY : |‖x‖ * ‖y‖| = ‖x‖ * ‖y‖ := abs_of_nonneg hnonnegXY
  rw [← habsZ, ← habsXY]
  exact (sq_le_sq.mp (by simpa using hsq))

end Commons.Analysis.InnerProductSpace
