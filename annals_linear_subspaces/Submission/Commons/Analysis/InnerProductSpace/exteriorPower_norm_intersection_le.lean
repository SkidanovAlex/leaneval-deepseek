import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.gram_det_shear_orthogonal
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_concat_le

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped BigOperators

namespace Commons.Analysis.InnerProductSpace

open Matrix exteriorPower

/-- The Gram matrix of `Fin.append u v` is the reindexing of the Gram matrix of
`Sum.elim u v`, so the two determinants agree. -/
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

/-- Gram determinants are unchanged when the index type is replaced by an equivalent one
(permutation of the family). -/
private lemma det_gram_comp_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι']
    [DecidableEq ι] [DecidableEq ι'] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e : ι ≃ ι') (f : ι' → E) :
    (Matrix.gram ℝ (f ∘ e)).det = (Matrix.gram ℝ f).det := by
  classical
  have hgram : Matrix.gram ℝ (f ∘ e) = (Matrix.gram ℝ f).submatrix ⇑e ⇑e := by
    ext i j
    simp [Matrix.gram_apply]
  rw [hgram]
  exact Matrix.det_submatrix_equiv_self e (Matrix.gram ℝ f)

/-- Reassociating a triple `Fin.append`: Gram determinants agree for `(u ++ x) ++ y` and
`u ++ (x ++ y)`. -/
private lemma det_gram_append_assoc {m a b : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u : Fin m → E) (x : Fin a → E) (y : Fin b → E) :
    (Matrix.gram ℝ (Fin.append (Fin.append u x) y)).det =
      (Matrix.gram ℝ (Fin.append u (Fin.append x y))).det := by
  classical
  let e : Fin (m + a + b) ≃ Fin (m + (a + b)) := finCongr (Nat.add_assoc m a b)
  have hfam : Fin.append (Fin.append u x) y = (Fin.append u (Fin.append x y)) ∘ ⇑e := by
    dsimp [e]
    exact Fin.append_assoc u x y
  calc
    (Matrix.gram ℝ (Fin.append (Fin.append u x) y)).det
        = (Matrix.gram ℝ ((Fin.append u (Fin.append x y)) ∘ ⇑e)).det := by
            rw [hfam]
    _ = (Matrix.gram ℝ (Fin.append u (Fin.append x y))).det := by
            exact det_gram_comp_equiv e (Fin.append u (Fin.append x y))

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

/-- Subspace-intersection (Pluecker) inequality for decomposable exterior powers:
`covol(V) * covol(W) ≥ covol(V ∩ W) * covol(V + W)` for `V = span (u ++ x)`,
`W = span (u ++ y)`. -/
lemma exteriorPower_norm_intersection_le {m a b : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (u : Fin m → E) (x : Fin a → E) (y : Fin b → E) :
    ‖exteriorPower.ιMulti ℝ (m + a) (Fin.append u x)‖ *
      ‖exteriorPower.ιMulti ℝ (m + b) (Fin.append u y)‖ ≥
    ‖exteriorPower.ιMulti ℝ m u‖ *
      ‖exteriorPower.ιMulti ℝ (m + a + b) (Fin.append (Fin.append u x) y)‖ := by
  classical
  let A := exteriorPower.ιMulti ℝ (m + a) (Fin.append u x)
  let B := exteriorPower.ιMulti ℝ (m + b) (Fin.append u y)
  let C := exteriorPower.ιMulti ℝ m u
  let D := exteriorPower.ιMulti ℝ (m + a + b) (Fin.append (Fin.append u x) y)
  let U : Submodule ℝ E := Submodule.span ℝ (Set.range u)
  let r : Fin a → E := fun j => x j - U.starProjection (x j)
  let s : Fin b → E := fun j => y j - U.starProjection (y j)
  have hxr : ∀ j : Fin a, x j - r j ∈ U := by
    intro j
    dsimp [r, U]
    simpa using (Submodule.starProjection_apply_mem (U := U) (x j))
  have hr : ∀ j : Fin a, r j ∈ Uᗮ := by
    intro j
    dsimp [r, U]
    simpa using (Submodule.sub_starProjection_mem_orthogonal (K := U) (x j))
  have hys : ∀ j : Fin b, y j - s j ∈ U := by
    intro j
    dsimp [s, U]
    simpa using (Submodule.starProjection_apply_mem (U := U) (y j))
  have hs : ∀ j : Fin b, s j ∈ Uᗮ := by
    intro j
    dsimp [s, U]
    simpa using (Submodule.sub_starProjection_mem_orthogonal (K := U) (y j))
  have hxr_span : ∀ j : Fin a, x j - r j ∈ Submodule.span ℝ (Set.range u) := by
    intro j
    simpa [U] using hxr j
  have hr_span : ∀ j : Fin a, r j ∈ Submodule.orthogonal (Submodule.span ℝ (Set.range u)) := by
    intro j
    simpa [U] using hr j
  have hys_span : ∀ j : Fin b, y j - s j ∈ Submodule.span ℝ (Set.range u) := by
    intro j
    simpa [U] using hys j
  have hs_span : ∀ j : Fin b, s j ∈ Submodule.orthogonal (Submodule.span ℝ (Set.range u)) := by
    intro j
    simpa [U] using hs j
  have hxy_rs : ∀ j : Fin (a + b),
      (Fin.append x y) j - (Fin.append r s) j ∈ Submodule.span ℝ (Set.range u) := by
    intro j
    refine Fin.addCases (m := a) (n := b) (motive := fun k : Fin (a + b) =>
        (Fin.append x y) k - (Fin.append r s) k ∈ Submodule.span ℝ (Set.range u)) ?_ ?_ j
    · intro i
      simpa [Fin.append_left, U] using hxr i
    · intro i
      simpa [Fin.append_right, U] using hys i
  have hrs : ∀ j : Fin (a + b),
      (Fin.append r s) j ∈ Submodule.orthogonal (Submodule.span ℝ (Set.range u)) := by
    intro j
    refine Fin.addCases (m := a) (n := b) (motive := fun k : Fin (a + b) =>
        (Fin.append r s) k ∈ Submodule.orthogonal (Submodule.span ℝ (Set.range u))) ?_ ?_ j
    · intro i
      simpa [Fin.append_left, U] using hr i
    · intro i
      simpa [Fin.append_right, U] using hs i
  have hdet_ux : (Matrix.gram ℝ (Fin.append u x)).det =
      (Matrix.gram ℝ u).det * (Matrix.gram ℝ r).det := by
    calc
      (Matrix.gram ℝ (Fin.append u x)).det = (Matrix.gram ℝ (Sum.elim u x)).det :=
            det_gram_append_eq_det_gram_sum_elim u x
      _ = (Matrix.gram ℝ u).det * (Matrix.gram ℝ r).det := by
            exact gram_det_shear_orthogonal_of_span (E := E) (ι := Fin m) (κ := Fin a)
              u x r hxr_span hr_span
  have hdet_uy : (Matrix.gram ℝ (Fin.append u y)).det =
      (Matrix.gram ℝ u).det * (Matrix.gram ℝ s).det := by
    calc
      (Matrix.gram ℝ (Fin.append u y)).det = (Matrix.gram ℝ (Sum.elim u y)).det :=
            det_gram_append_eq_det_gram_sum_elim u y
      _ = (Matrix.gram ℝ u).det * (Matrix.gram ℝ s).det := by
            exact gram_det_shear_orthogonal_of_span (E := E) (ι := Fin m) (κ := Fin b)
              u y s hys_span hs_span
  have hdet_triple : (Matrix.gram ℝ (Fin.append (Fin.append u x) y)).det =
      (Matrix.gram ℝ u).det * (Matrix.gram ℝ (Fin.append r s)).det := by
    calc
      (Matrix.gram ℝ (Fin.append (Fin.append u x) y)).det
          = (Matrix.gram ℝ (Fin.append u (Fin.append x y))).det :=
              det_gram_append_assoc u x y
      _ = (Matrix.gram ℝ (Sum.elim u (Fin.append x y))).det :=
              det_gram_append_eq_det_gram_sum_elim u (Fin.append x y)
      _ = (Matrix.gram ℝ u).det * (Matrix.gram ℝ (Fin.append r s)).det := by
            exact gram_det_shear_orthogonal_of_span (E := E) (ι := Fin m) (κ := Fin (a + b))
              u (Fin.append x y) (Fin.append r s) hxy_rs hrs
  have hsq_concat : (Matrix.gram ℝ (Fin.append r s)).det ≤
      (Matrix.gram ℝ r).det * (Matrix.gram ℝ s).det := by
    have hnorm : ‖exteriorPower.ιMulti ℝ (a + b) (Fin.append r s)‖ ≤
        ‖exteriorPower.ιMulti ℝ a r‖ * ‖exteriorPower.ιMulti ℝ b s‖ :=
      exteriorPower_norm_concat_le (p := a) (q := b) r s
    have hsq : ‖exteriorPower.ιMulti ℝ (a + b) (Fin.append r s)‖ ^ 2 ≤
        (‖exteriorPower.ιMulti ℝ a r‖ * ‖exteriorPower.ιMulti ℝ b s‖) ^ 2 := by
      have hn1 : 0 ≤ ‖exteriorPower.ιMulti ℝ (a + b) (Fin.append r s)‖ := norm_nonneg _
      have hn2 : 0 ≤ ‖exteriorPower.ιMulti ℝ a r‖ * ‖exteriorPower.ιMulti ℝ b s‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have hle : |‖exteriorPower.ιMulti ℝ (a + b) (Fin.append r s)‖| ≤
          |‖exteriorPower.ιMulti ℝ a r‖ * ‖exteriorPower.ιMulti ℝ b s‖| := by
        rw [abs_of_nonneg hn1, abs_of_nonneg hn2]
        exact hnorm
      exact sq_le_sq.mpr hle
    calc
      (Matrix.gram ℝ (Fin.append r s)).det
          = ‖exteriorPower.ιMulti ℝ (a + b) (Fin.append r s)‖ ^ 2 := by
              exact (normSq_ιMulti_eq_gram_det (Fin.append r s)).symm
      _ ≤ (‖exteriorPower.ιMulti ℝ a r‖ * ‖exteriorPower.ιMulti ℝ b s‖) ^ 2 := hsq
      _ = ‖exteriorPower.ιMulti ℝ a r‖ ^ 2 * ‖exteriorPower.ιMulti ℝ b s‖ ^ 2 := by ring
      _ = (Matrix.gram ℝ r).det * (Matrix.gram ℝ s).det := by
              rw [normSq_ιMulti_eq_gram_det r, normSq_ιMulti_eq_gram_det s]
  have hA : ‖A‖ ^ 2 = (Matrix.gram ℝ (Fin.append u x)).det := by
    simpa [A] using normSq_ιMulti_eq_gram_det (Fin.append u x)
  have hB : ‖B‖ ^ 2 = (Matrix.gram ℝ (Fin.append u y)).det := by
    simpa [B] using normSq_ιMulti_eq_gram_det (Fin.append u y)
  have hC : ‖C‖ ^ 2 = (Matrix.gram ℝ u).det := by
    simpa [C] using normSq_ιMulti_eq_gram_det u
  have hD : ‖D‖ ^ 2 = (Matrix.gram ℝ (Fin.append (Fin.append u x) y)).det := by
    simpa [D] using normSq_ιMulti_eq_gram_det (Fin.append (Fin.append u x) y)
  have hsq : (‖C‖ * ‖D‖) ^ 2 ≤ (‖A‖ * ‖B‖) ^ 2 := by
    calc
      (‖C‖ * ‖D‖) ^ 2 = ‖C‖ ^ 2 * ‖D‖ ^ 2 := by ring
      _ = (Matrix.gram ℝ u).det * (Matrix.gram ℝ (Fin.append (Fin.append u x) y)).det := by
            rw [hC, hD]
      _ = (Matrix.gram ℝ u).det *
            ((Matrix.gram ℝ u).det * (Matrix.gram ℝ (Fin.append r s)).det) := by
            rw [hdet_triple]
      _ = (Matrix.gram ℝ u).det ^ 2 * (Matrix.gram ℝ (Fin.append r s)).det := by ring
      _ ≤ (Matrix.gram ℝ u).det ^ 2 * ((Matrix.gram ℝ r).det * (Matrix.gram ℝ s).det) := by
            exact mul_le_mul_of_nonneg_left hsq_concat (sq_nonneg (Matrix.gram ℝ u).det)
      _ = (Matrix.gram ℝ u).det * (Matrix.gram ℝ r).det *
            ((Matrix.gram ℝ u).det * (Matrix.gram ℝ s).det) := by ring
      _ = (Matrix.gram ℝ (Fin.append u x)).det * (Matrix.gram ℝ (Fin.append u y)).det := by
            rw [← hdet_ux, ← hdet_uy]
      _ = ‖A‖ ^ 2 * ‖B‖ ^ 2 := by rw [← hA, ← hB]
      _ = (‖A‖ * ‖B‖) ^ 2 := by ring
  have hnonneg1 : 0 ≤ ‖C‖ * ‖D‖ := mul_nonneg (norm_nonneg C) (norm_nonneg D)
  have hnonneg2 : 0 ≤ ‖A‖ * ‖B‖ := mul_nonneg (norm_nonneg A) (norm_nonneg B)
  have habs1 : |‖C‖ * ‖D‖| = ‖C‖ * ‖D‖ := abs_of_nonneg hnonneg1
  have habs2 : |‖A‖ * ‖B‖| = ‖A‖ * ‖B‖ := abs_of_nonneg hnonneg2
  have hmain : ‖C‖ * ‖D‖ ≤ ‖A‖ * ‖B‖ := by
    have hle : |‖C‖ * ‖D‖| ≤ |‖A‖ * ‖B‖| := sq_le_sq.mp (by simpa using hsq)
    rwa [habs1, habs2] at hle
  change ‖A‖ * ‖B‖ ≥ ‖C‖ * ‖D‖
  exact hmain

end Commons.Analysis.InnerProductSpace
