import Mathlib
import Submission.Subspace.NumberField
import Submission.Subspace.Stage3

/-!
# The inverse of the matrix of linear forms, over the coefficient field

Let `L : σ → σ → ℂ` have algebraic entries and let `K ⊆ ℂ` be a number field containing them.
Write `A` for the matrix `(L i j)` viewed over `K`.  Row-independence of `L` gives `A.det ≠ 0`,
so `A` is invertible; the *transposed* inverse `Λ = (A⁻¹)ᵀ` is the matrix of linear forms dual
to `L`, in the sense that the "`U`-coordinates" `u (h,k) = ∑ j, L k j * x (h,j)` of a point
recover `x` by `x (h,j) = ∑ k, Λ k j * u (h,k)`.

This is the matrix `Λ` used in the auxiliary-polynomial construction
(`Submission.Subspace.exists_flat_poly`) and in the `A`-bounds
(`Submission.Subspace.A_bounds`), where it also has to be rescaled by a positive integer to
become integral.
-/

set_option maxHeartbeats 800000

open scoped BigOperators Matrix

namespace Submission.Subspace

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The matrix of the linear forms `L`, viewed over the coefficient field `K`. -/
noncomputable def coeffMatrix (K : IntermediateField ℚ ℂ) (L : σ → σ → ℂ)
    (hLK : ∀ i j, L i j ∈ K) : Matrix σ σ ↥K := fun i j => ⟨L i j, hLK i j⟩

@[simp] lemma coeffMatrix_apply (K : IntermediateField ℚ ℂ) (L : σ → σ → ℂ)
    (hLK : ∀ i j, L i j ∈ K) (i j : σ) :
    ((coeffMatrix K L hLK i j : ↥K) : ℂ) = L i j := rfl

lemma coeffMatrix_map (K : IntermediateField ℚ ℂ) (L : σ → σ → ℂ) (hLK : ∀ i j, L i j ∈ K) :
    (coeffMatrix K L hLK).map ⇑((IntermediateField.val K).toRingHom) = Matrix.of L := by
  ext i j
  rfl

/-- The determinant of the coefficient matrix does not vanish. -/
lemma coeffMatrix_det_ne_zero (K : IntermediateField ℚ ℂ) (L : σ → σ → ℂ)
    (hLK : ∀ i j, L i j ∈ K) (hL : (Matrix.of L).det ≠ 0) :
    (coeffMatrix K L hLK).det ≠ 0 := by
  intro h
  apply hL
  have h1 : ((coeffMatrix K L hLK).det : ℂ) = (Matrix.of L).det := by
    have h2 := RingHom.map_det (IntermediateField.val K).toRingHom (coeffMatrix K L hLK)
    rw [RingHom.mapMatrix_apply] at h2
    rwa [coeffMatrix_map] at h2
  rw [← h1, h]
  simp

/-- The transposed inverse of the coefficient matrix: the matrix `Λ` dual to `L`. -/
noncomputable def lambdaMat (K : IntermediateField ℚ ℂ) (L : σ → σ → ℂ)
    (hLK : ∀ i j, L i j ∈ K) : Matrix σ σ ↥K := ((coeffMatrix K L hLK)⁻¹).transpose

/-- The same matrix, pushed forward to `ℂ` along the embedding of the coefficient field. -/
noncomputable def lambdaMatC (K : IntermediateField ℚ ℂ) (L : σ → σ → ℂ)
    (hLK : ∀ i j, L i j ∈ K) : Matrix σ σ ℂ :=
  (lambdaMat K L hLK).map ⇑((IntermediateField.val K).toRingHom)

/-- The transposed dual matrix is a left inverse of the coefficient matrix. -/
lemma lambdaMatC_transpose_mul (K : IntermediateField ℚ ℂ) (L : σ → σ → ℂ)
    (hLK : ∀ i j, L i j ∈ K) (hL : (Matrix.of L).det ≠ 0) :
    (lambdaMatC K L hLK)ᵀ * Matrix.of L = 1 := by
  have hunit : IsUnit (coeffMatrix K L hLK).det :=
    isUnit_iff_ne_zero.mpr (coeffMatrix_det_ne_zero K L hLK hL)
  have hmapmul : ∀ X Y : Matrix σ σ ↥K,
      (X * Y).map ⇑((IntermediateField.val K).toRingHom)
        = X.map ⇑((IntermediateField.val K).toRingHom)
          * Y.map ⇑((IntermediateField.val K).toRingHom) := by
    intro X Y
    simpa [RingHom.mapMatrix_apply] using
      map_mul (RingHom.mapMatrix ((IntermediateField.val K).toRingHom)) X Y
  show ((lambdaMat K L hLK).map ⇑((IntermediateField.val K).toRingHom))ᵀ *
      (coeffMatrix K L hLK).map ⇑((IntermediateField.val K).toRingHom) = (1 : Matrix σ σ ℂ)
  rw [← Matrix.transpose_map]
  rw [show (lambdaMat K L hLK)ᵀ = (coeffMatrix K L hLK)⁻¹ from by
    simp [lambdaMat, Matrix.transpose_transpose]]
  rw [← hmapmul, Matrix.nonsing_inv_mul _ hunit]
  show (1 : Matrix σ σ ↥K).map ⇑((IntermediateField.val K).toRingHom) = 1
  rw [← RingHom.mapMatrix_apply, map_one]

/-- `Λ` recovers the coordinates of an integer point from its `L`-values. -/
lemma lambdaMatC_mulVec_eq (K : IntermediateField ℚ ℂ) (L : σ → σ → ℂ)
    (hLK : ∀ i j, L i j ∈ K) (hL : (Matrix.of L).det ≠ 0) (x : σ → ℤ) :
    (fun j => ((x j : ℤ) : ℂ)) = fun j =>
      ∑ k, lambdaMatC K L hLK k j * (∑ i, L k i * (x i : ℂ)) := by
  have h := Matrix.mulVec_mulVec (fun i => ((x i : ℤ) : ℂ)) ((lambdaMatC K L hLK)ᵀ) (Matrix.of L)
  rw [lambdaMatC_transpose_mul K L hLK hL, Matrix.one_mulVec] at h
  funext j
  have hj := congrFun h j
  rw [← hj]
  rfl

/-- A bound for the entries of `Λ`. -/
lemma exists_lambdaMatC_bound (K : IntermediateField ℚ ℂ) (L : σ → σ → ℂ)
    (hLK : ∀ i j, L i j ∈ K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ i j, ‖lambdaMatC K L hLK i j‖ ≤ M := by
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · exact ⟨1, le_rfl, fun i => isEmptyElim i⟩
  · haveI := hσ
    refine ⟨max 1 (Finset.univ.sup' Finset.univ_nonempty
      (fun p : σ × σ => ‖lambdaMatC K L hLK p.1 p.2‖)), le_max_left _ _, fun i j => ?_⟩
    exact le_trans (Finset.le_sup' (f := fun p : σ × σ => ‖lambdaMatC K L hLK p.1 p.2‖)
      (Finset.mem_univ (i, j))) (le_max_right _ _)

/-- A bound for the entries of the coefficient matrix. -/
lemma exists_coeffMatrix_bound (K : IntermediateField ℚ ℂ) (L : σ → σ → ℂ)
    (hLK : ∀ i j, L i j ∈ K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ i j, ‖(coeffMatrix K L hLK i j : ℂ)‖ ≤ M := by
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · exact ⟨1, le_rfl, fun i => isEmptyElim i⟩
  · haveI := hσ
    refine ⟨max 1 (Finset.univ.sup' Finset.univ_nonempty
      (fun p : σ × σ => ‖(coeffMatrix K L hLK p.1 p.2 : ℂ)‖)), le_max_left _ _, fun i j => ?_⟩
    exact le_trans (Finset.le_sup' (f := fun p : σ × σ => ‖(coeffMatrix K L hLK p.1 p.2 : ℂ)‖)
      (Finset.mem_univ (i, j))) (le_max_right _ _)

end Submission.Subspace
