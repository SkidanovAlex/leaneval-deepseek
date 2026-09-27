import Mathlib
import Submission.Work.EKLComp.EucDefs
import Submission.Work.EKLComp.FrameDefs
import Submission.Work.EKLComp.frame_gram
import Submission.Work.EKLComp.frame_det
import Submission.Work.EKLComp.frame_entry_bounds
import Submission.Work.EKLComp.dot3_cauchy_schwarz

/-!
# `Work.EKLComp.exists_orthonormal_frame`

For every non-zero `v : Fin 3 → ℝ` there is an orientation-preserving Euclidean isometry
(`det = 1`, dot-product preserving) `T` of `Fin 3 → ℝ` with `T v = enorm3 v • e3 0`, whose matrix
has all entries of absolute value at most `1` and whose inverse maps every vector into the cube of
radius `enorm3`.

The map is the composition of two planar Givens rotations: `MA v` rotates in the `(e₁, e₂)`-plane
killing the last two coordinates of `v`, and `MB v` rotates in the `(e₀, e₁)`-plane killing the one
remaining off-axis coordinate.  See `FrameDefs` for the definitions and the sub-lemmas.
-/

namespace Work.EKLComp

open Matrix

set_option linter.style.haveILetI false

noncomputable section

/-- `e3 i` is the standard unit vector: `dot3 (e3 i) y = y i`. -/
lemma dot3_e3_left (i : Fin 3) (y : Fin 3 → ℝ) : dot3 (e3 i) y = y i := by
  fin_cases i <;> simp [e3, dot3, Pi.single_apply]

/-- The standard basis vectors are unit vectors for `enorm3`. -/
lemma enorm3_e3 (i : Fin 3) : enorm3 (e3 i) = 1 := by
  unfold enorm3
  rw [dot3_e3_left]
  simp [e3]

/-- A matrix `M` with `Mᵀ * M = 1` preserves the Euclidean inner product `dot3`. -/
lemma dot3_mulVec_of_transpose_mul (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : Mᵀ * M = 1)
    (x y : Fin 3 → ℝ) : dot3 (M *ᵥ x) (M *ᵥ y) = dot3 x y := by
  have e1 : dot3 (M *ᵥ x) (M *ᵥ y) = (M *ᵥ x) ⬝ᵥ (M *ᵥ y) := rfl
  rw [e1, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hM]
  have hx : x ᵥ* (1 : Matrix (Fin 3) (Fin 3) ℝ) = x := by
    ext i; simp [Matrix.vecMul, dotProduct, Matrix.one_apply]
  rw [hx]
  rfl

/-- For a bijective linear isometry `T`, the inverse is the adjoint: `dot3 (T x) y = dot3 x (T.symm y)`. -/
lemma dot3_apply_symm (T : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ))
    (hT : ∀ x y, dot3 (T x) (T y) = dot3 x y) (x y : Fin 3 → ℝ) :
    dot3 (T x) y = dot3 x (T.symm y) := by
  conv_lhs => rw [← T.apply_symm_apply y]
  rw [hT x (T.symm y)]

/-- `Mmat v` sends `v` to `enorm3 v • e3 0`. -/
lemma Mmat_mulVec_v (v : Fin 3 → ℝ) :
    Matrix.mulVec (Mmat v) v = enorm3 v • e3 0 := by
  rw [Mmat, ← Matrix.mulVec_mulVec]
  have hMA : Matrix.mulVec (MA v) v = fun i => ![v 0, sv v, 0] i := by
    funext i; fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, MA]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, MA, ca_mul_v_one_add_cb_mul_v_two v]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, MA]
      linear_combination (neg_cb_mul_v_one_add_ca_mul_v_two v)
  rw [hMA]
  have hMB : Matrix.mulVec (MB v) (fun i => ![v 0, sv v, 0] i) = fun i => ![enorm3 v, 0, 0] i := by
    funext i; fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, MB, cc_mul_v_zero_add_cd_mul_sv v]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, MB]
      linear_combination (neg_cd_mul_v_zero_add_cc_mul_sv v)
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, MB]
  rw [hMB]
  funext i; fin_cases i <;> simp [e3]

theorem exists_orthonormal_frame (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    ∃ T : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ),
      T v = Work.EKLComp.enorm3 v • Work.EKLComp.e3 0 ∧
      (∀ x, Work.EKLComp.enorm3 (T x) = Work.EKLComp.enorm3 x) ∧
      (∀ x y, Work.EKLComp.dot3 (T x) (T y) = Work.EKLComp.dot3 x y) ∧
      (LinearMap.toMatrix' T.toLinearMap).det = 1 ∧
      (∀ i j, |(LinearMap.toMatrix' T.toLinearMap) i j| ≤ 1) ∧
      (∀ (y : Fin 3 → ℝ) (i : Fin 3), |(T.symm y) i| ≤ Work.EKLComp.enorm3 y) := by
  obtain ⟨_hgramA, _hgramB, hgramM⟩ := frame_gram v hv
  have hdet : (Mmat v).det = 1 := frame_det v hv
  haveI : Invertible (Mmat v).det := by rw [hdet]; exact invertibleOne
  let T : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
    Matrix.toLinearEquiv' (Mmat v) (Matrix.invertibleOfDetInvertible (Mmat v))
  have hTapply : ∀ x : Fin 3 → ℝ, T x = (Mmat v) *ᵥ x := by
    intro x
    show (Matrix.toLin' (Mmat v)) x = (Mmat v) *ᵥ x
    rw [Matrix.toLin'_apply]
  have hmat : LinearMap.toMatrix' T.toLinearMap = Mmat v := by
    show LinearMap.toMatrix' (Matrix.toLin' (Mmat v)) = Mmat v
    rw [LinearMap.toMatrix'_toLin']
  have hdot : ∀ x y, dot3 (T x) (T y) = dot3 x y := by
    intro x y
    rw [hTapply x, hTapply y]
    exact dot3_mulVec_of_transpose_mul (Mmat v) hgramM x y
  have hnorm : ∀ x, enorm3 (T x) = enorm3 x := by
    intro x; unfold enorm3; rw [hdot x x]
  have hsymm : ∀ (y : Fin 3 → ℝ) (i : Fin 3), |(T.symm y) i| ≤ enorm3 y := by
    intro y i
    have h1 : (T.symm y) i = dot3 (e3 i) (T.symm y) := by rw [dot3_e3_left]
    have h2 : dot3 (e3 i) (T.symm y) = dot3 (T (e3 i)) y :=
      (dot3_apply_symm T hdot (e3 i) y).symm
    rw [h1, h2]
    calc |dot3 (T (e3 i)) y| ≤ enorm3 (T (e3 i)) * enorm3 y := dot3_cauchy_schwarz (T (e3 i)) y
      _ = enorm3 (e3 i) * enorm3 y := by rw [hnorm (e3 i)]
      _ = enorm3 y := by rw [enorm3_e3, one_mul]
  refine ⟨T, ?_, hnorm, hdot, ?_, ?_, hsymm⟩
  · rw [hTapply v]; exact Mmat_mulVec_v v
  · rw [hmat]; exact frame_det v hv
  · intro i j; rw [hmat]; exact frame_entry_bounds v hv i j

end

end Work.EKLComp
