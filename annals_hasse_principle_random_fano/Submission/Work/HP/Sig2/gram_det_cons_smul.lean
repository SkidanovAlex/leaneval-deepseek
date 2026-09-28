import Mathlib
import Submission.Work.HP.ball_count_schmidt

/-!
# Determinant of the Gram matrix after adjoining one vector

For a nonzero vector `p` and a family `z : Fin m → EuclideanSpace ℝ ι`, adjoining `p` to the
family multiplies the determinant of the Gram matrix by `‖p‖²` once every vector of the family is
orthogonally projected onto `p^⊥`:

`det (gram (p, z)) = ‖p‖² * det (gram (projU p ∘ z))`.

This is the Schur-complement formula for the block matrix
`[[‖p‖², ⟪p,z⟫], [⟪z,p⟫, gram z]]`, whose Schur complement with respect to the leading `1 × 1`
block `‖p‖²` is exactly `gram (projU p ∘ z)`.
-/

namespace Work.HP.Sig2

open Matrix

/-- Schur-complement determinant formula for a block matrix with a `1 × 1` leading block
`[g]` (`g ≠ 0`):
`det [[g, B], [C, D]] = g * det (D - C * [g⁻¹] * B)`. -/
theorem det_fromBlocks_fin_one {m : ℕ} (g : ℝ) (hg : g ≠ 0)
    (B : Matrix (Fin 1) (Fin m) ℝ) (C : Matrix (Fin m) (Fin 1) ℝ) (D : Matrix (Fin m) (Fin m) ℝ) :
    (Matrix.fromBlocks (Matrix.of (fun _ _ : Fin 1 => g)) B C D).det
      = g * (D - C * Matrix.of (fun _ _ : Fin 1 => g⁻¹) * B).det := by
  let A : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => g
  let Ainv : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => g⁻¹
  letI : Invertible A :=
    { invOf := Ainv
      invOf_mul_self := by
        show Ainv * A = 1
        ext i j
        fin_cases i; fin_cases j
        rw [Matrix.mul_apply]
        simp [Ainv, A, Matrix.of_apply, inv_mul_cancel₀ hg]
      mul_invOf_self := by
        show A * Ainv = 1
        ext i j
        fin_cases i; fin_cases j
        rw [Matrix.mul_apply]
        simp [Ainv, A, Matrix.of_apply, mul_inv_cancel₀ hg] }
  have hAinv : (⅟A : Matrix (Fin 1) (Fin 1) ℝ) = Ainv := rfl
  have hdetA : A.det = g := by
    rw [Matrix.det_fin_one]; simp [A, Matrix.of_apply]
  rw [Matrix.det_fromBlocks₁₁]
  rw [hdetA, hAinv]

theorem gram_det_cons_smul {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (p : EuclideanSpace ℝ ι) (hp : p ≠ 0) (z : Fin m → EuclideanSpace ℝ ι) :
    (Matrix.gram ℝ (Sum.elim (fun _ : Fin 1 => p) z)).det
      = ‖p‖ ^ 2 * (Matrix.gram ℝ (fun i => Work.HP.projU p (z i))).det := by
  have hp2 : (inner ℝ p p) ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]; exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hp)
  let B : Matrix (Fin 1) (Fin m) ℝ := Matrix.of fun _ (j : Fin m) => inner ℝ p (z j)
  let C : Matrix (Fin m) (Fin 1) ℝ := Matrix.of fun i (_ : Fin 1) => inner ℝ (z i) p
  let D : Matrix (Fin m) (Fin m) ℝ := Matrix.gram ℝ z
  -- The Gram matrix of `(p, z)` is the block matrix `[[⟪p,p⟫, B], [C, D]]`.
  have hG : Matrix.gram ℝ (Sum.elim (fun _ : Fin 1 => p) z)
      = Matrix.fromBlocks (Matrix.of (fun _ _ : Fin 1 => inner ℝ p p)) B C D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · fin_cases i; fin_cases j; rfl
    · rfl
    · rfl
    · rfl
  -- The Schur complement of the leading block is the Gram matrix of the projections.
  have hEq : D - C * Matrix.of (fun _ _ : Fin 1 => (inner ℝ p p)⁻¹) * B
      = Matrix.gram ℝ (fun i => Work.HP.projU p (z i)) := by
    ext i j
    simp only [D, C, B, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one, Matrix.of_apply,
      Matrix.gram_apply, Work.HP.projU_apply, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
    ring
  rw [hG, det_fromBlocks_fin_one (inner ℝ p p) hp2 B C D, hEq, real_inner_self_eq_norm_sq]

end Work.HP.Sig2
