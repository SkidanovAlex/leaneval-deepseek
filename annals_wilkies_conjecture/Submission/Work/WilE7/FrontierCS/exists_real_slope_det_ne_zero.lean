import Mathlib
import Submission.Work.WilE7.FrontierCS.Defs
import Submission.Work.WilE7.FrontierCS.exists_right_factor
import Submission.Work.WilE7.FrontierCS.exists_smul_add_det_ne_zero

namespace Work.WilE7.FrontierCS

/-- **N2b (CS-slice grid lemma, real-slope step).**

If the linear map `(t,e) ↦ P t + Q e : ℝ^d × ℝ^j → ℝ^j` is surjective (equivalently the block
matrix `[P | Q]` has full row rank), then there is a real slope matrix `Λ` with `P * Λ + Q`
invertible.

Proof.  Surjectivity supplies a right inverse, i.e. matrices `L_t : Matrix (Fin d) (Fin j) ℝ` and
`L_u : Matrix (Fin j) (Fin j) ℝ` with `P * L_t + Q * L_u = 1`.  Choose a real number `a` for which
both `L_u + a • 1` and `1 + a • Q` are invertible (such an `a` exists since `det (L_u + a • 1)` is a
monic polynomial of degree `j` in `a`, while `det (1 + a • Q)` has constant term `1`; the union of
their finitely many roots cannot be all of `ℝ`).  Set `Λ := L_t * (L_u + a • 1)⁻¹`.  Then
`(P * Λ + Q) * (L_u + a • 1) = P * L_t + Q * (L_u + a • 1) = (P * L_t + Q * L_u) + a • Q = 1 + a • Q`,
so `det (P * Λ + Q) * det (L_u + a • 1) = det (1 + a • Q) ≠ 0`, and both factors are nonzero; in
particular `det (P * Λ + Q) ≠ 0`. -/
theorem exists_real_slope_det_ne_zero {d j : ℕ} (P : Matrix (Fin j) (Fin d) ℝ)
    (Q : Matrix (Fin j) (Fin j) ℝ)
    (hsurj : ∀ y : Fin j → ℝ, ∃ t e, P.mulVec t + Q.mulVec e = y) :
    ∃ Λ : Matrix (Fin d) (Fin j) ℝ, (P * Λ + Q).det ≠ 0 := by
  obtain ⟨L_t, L_u, hrel⟩ := exists_right_factor P Q hsurj
  obtain ⟨a, ha1, ha2⟩ := exists_smul_add_det_ne_zero L_u Q
  refine ⟨L_t * (L_u + a • 1)⁻¹, ?_⟩
  -- `(L_u + a • 1)⁻¹ * (L_u + a • 1) = 1`, since `det (L_u + a • 1) ≠ 0`.
  have hinv : (L_u + a • 1)⁻¹ * (L_u + a • 1) = 1 :=
    Matrix.nonsing_inv_mul (L_u + a • 1) (isUnit_iff_ne_zero.mpr ha1)
  -- The key identity.
  have hkey : (P * (L_t * (L_u + a • 1)⁻¹) + Q) * (L_u + a • 1) = 1 + a • Q := by
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hinv, Matrix.mul_one,
      Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, ← add_assoc, hrel]
  -- Taking determinants gives the result.
  have hdet : ((P * (L_t * (L_u + a • 1)⁻¹) + Q) * (L_u + a • 1)).det ≠ 0 := by
    rw [hkey]; exact ha2
  rw [Matrix.det_mul] at hdet
  intro h0
  exact hdet (by rw [h0, zero_mul])

end Work.WilE7.FrontierCS
