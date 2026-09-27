import Mathlib
import Submission.Work.EKLComp.FrameDefs

/-!
# The Gram matrices of `MA`, `MB`, `Mmat` are the identity

`MA` and `MB` are planar rotations (`(e₁,e₂)`- and `(e₀,e₁)`-plane respectively), so they are
orthogonal matrices; `Mmat = MB * MA` is then orthogonal as well.  Concretely we show
`Mᵀ * M = 1` for each of the three matrices.
-/

namespace Work.EKLComp

open Matrix

noncomputable section

/-- The `(e₁,e₂)`-plane rotation `MA` is orthogonal. -/
lemma transpose_MA_mul_MA (v : Fin 3 → ℝ) : Matrix.transpose (MA v) * MA v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MA, Matrix.mul_apply, Fin.sum_univ_three] <;>
    nlinarith [ca_sq_add_cb_sq v]

/-- The `(e₀,e₁)`-plane rotation `MB` is orthogonal. -/
lemma transpose_MB_mul_MB (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    Matrix.transpose (MB v) * MB v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MB, Matrix.mul_apply, Fin.sum_univ_three] <;>
    nlinarith [cc_sq_add_cd_sq v hv]

theorem frame_gram (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    Matrix.transpose (Work.EKLComp.MA v) * Work.EKLComp.MA v = 1 ∧
    Matrix.transpose (Work.EKLComp.MB v) * Work.EKLComp.MB v = 1 ∧
    Matrix.transpose (Work.EKLComp.Mmat v) * Work.EKLComp.Mmat v = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact transpose_MA_mul_MA v
  · exact transpose_MB_mul_MB v hv
  · rw [Mmat, Matrix.transpose_mul]
    -- `(MB * MA)ᵀ * (MB * MA) = MAᵀ * (MBᵀ * MB) * MA = MAᵀ * MA = 1`
    rw [← Matrix.mul_assoc ((MA v)ᵀ * (MB v)ᵀ) (MB v) (MA v),
      Matrix.mul_assoc (MA v)ᵀ (MB v)ᵀ (MB v), transpose_MB_mul_MB v hv, Matrix.mul_one,
      transpose_MA_mul_MA v]

end

end Work.EKLComp
