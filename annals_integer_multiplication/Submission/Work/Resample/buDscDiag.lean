import Mathlib
import Submission.Work.Resample.sliceB1defs

namespace Work.Resample

/-- `D'` is a scalar multiple of a diagonal matrix whose entries are real numbers, so
`(c • diagonal f) *ᵥ y` at `ℓ` is the (real) entry times `y ℓ`. -/
private lemma diag_smul_mulVec_ofReal {n : Type*} [Fintype n] [DecidableEq n]
    (c : ℝ) (f : n → ℝ) (y : n → ℂ) (ℓ : n) :
    (((c : ℂ) • Matrix.diagonal (fun i => ((f i : ℝ) : ℂ))).mulVec y ℓ)
      = ((((c : ℂ) • Matrix.diagonal (fun i => ((f i : ℝ) : ℂ))) ℓ ℓ).re : ℂ) * y ℓ := by
  have hentry : ((c : ℂ) • Matrix.diagonal (fun i => ((f i : ℝ) : ℂ))) ℓ ℓ
      = (c : ℂ) * ((f ℓ : ℝ) : ℂ) := by
    rw [Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
  have hreal : (((c : ℂ) * ((f ℓ : ℝ) : ℂ)).re : ℂ) = (c : ℂ) * ((f ℓ : ℝ) : ℂ) := by
    rw [show ((c : ℂ) * ((f ℓ : ℝ) : ℂ)) = ((c * f ℓ : ℝ) : ℂ) by rw [Complex.ofReal_mul]]
    simp
  rw [Matrix.smul_mulVec, Pi.smul_apply, Matrix.mulVec_diagonal, smul_eq_mul, hentry, hreal]
  ring

/-- The diagonal weight matrix `D̃' = D'` of `HvdH` acts on a vector by scalar multiplication
with its (real) diagonal entry. -/
theorem buDscDiag (s t α : ℕ) (y : Fin s → ℂ) (ℓ : Fin s) :
    (HvdH.diagD' s t α).mulVec y ℓ = ((HvdH.diagD' s t α ℓ ℓ).re : ℂ) * y ℓ := by
  have hcast : (((1 : ℝ) / (2 : ℝ) ^ (2 * α ^ 2 - 2) : ℝ) : ℂ)
      = 1 / (2 : ℂ) ^ (2 * α ^ 2 - 2) := by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow]
    norm_num
  simp only [HvdH.diagD', HvdH.diagD, ← hcast]
  exact diag_smul_mulVec_ofReal _ _ y ℓ

end Work.Resample
