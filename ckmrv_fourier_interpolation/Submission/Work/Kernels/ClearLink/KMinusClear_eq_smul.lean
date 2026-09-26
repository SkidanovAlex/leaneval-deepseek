import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ClearLink.UpsilonMinusClear_eq_smul

namespace Work.Kernels.ClearLink

/-- Entrywise form of `UpsilonMinusClear_eq_smul`: the cleared coefficient matrix `Υ_-` is the
`growthPrefactor` multiple of `Υ_-`, entry by entry. -/
lemma UpsilonMinusClear_apply_eq (d : ℕ) (hd : d = 8 ∨ d = 24) (τ z : UpperHalfPlane)
    (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) (i j : Fin 3) :
    Work.Kernels.UpsilonMinusClear d τ z i j
      = Work.Kernels.growthPrefactor d τ z * Work.Kernels.UpsilonMinus d τ z i j := by
  rw [UpsilonMinusClear_eq_smul d hd τ z h, Matrix.smul_apply, smul_eq_mul]

/-- Off the diagonal `j(τ) ≠ j(z)`, the cleared kernel `K_-^Clear` is the `growthPrefactor`
multiple of `K_-`.  This is the `K_-` counterpart of `KPlusClear_eq_smul`. -/
theorem KMinusClear_eq_smul (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ z : UpperHalfPlane) (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    Work.Kernels.KMinusClear ℓ d τ z
      = Work.Kernels.growthPrefactor d τ z * Work.Kernels.KMinus ℓ d τ z := by
  simp only [Work.Kernels.KMinusClear, Work.Kernels.KMinus]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  rw [UpsilonMinusClear_apply_eq d hd τ z h i j]
  ring

end Work.Kernels.ClearLink
