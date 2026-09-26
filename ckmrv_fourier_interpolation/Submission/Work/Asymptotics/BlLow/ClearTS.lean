import Mathlib
import Submission.Work.Asymptotics.BlLow.Defs
import Submission.Work.Kernels.KernelGrowth
import Submission.Work.Asymptotics.TileWindow.AfunFun_crossed_zero

/-!
# The `TS`-branch vanishing of `KfunClear` in the second variable

`KfunClear ℓ d τ (TS·τ) = 0` for every `τ : ℍ`, where `TS·τ = 1 + S·τ`.  This is the `δ = (T S)⁻¹`
instance of the family of "cleared kernel vanishing" lemmas; it is the input that makes the pole
of `z ↦ K(τ,z)` at the crossed translate `z = 1 - 1/τ` removable, and hence is what keeps
`‖Kaxis (Kfun ℓ d) τ t‖` bounded near the tangency arc `|τ - 1/2| = 1/2`, `Re τ > 0`.

It is a packaging of `Work.Asymptotics.TileWindow.AfunFun_crossed_zero`
(`AfunFun ℓ d τ ((T*S)•τ) = 0`, proved by the cancellation
`KPlusClear_crossed + KMinusClear_crossed = 0`) through
`Work.Asymptotics.KfunClear_eq_mul_AfunFun`.
-/

noncomputable section

open UpperHalfPlane ModularGroup

namespace Work.Asymptotics.BlLow

open Work.Kernels

/-- `(T * S) • τ = 1 + S • τ` on `ℍ`. -/
lemma ts_smul_eq (τ : UpperHalfPlane) :
    (ModularGroup.T * ModularGroup.S) • τ = (1 : ℝ) +ᵥ (ModularGroup.S • τ) := by
  rw [mul_smul, UpperHalfPlane.modular_T_smul]

/-- **The `TS`-branch vanishing of the cleared kernel in the second variable.**
`KfunClear ℓ d τ (1 + S·τ) = 0`. -/
theorem KfunClear_vadd_S (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) :
    Work.Kernels.KfunClear ℓ d τ ((1 : ℝ) +ᵥ (ModularGroup.S • τ)) = 0 := by
  rw [← ts_smul_eq τ, Work.Asymptotics.KfunClear_eq_mul_AfunFun,
    Work.Asymptotics.TileWindow.AfunFun_crossed_zero ℓ d hd τ, mul_zero]

end Work.Asymptotics.BlLow
