import Mathlib
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Residues.KPlusClear_TS
import Submission.Work.Residues.KMinusClear_TS
import Submission.Work.Asymptotics.KClear_S_vanishing
import Submission.Work.Asymptotics.Kaxis_Kfun_noncoincidence_E

namespace Work.Asymptotics

open Work.Kernels Work.Residues

/-- **The cleared value function `AfunFun` vanishes at the two cusp translates.**

For `n = ±1`, `σ ∈ ℍ` and `d ∈ {8, 24}`,

  `AfunFun ℓ d (n +ᵥ σ) (S • σ) = 0`.

Since `AfunFun ℓ d τ z = (K_+^{clear} d τ z + K_-^{clear} ℓ d τ z) / (2 Δ(τ) Δ(z)^e)`, and the
second argument `z = S • σ` satisfies `σ = S • z` (`S` is an involution), the point `τ = n +ᵥ σ`
is `τ = n +ᵥ (S • z)`, where both cleared kernels vanish: for `n = 1` this is
`KPlusClear_TS`/`KMinusClear_TS` (the residue `φ(TS) = 0`) and for `n = -1` it is
`KPlusClear_Tinv_S`/`KMinusClear_Tinv_S` (the residue `φ(T⁻¹S) = 0`, derived from the
second-difference equation `(T-I)² = 0`). -/
theorem AfunFun_S_vadd_eq_zero (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (n : ℤ) (hn : n = 1 ∨ n = -1) (σ : UpperHalfPlane) :
    Work.Asymptotics.AfunFun ℓ d ((n : ℝ) +ᵥ σ) (ModularGroup.S • σ) = 0 := by
  have hS : ModularGroup.S • (ModularGroup.S • σ) = σ := Work.Asymptotics.S_smul_S_smul σ
  have hnr : (n : ℝ) = 1 ∨ (n : ℝ) = -1 := by
    rcases hn with h | h <;> simp [h]
  rcases hnr with h | h
  · have hplus : KPlusClear d ((1 : ℝ) +ᵥ σ) (ModularGroup.S • σ) = 0 := by
      have hh := KPlusClear_TS d hd (ModularGroup.S • σ)
      rwa [hS] at hh
    have hminus : KMinusClear ℓ d ((1 : ℝ) +ᵥ σ) (ModularGroup.S • σ) = 0 := by
      have hh := KMinusClear_TS ℓ d hd (ModularGroup.S • σ)
      rwa [hS] at hh
    rw [h, AfunFun, AfunPlus, AfunMinus, hplus, hminus]
    ring
  · have hplus : KPlusClear d ((-1 : ℝ) +ᵥ σ) (ModularGroup.S • σ) = 0 := by
      have hh := KPlusClear_Tinv_S d hd (ModularGroup.S • σ)
      rwa [hS] at hh
    have hminus : KMinusClear ℓ d ((-1 : ℝ) +ᵥ σ) (ModularGroup.S • σ) = 0 := by
      have hh := KMinusClear_Tinv_S ℓ d hd (ModularGroup.S • σ)
      rwa [hS] at hh
    rw [h, AfunFun, AfunPlus, AfunMinus, hplus, hminus]
    ring

end Work.Asymptotics
