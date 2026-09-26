/-
# A concrete choice of the logarithm data, and the concrete kernels

`Work.Kernels.LogLambda.logLambdaData_exists` proves that `LogLambdaData` (the pair
`(𝓛, 𝓛_S)` of CKMRV §2.1.5) is inhabited.  This file fixes a concrete such choice
`Work.Kernels.logLambda`, so that `K_-^{(d)}`, `K^{(d)}` and `K̂^{(d)}` are no longer
relative to a parameter, and restates the functional equations and the growth bounds
for that specific choice.
-/
import Mathlib
import Submission.Work.Kernels.LogLambda.logLambdaData_exists
import Submission.Work.Kernels.KMinusSlash
import Submission.Work.Kernels.KernelGrowth

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels

/-- A concrete choice of the logarithm data `(𝓛, 𝓛_S)` of CKMRV §2.1.5. -/
noncomputable def logLambda : LogLambdaData := Classical.choice LogLambda.logLambdaData_exists

lemma logLambda_memP : ModerateGrowthOn Set.univ logLambda.L ∧
    ModerateGrowthOn Set.univ logLambda.L_S := ⟨logLambda.memP, logLambda.memP_S⟩

/-- `K_-^{(d)}` for the concrete logarithm data, annihilated by `(T-I)²` in `τ`. -/
theorem KMinus_slash_T2_concrete (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    slash ((d : ℤ) / 2) ((R_T - 1) ^ 2) (fun τ => KMinus logLambda d τ z) = 0 :=
  KMinus_slash_T2 logLambda d hd z

/-- `K_-^{(d)}` for the concrete logarithm data, annihilated by `S-I` in `τ`. -/
theorem KMinus_slash_S_sub_concrete (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    slash ((d : ℤ) / 2) (R_S - 1) (fun τ => KMinus logLambda d τ z) = 0 :=
  KMinus_slash_S_sub logLambda d hd z

/-- The `τ`-variable growth bounds of Theorem 4.9(4) for the concrete kernels. -/
theorem ConcreteClear_growth_tau (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    InP (fun τ : ℍ => KPlusClear d τ z) ∧
    InP (fun τ : ℍ => KMinusClear logLambda d τ z) ∧
    InP (fun τ : ℍ => KfunClear logLambda d τ z) ∧
    InP (fun τ : ℍ => KhatClear logLambda d τ z) := by
  obtain ⟨h1, h3⟩ := KernelClear_growth_tau logLambda d hd z
  exact ⟨KernelGrowth.KPlusClear_growth_tau d hd z,
    KernelGrowth.KMinusClear_growth_tau logLambda d hd z, h1, h3⟩

/-- The `z`-variable growth bounds of Theorem 4.9(4) for the concrete kernels. -/
theorem ConcreteClear_growth_z (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : ℍ) :
    InP (fun z : ℍ => KPlusClear d τ z) ∧
    InP (fun z : ℍ => KMinusClear logLambda d τ z) ∧
    InP (fun z : ℍ => KfunClear logLambda d τ z) ∧
    InP (fun z : ℍ => KhatClear logLambda d τ z) := by
  obtain ⟨h1, h3⟩ := KernelClear_growth_z logLambda d hd τ
  exact ⟨KernelGrowth.KPlusClear_growth_z d hd τ,
    KernelGrowth.KMinusClear_growth_z logLambda d hd τ, h1, h3⟩

end Work.Kernels
