import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Asymptotics.mdiff_eta

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

/-!
## Continuity of the `𝓛_S`-piece `𝒱₀^S` of `𝒱₀`

The function

  `τ ↦ 3456 E₄(τ)³ + (3 j(τ) Y(τ) - 1728 (U² + V² - 2W²)(τ) E₈(τ)) · 𝓛_S(τ)`

is a finite algebraic combination of the holomorphic (hence continuous) functions `E₄`, `E₆`,
`Δ`, the theta functions `U = θ₀₀⁴`, `V = θ₁₀⁴`, `W = θ₀₁⁴`, the `j`-invariant `j = E₄³/Δ`
(well defined since `Δ ≠ 0`), the combination `U² + V² - 2W² = ξ₄|₄S` and the logarithm
`𝓛_S` (holomorphic by hypothesis), so it is continuous on `ℍ`.
-/

theorem V0LS_continuous (ℓ : Work.Kernels.LogLambdaData) :
    Continuous (fun τ : UpperHalfPlane =>
      3456 * Work.Kernels.E4Fun τ ^ 3
        + (3 * Work.Kernels.jInvariantFun τ * Work.Residues.Yfun τ
            - 1728 * (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
                - 2 * Work.Kernels.WFun τ ^ 2) * Work.Kernels.E8Fun τ) * ℓ.L_S τ) := by
  have hE4 : Continuous (fun τ : ℍ => Work.Kernels.E4Fun τ) :=
    Work.Kernels.ClassicalFacts.E4Fun_mem_InP.1.continuous
  have hE6 : Continuous (fun τ : ℍ => Work.Kernels.E6Fun τ) :=
    Work.Kernels.ClassicalFacts.E6Fun_mem_InP.1.continuous
  have hDelta : Continuous (fun τ : ℍ => Work.Kernels.DeltaFun τ) :=
    Work.Kernels.ClassicalFacts.DeltaFun_mem_InP.1.continuous
  have hU : Continuous (fun τ : ℍ => Work.Kernels.UFun τ) :=
    (Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.1.continuous).pow 4
  have hV : Continuous (fun τ : ℍ => Work.Kernels.VFun τ) :=
    (Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.1.continuous).pow 4
  have hW : Continuous (fun τ : ℍ => Work.Kernels.WFun τ) :=
    (Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.1.continuous).pow 4
  -- the `j`-invariant is holomorphic (and `Δ` never vanishes)
  have hj : Continuous (fun τ : ℍ => Work.Kernels.jInvariantFun τ) := by
    have h : (fun τ : ℍ => Work.Kernels.jInvariantFun τ)
        = fun τ : ℍ => Work.Kernels.E4Fun τ ^ 3 / Work.Kernels.DeltaFun τ := rfl
    rw [h]
    exact (hE4.pow 3).div hDelta (fun τ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
  -- the `S`-translate `ξ₄|₄S = U² + V² - 2W²` and `ξ₂|₂S = -(U + V)`
  have hxi4 : Continuous (fun τ : ℍ => Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
      - 2 * Work.Kernels.WFun τ ^ 2) :=
    ((hU.pow 2).add (hV.pow 2)).sub ((hW.pow 2).const_mul 2)
  have hxi2 : Continuous (fun τ : ℍ => -(Work.Kernels.UFun τ + Work.Kernels.VFun τ)) :=
    (hU.add hV).neg
  have hE8 : Continuous (fun τ : ℍ => Work.Kernels.E8Fun τ) := hE4.pow 2
  have hE10 : Continuous (fun τ : ℍ => Work.Kernels.E10Fun τ) := hE4.mul hE6
  -- `Y = (ξ₄|₄S) E₈ - (ξ₂|₂S) E₁₀`
  have hY : Continuous (fun τ : ℍ => Work.Residues.Yfun τ) := by
    have hfun : (fun τ : ℍ => Work.Residues.Yfun τ)
        = fun τ : ℍ => (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
            - 2 * Work.Kernels.WFun τ ^ 2) * Work.Kernels.E8Fun τ
          - (-(Work.Kernels.UFun τ + Work.Kernels.VFun τ)) * Work.Kernels.E10Fun τ := by
      funext τ
      simp only [Work.Residues.Yfun, Work.Residues.xi4Fun_slash_S_apply,
        Work.Residues.xi2Fun_slash_S_apply]
    rw [hfun]
    exact (hxi4.mul hE8).sub (hxi2.mul hE10)
  have hLS : Continuous (fun τ : ℍ => ℓ.L_S τ) := ℓ.holo_S.continuous
  exact (continuous_const.mul (hE4.pow 3)).add
    ((((continuous_const.mul hj).mul hY).sub ((continuous_const.mul hxi4).mul hE8)).mul hLS)

end Work.CKFinal.LineDecay
