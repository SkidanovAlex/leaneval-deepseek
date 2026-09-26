import Mathlib
import Submission.Work.Asymptotics.ERegDefs

/-!
# The two cusp identities behind the CKMRV `E`-order cancellation

Writing `U = θ₀₀⁴`, `V = θ₁₀⁴`, `W = θ₀₁⁴` (so that `U = V + W`) and
`ξ₂ = U + W`, `ξ₄ = U² + W² - 2V²`, the classical theta expressions
`E₄ = (U²+V²+W²)/2`, `E₆ = -U³ + (3/2)U²W + (3/2)UW² - W³`
(`Work.Residues.KMinusT_E4Fun_eq_theta`, `..._E6Fun_eq_theta`) give the *exact* factorisations

  `ξ₂E₆ - ξ₄E₄ = -(9/2) U V² W`,   `(ξ₂|₂S)E₆ - (ξ₄|₄S)E₄ = -(9/2) U V W²`,

and hence `X = ξ₄E₈ - ξ₂E₁₀ = (9/2) U V² W E₄`, `Y = (ξ₄|₄S)E₈ - (ξ₂|₂S)E₁₀ = (9/2) U V W² E₄`.

These factorisations are what makes the combination `ψ₄E₈ - ψ₂E₁₀ = 𝓛X + 𝓛_S Y` vanish at the
cusp `0` to the order needed for the `E`-region estimate.
-/

noncomputable section

open UpperHalfPlane ModularGroup

namespace Work.Asymptotics

theorem EReg_identities (τ : UpperHalfPlane) :
    (Work.Kernels.xi2Fun τ * Work.Kernels.E6Fun τ - Work.Kernels.xi4Fun τ * Work.Kernels.E4Fun τ
        = -(9 / 2 : ℂ) * (Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2 * Work.Kernels.WFun τ))
  ∧ ((SlashAction.map (2 : ℤ) ModularGroup.S Work.Kernels.xi2Fun) τ * Work.Kernels.E6Fun τ
        - (SlashAction.map (4 : ℤ) ModularGroup.S Work.Kernels.xi4Fun) τ * Work.Kernels.E4Fun τ
        = -(9 / 2 : ℂ) * (Work.Kernels.UFun τ * Work.Kernels.VFun τ * Work.Kernels.WFun τ ^ 2))
  ∧ (Work.Residues.Xfun τ
        = (9 / 2 : ℂ) * (Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2 * Work.Kernels.WFun τ
            * Work.Kernels.E4Fun τ))
  ∧ (Work.Residues.Yfun τ
        = (9 / 2 : ℂ) * (Work.Kernels.UFun τ * Work.Kernels.VFun τ * Work.Kernels.WFun τ ^ 2
            * Work.Kernels.E4Fun τ)) := by
  have hd1 : Work.Kernels.xi2Fun τ * Work.Kernels.E6Fun τ - Work.Kernels.xi4Fun τ * Work.Kernels.E4Fun τ
      = -(9 / 2 : ℂ) * (Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2 * Work.Kernels.WFun τ) := by
    rw [show Work.Kernels.xi2Fun τ = Work.Kernels.UFun τ + Work.Kernels.WFun τ from rfl,
      show Work.Kernels.xi4Fun τ = Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2
        - 2 * Work.Kernels.VFun τ ^ 2 from rfl]
    rw [Work.Residues.KMinusT_E4Fun_eq_theta τ, Work.Residues.KMinusT_E6Fun_eq_theta τ,
      Work.Kernels.TildeFacts.theta_quartic τ]
    ring
  have hd2 : (SlashAction.map (2 : ℤ) ModularGroup.S Work.Kernels.xi2Fun) τ * Work.Kernels.E6Fun τ
      - (SlashAction.map (4 : ℤ) ModularGroup.S Work.Kernels.xi4Fun) τ * Work.Kernels.E4Fun τ
      = -(9 / 2 : ℂ) * (Work.Kernels.UFun τ * Work.Kernels.VFun τ * Work.Kernels.WFun τ ^ 2) := by
    rw [Work.Kernels.KernelFacts.xi2Fun_slash_S τ, Work.Kernels.KernelFacts.xi4S_apply τ]
    rw [Work.Residues.KMinusT_E4Fun_eq_theta τ, Work.Residues.KMinusT_E6Fun_eq_theta τ,
      Work.Kernels.TildeFacts.theta_quartic τ]
    ring
  refine ⟨hd1, hd2, ?_, ?_⟩
  · rw [show Work.Residues.Xfun τ = Work.Kernels.xi4Fun τ * Work.Kernels.E8Fun τ
        - Work.Kernels.xi2Fun τ * Work.Kernels.E10Fun τ from rfl]
    rw [show Work.Kernels.xi4Fun τ = Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2
        - 2 * Work.Kernels.VFun τ ^ 2 from rfl,
      show Work.Kernels.xi2Fun τ = Work.Kernels.UFun τ + Work.Kernels.WFun τ from rfl]
    rw [show Work.Kernels.E8Fun τ = Work.Kernels.E4Fun τ ^ 2 from rfl,
      show Work.Kernels.E10Fun τ = Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ from rfl]
    rw [Work.Residues.KMinusT_E4Fun_eq_theta τ, Work.Residues.KMinusT_E6Fun_eq_theta τ,
      Work.Kernels.TildeFacts.theta_quartic τ]
    ring
  · rw [show Work.Residues.Yfun τ
        = (SlashAction.map (4 : ℤ) ModularGroup.S Work.Kernels.xi4Fun) τ * Work.Kernels.E8Fun τ
          - (SlashAction.map (2 : ℤ) ModularGroup.S Work.Kernels.xi2Fun) τ
            * Work.Kernels.E10Fun τ from rfl]
    rw [Work.Kernels.KernelFacts.xi4S_apply τ, Work.Kernels.KernelFacts.xi2Fun_slash_S τ]
    rw [show Work.Kernels.E8Fun τ = Work.Kernels.E4Fun τ ^ 2 from rfl,
      show Work.Kernels.E10Fun τ = Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ from rfl]
    rw [Work.Residues.KMinusT_E4Fun_eq_theta τ, Work.Residues.KMinusT_E6Fun_eq_theta τ,
      Work.Kernels.TildeFacts.theta_quartic τ]
    ring

end Work.Asymptotics
