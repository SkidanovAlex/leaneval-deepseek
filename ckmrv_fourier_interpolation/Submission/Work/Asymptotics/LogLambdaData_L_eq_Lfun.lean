/-
# The `𝓛`-component of any logarithm data is the canonical branch `Lfun`

The pair `(𝓛, 𝓛_S)` of CKMRV (Ann. of Math. 196 (2022), Section 2.1.5) is characterised, as
*data*, by the four transformation laws (2.9) together with `exp 𝓛 = λ`, `exp 𝓛_S = λ_S`.
Here we show that these conditions already pin `𝓛` down: for *every* `ℓ : LogLambdaData` and
every `τ ∈ ℍ`,

  `ℓ.L τ = Lfun (τ : ℂ)`,

where `Lfun` is the normalised branch of `log λ` of `LogExtension`.

## Proof

`ll_sub_Lfun_const` (`Submission.Work.Asymptotics.cusp_L_second`) gives that `ℓ.L` differs from
`Lfun` by a constant `c`: both are continuous logarithms of `λ` on the connected set `ℍ`.  It
remains to show `c = 0`, and this is forced by the `T`-law.  Indeed, at any `τ₀`, the `T`-law for
`ℓ` reads

  `ℓ.L (T τ₀) = ℓ.L τ₀ - ℓ.L_S τ₀ + πi`,

while `ℓ.L_S τ₀ = ℓ.L (S τ₀)` by the `S`-law.  Substituting `ℓ.L = Lfun + c` and using the
`T`-law `Lfun (τ₀+1) = Lfun τ₀ - Lfun (-τ₀⁻¹) + πi` of the explicit branch (proved in `LogLaws`),
together with `T τ₀ = τ₀ + 1` and `S τ₀ = -τ₀⁻¹`, the two constants `c` cancel on the right and
we are left with `Lfun (T τ₀) + c = Lfun (T τ₀)`, i.e. `c = 0`.
-/
import Mathlib
import Submission.Work.Asymptotics.cusp_L_second
import Submission.Work.Kernels.LogLambda.LogLaws

noncomputable section

open UpperHalfPlane ModularGroup

namespace Work.Asymptotics

/-- **The `𝓛`-component of any logarithm data is `Lfun`.** -/
theorem LogLambdaData_L_eq_Lfun (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    ℓ.L τ = Work.Kernels.LogLambda.Lfun (τ : ℂ) := by
  obtain ⟨c, hc⟩ := Work.Asymptotics.ll_sub_Lfun_const ℓ
  -- The constant `c` is zero, forced by the `T`-law at the point `i`.
  have hc0 : c = 0 := by
    set τ₀ : ℍ := ⟨Complex.I, by norm_num⟩ with hτ₀
    -- The `T`-law for `ℓ`, read pointwise at `τ₀`.
    have hT : ℓ.L (ModularGroup.T • τ₀) = ℓ.L τ₀ - ℓ.L_S τ₀ + (Real.pi : ℂ) * Complex.I := by
      have h := ℓ.slash_T τ₀
      rw [ModularForm.SL_slash_apply] at h
      simpa using h
    -- The `S`-law for `ℓ`, read pointwise at `τ₀`.
    have hS : ℓ.L (ModularGroup.S • τ₀) = ℓ.L_S τ₀ := by
      have h := congr_fun ℓ.slash_S τ₀
      rw [ModularForm.SL_slash_apply] at h
      simpa using h
    have hco_T : ((ModularGroup.T • τ₀ : ℍ) : ℂ) = (τ₀ : ℂ) + 1 := by
      rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]; simp; ring
    have hco_S : ((ModularGroup.S • τ₀ : ℍ) : ℂ) = -((τ₀ : ℂ))⁻¹ := by
      rw [UpperHalfPlane.modular_S_smul, neg_inv]
    -- The `T`-law of the explicit branch `Lfun`.
    have hLfun := Work.Kernels.LogLambda.lfun_add_one (τ₀ : ℂ) τ₀.2
    have key : Work.Kernels.LogLambda.Lfun ((ModularGroup.T • τ₀ : ℍ) : ℂ) + c
        = Work.Kernels.LogLambda.Lfun ((ModularGroup.T • τ₀ : ℍ) : ℂ) := by
      rw [← hc (ModularGroup.T • τ₀), hT, ← hS, hc τ₀, hc (ModularGroup.S • τ₀)]
      rw [hco_T, hco_S, hLfun]
      ring
    exact add_eq_left.mp key
  rw [hc τ, hc0, add_zero]

end Work.Asymptotics
