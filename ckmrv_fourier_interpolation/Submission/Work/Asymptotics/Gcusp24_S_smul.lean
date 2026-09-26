/-
# The Fricke (`S`) transformation laws of the leading cusp coefficients `G_{1,0}`, `G_{1,1}`

The two `e^{2πi z}`-coefficient functions `G_{1,0}`, `G_{1,1}` of the cusp-`i∞` expansion of the
CKMRV kernel (`Work.Asymptotics.Gcusp24`) are *quasi*-modular of mixed weight: under the Fricke
involution `S : τ ↦ -1/τ` one has

* `G_{1,0}(S•τ) = τ¹²·(−G_{1,0}(τ) + W₃(τ) + (cuspL ℓ − 1)Δ(τ)/π)`,  and
* `G_{1,1}(S•τ) = −τ¹²·(G_{1,1}(τ) − iΔ(τ))`,

where `W₃ = (ψ₂E₁₀ − ψ₄E₈)/(1152π)`.  The weights `E₁₄, E₁₀, E₄³, Δ` (weights `14, 10, 12, 12`)
and `ψ₂, ψ₄` (`ψ₂|₂S = ψ₂`, `ψ₄|₄S = ψ₄`) transform with the factor `τ¹²`, while
`φ_{-2}(S•τ) = −τ⁻¹`, `φ_0(S•τ) = −φ_0(τ)`, `φ_2(S•τ) = −τ²φ_2(τ)`; the four `φ`-terms of
`G_{1,0}` therefore all pick up `−τ¹²`, which is the extra `−` in the first law.

These are the `S`-analogues of the `T`-affine laws `Work.Asymptotics.Gcusp24_vadd_int`, and they
are what turns the strip bounds at the cusp `i∞` into bounds at the cusp `0`.
-/
import Mathlib
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Kernels.PhiAnnihilation
import Submission.Work.Kernels.KernelFacts.KPlusCoeff_slash_S
import Submission.Work.Kernels.KernelFacts.psi2_Sopm
import Submission.Work.Kernels.KernelFacts.psi4_Sopm
import Submission.Work.Kernels.E2Laws

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

noncomputable section

/-- The explicit `(i,j) = (1,0)` branch of `Work.Asymptotics.Gcusp24`, written in terms of the
atoms. -/
noncomputable def G10exp (ℓ : Work.Kernels.LogLambdaData) (σ : UpperHalfPlane) : ℂ :=
  ( -(Complex.I / 288) * (Work.Kernels.phiVec σ 0 * (Work.Kernels.E4Fun σ ^ 2 * Work.Kernels.E6Fun σ)
        + Work.Kernels.phiVec σ 2 * (Work.Kernels.E4Fun σ * Work.Kernels.E6Fun σ))
    + (Complex.I / 144) * (Work.Kernels.phiVec σ 1 * Work.Kernels.E4Fun σ ^ 3)
    - 7 * Complex.I * (Work.Kernels.phiVec σ 1 * Work.Kernels.DeltaFun σ)
    + Work.Kernels.DeltaFun σ * (cuspL ℓ - 1) / (Real.pi : ℂ)
    + (Work.Kernels.psi2 ℓ σ * (Work.Kernels.E4Fun σ * Work.Kernels.E6Fun σ)
        - Work.Kernels.psi4 ℓ σ * (Work.Kernels.E4Fun σ ^ 2)) / (1152 * (Real.pi : ℂ)) ) / 2

lemma Gcusp24_10_eq_exp (ℓ : Work.Kernels.LogLambdaData) (σ : UpperHalfPlane) :
    Gcusp24 ℓ 1 0 σ = G10exp ℓ σ := rfl

/-- The explicit `(i,j) = (1,1)` branch of `Work.Asymptotics.Gcusp24`, written in terms of the
atoms. -/
noncomputable def G11exp (σ : UpperHalfPlane) : ℂ :=
  ((Real.pi : ℂ) / 864 * (Work.Kernels.phiVec σ 0 * (Work.Kernels.E4Fun σ ^ 2 * Work.Kernels.E6Fun σ)
      + Work.Kernels.phiVec σ 2 * (Work.Kernels.E4Fun σ * Work.Kernels.E6Fun σ)
      + 1728 * (Work.Kernels.phiVec σ 1 * Work.Kernels.DeltaFun σ)
      - 2 * (Work.Kernels.phiVec σ 1 * Work.Kernels.E4Fun σ ^ 3))
    + Complex.I * Work.Kernels.DeltaFun σ) / 2

lemma Gcusp24_11_eq_exp (ℓ : Work.Kernels.LogLambdaData) (σ : UpperHalfPlane) :
    Gcusp24 ℓ 1 1 σ = G11exp σ := rfl

/-! ## The pointwise `S`-transformation laws -/

private lemma phiVec_S_zero (τ : ℍ) : Work.Kernels.phiVec (ModularGroup.S • τ) 0 = -((τ:ℂ))⁻¹ := by
  rw [show Work.Kernels.phiVec (ModularGroup.S • τ) 0 = Work.Kernels.phiNeg2 (ModularGroup.S • τ)
      from by simp [Work.Kernels.phiVec], Work.Kernels.phiNeg2_S_smul]

private lemma phiVec_S_one (τ : ℍ) : Work.Kernels.phiVec (ModularGroup.S • τ) 1
    = - Work.Kernels.phi0 τ := by
  rw [show Work.Kernels.phiVec (ModularGroup.S • τ) 1 = Work.Kernels.phi0 (ModularGroup.S • τ)
      from by simp [Work.Kernels.phiVec], Work.Kernels.phi0_S_smul]

private lemma phiVec_S_two (τ : ℍ) : Work.Kernels.phiVec (ModularGroup.S • τ) 2
    = (τ:ℂ)^2 * (- Work.Kernels.phi2 τ) := by
  rw [show Work.Kernels.phiVec (ModularGroup.S • τ) 2 = Work.Kernels.phi2 (ModularGroup.S • τ)
      from by simp [Work.Kernels.phiVec], Work.Kernels.phi2_S_smul]

private lemma phiVec_zero (τ : ℍ) : Work.Kernels.phiVec τ 0 = (τ : ℂ) := by
  simp [Work.Kernels.phiVec, Work.Kernels.phiNeg2]

private lemma phiVec_one (τ : ℍ) : Work.Kernels.phiVec τ 1 = Work.Kernels.phi0 τ := by
  simp [Work.Kernels.phiVec]

private lemma phiVec_two (τ : ℍ) : Work.Kernels.phiVec τ 2 = Work.Kernels.phi2 τ := by
  simp [Work.Kernels.phiVec]

private lemma E4Fun_S_smul' (τ : ℍ) : Work.Kernels.E4Fun (ModularGroup.S • τ)
    = (τ:ℂ)^4 * Work.Kernels.E4Fun τ :=
  Work.Kernels.KernelFacts.kpc_smul_S_of_slash Work.Kernels.KernelFacts.kpc_E4_slash_S τ

private lemma E6Fun_S_smul' (τ : ℍ) : Work.Kernels.E6Fun (ModularGroup.S • τ)
    = (τ:ℂ)^6 * Work.Kernels.E6Fun τ :=
  Work.Kernels.KernelFacts.kpc_smul_S_of_slash Work.Kernels.KernelFacts.kpc_E6_slash_S τ

private lemma DeltaFun_S_smul' (τ : ℍ) : Work.Kernels.DeltaFun (ModularGroup.S • τ)
    = (τ:ℂ)^12 * Work.Kernels.DeltaFun τ :=
  Work.Kernels.KernelFacts.kpc_smul_S_of_slash Work.Kernels.KernelFacts.kpc_Delta_slash_S τ

private lemma psi2_S_smul' (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Kernels.psi2 ℓ (ModularGroup.S • τ) = (τ:ℂ)^2 * Work.Kernels.psi2 ℓ τ :=
  Work.Kernels.KernelFacts.smul_of_sopm (Work.Kernels.KernelFacts.psi2_Sopm ℓ) τ

private lemma psi4_S_smul' (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Kernels.psi4 ℓ (ModularGroup.S • τ) = (τ:ℂ)^4 * Work.Kernels.psi4 ℓ τ :=
  Work.Kernels.KernelFacts.smul_of_sopm (Work.Kernels.KernelFacts.psi4_Sopm ℓ) τ

/-- **The Fricke law of `G_{1,0}`.** -/
theorem Gcusp24_10_S_smul (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    Gcusp24 ℓ 1 0 (ModularGroup.S • τ)
      = (τ : ℂ) ^ 12 * (-(Gcusp24 ℓ 1 0 τ)
          + (Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ
              - Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ) / (1152 * (Real.pi : ℂ))
          + (cuspL ℓ - 1) * Work.Kernels.DeltaFun τ / (Real.pi : ℂ)) := by
  have h1 : (τ : ℂ) ≠ 0 := fun h => τ.im_ne_zero (by rw [← UpperHalfPlane.coe_im τ, h]; simp)
  rw [show Gcusp24 ℓ 1 0 (ModularGroup.S • τ) = G10exp ℓ (ModularGroup.S • τ) from rfl,
      show Gcusp24 ℓ 1 0 τ = G10exp ℓ τ from rfl]
  simp only [G10exp, phiVec_S_zero τ, phiVec_S_one τ, phiVec_S_two τ,
    phiVec_zero τ, phiVec_one τ, phiVec_two τ, psi2_S_smul' ℓ τ, psi4_S_smul' ℓ τ,
    E4Fun_S_smul' τ, E6Fun_S_smul' τ, DeltaFun_S_smul' τ,
    Work.Kernels.E8Fun, Work.Kernels.E10Fun]
  field_simp
  ring

/-- **The Fricke law of `G_{1,1}`.** -/
theorem Gcusp24_11_S_smul (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    Gcusp24 ℓ 1 1 (ModularGroup.S • τ)
      = -((τ : ℂ) ^ 12) * (Gcusp24 ℓ 1 1 τ - Complex.I * Work.Kernels.DeltaFun τ) := by
  have h1 : (τ : ℂ) ≠ 0 := fun h => τ.im_ne_zero (by rw [← UpperHalfPlane.coe_im τ, h]; simp)
  have hL : ∀ σ : UpperHalfPlane, Gcusp24 ℓ 1 1 σ = G11exp σ :=
    fun σ => Gcusp24_11_eq_exp ℓ σ
  rw [hL (ModularGroup.S • τ), hL τ]
  simp only [G11exp, phiVec_S_zero τ, phiVec_S_one τ, phiVec_S_two τ,
    phiVec_zero τ, phiVec_one τ, phiVec_two τ,
    E4Fun_S_smul' τ, E6Fun_S_smul' τ, DeltaFun_S_smul' τ]
  field_simp
  ring

end

end Work.Asymptotics
