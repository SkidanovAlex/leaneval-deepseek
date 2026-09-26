import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Modular.ramanujan_E4
import Submission.Work.Modular.ramanujan_E6

/-!
# Ramanujan's differential identity `D Δ = E₂ · Δ`

CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022)) use, in the
residue computation of Theorem 4.9, the classical Ramanujan identity

  `D Δ = E₂ Δ`,   where `D = (2πi)⁻¹ d/dτ` and `Δ = η²⁴`

is the modular discriminant (`Work.Kernels.DeltaFun = ⇑CuspForm.discriminant`) and
`E₂` is the weight-two Eisenstein series (`Work.Kernels.E2Fun = EisensteinSeries.E2`).

The proof is the logarithmic derivative of the eta function: `Δ = η²⁴`, so on `ℍ`

  `d/dτ log Δ = 24 · d/dτ log η = 24 · logDeriv η = 24 · (πi/12) E₂ = 2πi E₂`,

using Mathlib's `ModularForm.logDeriv_eta_eq_E2`.  Multiplying by `Δ` and by the normalizing
constant `(2πi)⁻¹ = 1/(2πi)` gives `D Δ = E₂ Δ`.
-/

noncomputable section

open Filter Topology

namespace Work.Residues

open Work.Kernels

/-- **Ramanujan's identity for the discriminant.**  The normalized derivative
`D = (2πi)⁻¹ d/dτ` of `Δ = η²⁴` is `E₂ · Δ`, where `E₂` is the weight-two Eisenstein series
(Mathlib's `EisensteinSeries.E2`). -/
theorem normalizedDeriv_DeltaFun :
    Derivative.normalizedDerivOfComplex Work.Kernels.DeltaFun
      = fun z => Work.Kernels.E2Fun z * Work.Kernels.DeltaFun z := by
  funext z
  have hzmem : (z : ℂ) ∈ UpperHalfPlane.upperHalfPlaneSet := z.im_pos
  -- Near `z`, `Δ ∘ ofComplex` is `η ^ 24`.
  have hloc : (Work.Kernels.DeltaFun ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (z : ℂ)]
      (fun w : ℂ => ModularForm.eta w ^ 24) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hzmem] with w hw
    simp only [Function.comp_apply]
    simp [Work.Kernels.DeltaFun, ModularForm.discriminant, CuspForm.coe_discriminant,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  have hdiff : DifferentiableAt ℂ ModularForm.eta (z : ℂ) :=
    ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hzmem
  have heta_ne : ModularForm.eta (z : ℂ) ≠ 0 := ModularForm.eta_ne_zero hzmem
  have hDz : Work.Kernels.DeltaFun z = ModularForm.eta (z : ℂ) ^ 24 := by
    simp [Work.Kernels.DeltaFun, ModularForm.discriminant, CuspForm.coe_discriminant]
  -- `η' = logDeriv η · η = (πi/12) E₂ · η`.
  have hderiv_eta : deriv ModularForm.eta (z : ℂ)
      = ((Real.pi : ℂ) * Complex.I / 12) * Work.Kernels.E2Fun z * ModularForm.eta (z : ℂ) := by
    have h := ModularForm.logDeriv_eta_eq_E2 z
    rw [logDeriv_apply, div_eq_iff heta_ne] at h
    exact h
  -- Hence `(η²⁴)' = 24 η²³ η' = 2πi · (E₂ Δ)`.
  have hE : deriv (fun w : ℂ => ModularForm.eta w ^ 24) (z : ℂ)
      = (2 * (Real.pi : ℂ) * Complex.I) * (Work.Kernels.E2Fun z * Work.Kernels.DeltaFun z) := by
    rw [deriv_fun_pow hdiff 24, hderiv_eta, hDz]
    ring
  rw [Derivative.normalizedDerivOfComplex, Filter.EventuallyEq.deriv_eq hloc, hE]
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  rw [← mul_assoc, inv_mul_cancel₀ h2, one_mul]

end Work.Residues
