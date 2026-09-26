/-
# `λ` is a local biholomorphism

The modular lambda function `λ = θ₁₀⁴/θ₀₀⁴` is a local biholomorphism at every point of `ℍ`,
i.e. `Work.Rigidity.LambdaLocalInverse` holds.

The proof rests on the classical identity

  `λ'(τ) = π i λ(τ) (1 - λ(τ)) θ₀₀(τ)⁴`,

which is proved by observing that

  `ρ(τ) = λ'(τ) / (λ(τ) (1 - λ(τ)) θ₀₀(τ)⁴)`

is a level-one modular form of weight zero: it is holomorphic on `ℍ` (`differentiableOn_rhoC`),
invariant under the two generators `S`, `T` of `SL(2, ℤ)` (`rhoC_neg_inv`, `rhoC_add_one`) and
bounded at the cusp `i∞` (`isBoundedAtImInfty_rho_of`).  By
`ModularFormClass.levelOne_weight_zero_const` it is therefore constant, say `ρ = c`; and `c ≠ 0`
since otherwise `λ' ≡ 0`, forcing `λ` to be constant, contradicting its transformation laws
`λ(-1/τ) = 1 - λ(τ)` and `λ(τ+1) = λ(τ)/(λ(τ) - 1)`.

Then `λ'(τ) = c λ(τ)(1 - λ(τ))θ₀₀(τ)⁴ ≠ 0` everywhere on `ℍ`, so `λ` has a non-zero strict
derivative at every point, and the analytic inverse function theorem
(`AnalyticAt.analyticAt_localInverse`) produces the required local right inverse.
-/
import Mathlib
import Submission.Work.Rigidity.LambdaDerivDefs
import Submission.Work.Rigidity.LambdaTargets
import Submission.Work.Rigidity.periodic_lambdaFun_ofComplex
import Submission.Work.Rigidity.isBoundedAtImInfty_lambdaFun
import Submission.Work.Rigidity.lamC_neg_inv
import Submission.Work.Rigidity.lamC_add_one
import Submission.Work.Rigidity.lambdaFun_div_qParam_tendsto
import Submission.Work.Rigidity.Flam_div_tendsto
import Submission.Work.Rigidity.differentiableOn_rhoC
import Submission.Work.Rigidity.rhoC_add_one
import Submission.Work.Rigidity.rhoC_neg_inv
import Submission.Work.Rigidity.isBoundedAtImInfty_inv_theta01Fun_pow4
import Submission.Work.Rigidity.isBoundedAtImInfty_deriv_lamC_div_lamC
import Submission.Work.Rigidity.isBoundedAtImInfty_rho_of

noncomputable section

open UpperHalfPlane ModularGroup Matrix Filter Topology Complex
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology UpperHalfPlane

namespace Work.Rigidity

open Work.Kernels Work.Kernels.LogLambda

/-! ## Elementary properties of `λ` on the upper half plane -/

/-- On the upper half plane the extension `lamC` agrees with `lambdaFun`. -/
lemma lamC_coe (τ : ℍ) : lamC (τ : ℂ) = lambdaFun τ :=
  lamC_of_mem τ.im_pos

/-- `1 - λ` does not vanish on the upper half plane. -/
lemma one_sub_lamC_ne_zero (z : ℂ) (hz : 0 < z.im) : 1 - lamC z ≠ 0 := by
  intro h
  have h2 : lamC z = 1 := (sub_eq_zero.mp h).symm
  rw [lamC_of_mem hz] at h2
  exact lambdaFun_ne_one ⟨z, hz⟩ h2

/-- The denominator appearing in `rhoC` is non-zero on the upper half plane. -/
lemma rhoC_denom_ne_zero (z : ℂ) (hz : 0 < z.im) :
    lamC z * (1 - lamC z) * (thetaC00 z) ^ 4 ≠ 0 :=
  mul_ne_zero (mul_ne_zero (lamC_ne_zero hz) (one_sub_lamC_ne_zero z hz))
    (pow_ne_zero 4 (thetaC00_ne_zero hz))

/-! ## `ρ` is a level-one modular form of weight zero -/

/-- `rho` is invariant under `τ ↦ τ + 1`. -/
lemma rho_vadd_one (τ : ℍ) : rho ((1 : ℝ) +ᵥ τ) = rho τ := by
  have h : (((1 : ℝ) +ᵥ τ : ℍ) : ℂ) = (τ : ℂ) + 1 := by
    rw [UpperHalfPlane.coe_vadd]
    push_cast
    ring
  have him : 0 < (τ : ℂ).im := τ.im_pos
  show rhoC _ = rhoC _
  rw [h]
  exact rhoC_add_one _ him

/-- `rho` is invariant under `τ ↦ -1/τ`. -/
lemma rho_S (τ : ℍ) : rho (ModularGroup.S • τ) = rho τ := by
  have h : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / (τ : ℂ) := by
    rw [Work.Kernels.coe_S_smul τ, neg_div, one_div, inv_neg]
  have him : 0 < (τ : ℂ).im := τ.im_pos
  show rhoC _ = rhoC _
  rw [h]
  exact rhoC_neg_inv _ him

/-- `rho` is slash-invariant of weight zero under `T`. -/
lemma rho_slash_T : rho ∣[(0 : ℤ)] ModularGroup.T = rho := by
  funext z
  rw [ModularForm.slash_action_eq'_iff]
  rw [UpperHalfPlane.modular_T_smul z, rho_vadd_one]
  simp [ModularGroup.coe_T]

/-- `rho` is slash-invariant of weight zero under `S`. -/
lemma rho_slash_S : rho ∣[(0 : ℤ)] ModularGroup.S = rho := by
  funext z
  rw [ModularForm.slash_action_eq'_iff]
  rw [rho_S]
  simp [ModularGroup.coe_S]

/-- `rho` is holomorphic on `ℍ`. -/
lemma mdifferentiable_rho : MDiff rho := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine differentiableOn_rhoC.congr ?_
  intro z hz
  show rhoC _ = rhoC z
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

/-! ## `ρ` is constant, and the constant is non-zero -/

/-- The function `ρ` is bounded at the cusp. -/
lemma isBoundedAtImInfty_rho : IsBoundedAtImInfty rho :=
  isBoundedAtImInfty_rho_of
    (isBoundedAtImInfty_deriv_lamC_div_lamC periodic_lambdaFun_ofComplex
      isBoundedAtImInfty_lambdaFun
      (Flam_div_tendsto periodic_lambdaFun_ofComplex lambdaFun_div_qParam_tendsto))
    isBoundedAtImInfty_inv_theta01Fun_pow4

/-- **`ρ` is a level-one modular form of weight zero**, hence constant. -/
theorem exists_rho_const : ∃ c : ℂ, ∀ τ : ℍ, rho τ = c := by
  have hper : ∀ γ : SL(2, ℤ), rho ∣[(0 : ℤ)] γ = rho :=
    SlashInvariantForm.slash_action_generators_SL2Z rho_slash_S rho_slash_T
  obtain ⟨g, hg⟩ := Work.Modular.modularForm_of_slash_invariant (k := 0) hper
    mdifferentiable_rho isBoundedAtImInfty_rho
  obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const g
  exact ⟨c, fun τ => by rw [← hg]; exact congrFun hc τ⟩

/-- The constant value of `ρ` is non-zero: otherwise `λ' ≡ 0`, so `λ` would be constant,
contradicting `λ(-1/τ) = 1 - λ(τ)` and `λ(τ+1) = λ(τ)/(λ(τ) - 1)`. -/
theorem rho_const_ne_zero {c : ℂ} (hc : ∀ τ : ℍ, rho τ = c) : c ≠ 0 := by
  intro h0
  have hderiv0 : ∀ z ∈ U, deriv lamC z = 0 := by
    intro z hz
    have h1 : rhoC z = c := hc ⟨z, hz⟩
    rw [h0, rhoC] at h1
    exact (div_eq_zero_iff.mp h1).resolve_right (rhoC_denom_ne_zero z hz)
  obtain ⟨a, ha⟩ := IsOpen.exists_is_const_of_deriv_eq_zero isOpen_U isPreconnected_U
    differentiableOn_lamC (fun z hz => hderiv0 z hz)
  -- `-1/I = I` and `I + 1` are both in the upper half plane
  have hI : Complex.I ∈ U := by simp [U]
  have hI1 : Complex.I + 1 ∈ U := by
    simp only [U, Set.mem_setOf_eq, Complex.add_im, Complex.I_im]
    norm_num
  have hIeq : -1 / Complex.I = Complex.I := by
    rw [neg_div, one_div, Complex.inv_I, neg_neg]
  have hS : lamC Complex.I = 1 - lamC Complex.I := by
    have h := lamC_neg_inv Complex.I (by simp)
    rwa [hIeq] at h
  have hhalf : lamC Complex.I = 1 / 2 := by linear_combination hS / 2
  have hT := lamC_add_one Complex.I (by simp)
  have hc1 : lamC (Complex.I + 1) = lamC Complex.I := (ha _ hI1).trans (ha _ hI).symm
  rw [hc1, hhalf] at hT
  norm_num at hT

/-! ## The derivative identity and non-vanishing of `λ'` -/

/-- The identity `λ'(z) = c · λ(z) (1 - λ(z)) θ₀₀(z)⁴` for the constant value `c` of `ρ`. -/
theorem deriv_lamC_eq_const {c : ℂ} (hc : ∀ τ : ℍ, rho τ = c) (z : ℂ) (hz : 0 < z.im) :
    deriv lamC z = c * (lamC z * (1 - lamC z) * (thetaC00 z) ^ 4) := by
  have h1 : rhoC z = c := hc ⟨z, hz⟩
  rw [rhoC] at h1
  exact (div_eq_iff (rhoC_denom_ne_zero z hz)).mp h1

/-! ## The local right inverse -/

theorem lambda_local_inverse : Work.Rigidity.LambdaLocalInverse := by
  obtain ⟨c, hc⟩ := exists_rho_const
  have hc0 : c ≠ 0 := rho_const_ne_zero hc
  intro τ₀
  set z₀ : ℂ := (τ₀ : ℂ) with hz₀def
  have hz₀U : 0 < z₀.im := τ₀.im_pos
  have hlam0 : lamC z₀ = lambdaFun τ₀ := by
    rw [hz₀def]
    exact lamC_coe τ₀
  have hne : deriv lamC z₀ ≠ 0 := by
    rw [deriv_lamC_eq_const hc z₀ hz₀U]
    exact mul_ne_zero hc0 (rhoC_denom_ne_zero z₀ hz₀U)
  have hAna : AnalyticAt ℂ lamC z₀ :=
    differentiableOn_lamC.analyticAt (isOpen_U.mem_nhds hz₀U)
  have hstrict : HasStrictDerivAt lamC (deriv lamC z₀) z₀ := hAna.hasStrictDerivAt
  let φ : ℂ → ℂ := HasStrictDerivAt.localInverse lamC (deriv lamC z₀) z₀ hstrict hne
  have hφ0 : φ (lamC z₀) = z₀ := by
    show HasStrictDerivAt.localInverse lamC (deriv lamC z₀) z₀ hstrict hne (lamC z₀) = z₀
    simpa only [HasStrictDerivAt.localInverse] using
      (HasStrictFDerivAt.localInverse_apply_image (hstrict.hasStrictFDerivAt_equiv hne))
  have hφdiff : DifferentiableAt ℂ φ (lamC z₀) := by
    show DifferentiableAt ℂ
      (HasStrictDerivAt.localInverse lamC (deriv lamC z₀) z₀ hstrict hne) (lamC z₀)
    exact (hstrict.to_localInverse hne).hasStrictFDerivAt.differentiableAt
  have hφana : AnalyticAt ℂ φ (lamC z₀) := by
    show AnalyticAt ℂ
      (HasStrictDerivAt.localInverse lamC (deriv lamC z₀) z₀ hstrict hne) (lamC z₀)
    exact hAna.analyticAt_localInverse hne
  have hφright : ∀ᶠ w in 𝓝 (lamC z₀), lamC (φ w) = w := by
    show ∀ᶠ w in 𝓝 (lamC z₀),
      lamC (HasStrictDerivAt.localInverse lamC (deriv lamC z₀) z₀ hstrict hne w) = w
    exact hstrict.eventually_right_inverse hne
  refine ⟨φ, {w : ℂ | DifferentiableAt ℂ φ w}, ?_, ?_, ?_, ?_⟩
  · rw [← hlam0]
    filter_upwards [hφana.eventually_analyticAt] with w hw
    exact hw.differentiableAt
  · exact fun w hw => hw.differentiableWithinAt
  · rw [← hlam0, hφ0, hz₀def]
  · rw [← hlam0]
    have htend : Tendsto (fun w : ℂ => (φ w).im) (𝓝 (lamC z₀)) (𝓝 z₀.im) := by
      have h := (Complex.continuous_im.continuousAt (x := φ (lamC z₀))).tendsto.comp
        hφdiff.continuousAt
      simpa [Function.comp_def, hφ0] using h
    have him : ∀ᶠ w in 𝓝 (lamC z₀), 0 < (φ w).im := by
      have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝 z₀.im := isOpen_Ioi.mem_nhds hz₀U
      filter_upwards [htend.eventually hmem] with w hw
      exact hw
    filter_upwards [him, hφright] with w hwim hwright
    refine ⟨hwim, fun hw => ?_⟩
    rw [← lamC_of_mem hw, hwright]

end Work.Rigidity
