import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Modular.modularForm_of_slash_invariant
import Submission.Work.Modular.ThetaFuncs
import Submission.Work.Modular.theta2_at_cusp
import Submission.Work.Modular.E4_qExpansion_coeff
import Submission.Work.Modular.theta2_S_smul
import Submission.Work.Modular.theta4_S_smul

/-!
# Jacobi's quartic identity `θ₃⁴ = θ₄⁴ + θ₂⁴`

This file proves the classical quartic theta identity, in the normalisation of
`Submission.Work.Modular.ThetaFuncs` (`θ₃ = ∑ q^{n²/2}` with `q = e^{2πiτ}`, so that
`U = θ₃⁴`, `W = θ₄⁴`, `V = θ₂⁴`):

  `θ₃⁴ = θ₄⁴ + θ₂⁴`,  i.e.  `UFun = WFun + VFun`.

## Strategy

Let `G = θ₃⁴ - θ₄⁴ - θ₂⁴` and `H = G²`.  The individual theta functions satisfy

* `θ₃(T•τ) = θ₄ τ`, `θ₄(T•τ) = θ₃ τ`, `θ₂(T•τ) = e^{iπ/4} θ₂ τ`,
* `θ₃(S•τ) = (-iτ)^{1/2} θ₃ τ`, `θ₄(S•τ) = (-iτ)^{1/2} θ₂ τ`,
  `θ₂(S•τ) = (-iτ)^{1/2} θ₄ τ`   (Jacobi's imaginary transformation),

so `G(T•τ) = -G(τ)` and `G(S•τ) = -τ² G(τ)`.  Hence `H = G²` is slash-invariant of
weight `4` for `SL(2, ℤ)`: `H(T•τ) = H(τ)` and `H(S•τ) = τ⁴ H(τ)`.  Also `H` is
holomorphic, and `H → 0` at the cusp `i∞` (since `G → 1 - 1 - 0 = 0`).

Thus `H` is a level-one modular form of weight `4` whose constant term vanishes.  As
`dim M₄ = 1` (`ModularForm.levelOne_weight_four_rank_one`) and the constant term of
`E₄` is `1`, such a form must vanish identically: `H = 0`.  Since `ℂ` is a domain,
`G = 0`, which is the identity.
-/

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Real Topology
open Filter Work.Modular

namespace Work.Kernels.TildeFacts

/-- The difference `G = θ₃⁴ - θ₄⁴ - θ₂⁴` of Jacobi's quartic identity. -/
private abbrev quarticG : ℍ → ℂ := fun τ => theta3 τ ^ 4 - theta4 τ ^ 4 - theta2 τ ^ 4

/-- `G²`, which is a level-one modular form of weight `4`. -/
private abbrev quarticH : ℍ → ℂ := fun τ => quarticG τ ^ 2

/-! ## The transformation laws of `G` and `H` -/

private lemma exp_pi_I_div_four_pow_four :
    (Complex.exp (Real.pi * Complex.I / 4)) ^ 4 = -1 := by
  rw [← Complex.exp_nat_mul]
  rw [show (4 : ℕ) * (Real.pi * Complex.I / 4) = Real.pi * Complex.I by ring]
  exact Complex.exp_pi_mul_I

/-- `G` changes sign under `T : τ ↦ τ + 1`. -/
private lemma quarticG_T_smul (τ : ℍ) : quarticG (ModularGroup.T • τ) = -quarticG τ := by
  simp only [quarticG, theta3_T_smul, theta4_T_smul, theta2_T_smul, mul_pow,
    exp_pi_I_div_four_pow_four]
  ring

/-- The square of the automorphy factor `(-iτ)^{1/2}` is `-τ²`. -/
private lemma auFactor_pow_four (τ : ℍ) :
    ((-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ 4 = -(τ : ℂ) ^ 2 := by
  have h4 : (((4 : ℕ) : ℂ) * (1 / 2)) = ((2 : ℕ) : ℂ) := by norm_num
  rw [← Complex.cpow_nat_mul, h4, Complex.cpow_natCast]
  rw [mul_pow, show (-Complex.I : ℂ) ^ 2 = -1 by
    rw [show (-Complex.I : ℂ) = (-1 : ℂ) * Complex.I by ring, mul_pow, Complex.I_sq,
      show ((-1 : ℂ)) ^ 2 = 1 by norm_num, one_mul]]
  ring

/-- `G` changes sign and picks up the weight-two automorphy factor under `S : τ ↦ -1/τ`. -/
private lemma quarticG_S_smul (τ : ℍ) :
    quarticG (ModularGroup.S • τ) = -(τ : ℂ) ^ 2 * quarticG τ := by
  simp only [quarticG, theta3_S_smul, theta4_S_smul, theta2_S_smul, mul_pow,
    auFactor_pow_four τ]
  ring

private lemma quarticH_T_smul (τ : ℍ) : quarticH (ModularGroup.T • τ) = quarticH τ := by
  simp only [quarticH, quarticG_T_smul τ]
  ring

private lemma quarticH_S_smul (τ : ℍ) :
    quarticH (ModularGroup.S • τ) = (τ : ℂ) ^ 4 * quarticH τ := by
  simp only [quarticH, quarticG_S_smul τ]
  ring

/-- `H` is invariant under the slash action of `T` of weight `4`. -/
private lemma quarticH_slash_T : quarticH ∣[(4 : ℤ)] ModularGroup.T = quarticH := by
  funext z
  rw [ModularForm.slash_action_eq'_iff, quarticH_T_smul z]
  have h10 : ((ModularGroup.T : SL(2, ℤ)) 1 0 : ℂ) = 0 := by simp [ModularGroup.coe_T]
  have h11 : ((ModularGroup.T : SL(2, ℤ)) 1 1 : ℂ) = 1 := by simp [ModularGroup.coe_T]
  rw [h10, h11]
  simp

/-- `H` is invariant under the slash action of `S` of weight `4`. -/
private lemma quarticH_slash_S : quarticH ∣[(4 : ℤ)] ModularGroup.S = quarticH := by
  funext z
  rw [ModularForm.slash_action_eq'_iff, quarticH_S_smul z]
  have h10 : ((ModularGroup.S : SL(2, ℤ)) 1 0 : ℂ) = 1 := by simp [ModularGroup.coe_S]
  have h11 : ((ModularGroup.S : SL(2, ℤ)) 1 1 : ℂ) = 0 := by simp [ModularGroup.coe_S]
  rw [h10, h11]
  simp

/-- `H` is invariant under the slash action of all of `SL(2, ℤ)` of weight `4`. -/
private lemma quarticH_per : ∀ γ : SL(2, ℤ), quarticH ∣[(4 : ℤ)] γ = quarticH :=
  SlashInvariantForm.slash_action_generators_SL2Z quarticH_slash_S quarticH_slash_T

/-! ## Holomorphy, and vanishing at the cusp -/

private lemma mdifferentiable_quarticH : MDiff quarticH := by
  have hG : MDiff quarticG := by
    have h3 : MDiff (fun τ : ℍ => theta3 τ ^ 4) := mdifferentiable_theta3.pow 4
    have h4 : MDiff (fun τ : ℍ => theta4 τ ^ 4) := mdifferentiable_theta4.pow 4
    have h2 : MDiff (fun τ : ℍ => theta2 τ ^ 4) := mdifferentiable_theta2.pow 4
    have h : MDiff (fun τ : ℍ => theta3 τ ^ 4 - theta4 τ ^ 4 - theta2 τ ^ 4) :=
      (h3.sub h4).sub h2
    exact h
  exact hG.pow 2

private lemma tendsto_quarticH : Tendsto quarticH atImInfty (nhds 0) := by
  have hG : Tendsto quarticG atImInfty (nhds 0) := by
    have h3 : Tendsto (fun τ : ℍ => theta3 τ ^ 4) atImInfty (nhds ((1 : ℂ) ^ 4)) :=
      tendsto_theta3_atImInfty.pow 4
    have h4 : Tendsto (fun τ : ℍ => theta4 τ ^ 4) atImInfty (nhds ((1 : ℂ) ^ 4)) :=
      tendsto_theta4_atImInfty.pow 4
    have h2 : Tendsto (fun τ : ℍ => theta2 τ ^ 4) atImInfty (nhds ((0 : ℂ) ^ 4)) :=
      theta2_at_cusp.pow 4
    have h : Tendsto (fun τ : ℍ => theta3 τ ^ 4 - theta4 τ ^ 4 - theta2 τ ^ 4)
        atImInfty (nhds ((1 : ℂ) ^ 4 - (1 : ℂ) ^ 4 - (0 : ℂ) ^ 4)) :=
      (h3.sub h4).sub h2
    have h0 : Tendsto (fun τ : ℍ => theta3 τ ^ 4 - theta4 τ ^ 4 - theta2 τ ^ 4)
        atImInfty (nhds 0) := by
      simpa using h
    exact h0
  have h : Tendsto (fun τ : ℍ => quarticG τ ^ 2) atImInfty (nhds 0) := by
    simpa using hG.pow 2
  exact h

private lemma isBoundedAtImInfty_quarticH : IsBoundedAtImInfty quarticH := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  have hnorm : Tendsto (fun z : ℍ => ‖quarticH z‖) atImInfty (nhds 0) := by
    simpa using tendsto_quarticH.norm
  have h1 : {z : ℍ | ‖quarticH z‖ ≤ 1} ∈ atImInfty := by
    have hmem : Set.Iic (1 : ℝ) ∈ nhds (0 : ℝ) :=
      eventually_le_nhds (show (0 : ℝ) < 1 by norm_num)
    filter_upwards [hnorm.eventually hmem] with z hz
    simpa using hz
  rw [UpperHalfPlane.atImInfty_mem] at h1
  obtain ⟨A, hA⟩ := h1
  exact ⟨1, A, fun z hz => hA z hz⟩

/-! ## The main theorem -/

theorem theta_quartic (z : UpperHalfPlane) :
    Work.Kernels.UFun z = Work.Kernels.WFun z + Work.Kernels.VFun z := by
  -- `H = G²` is a level-one modular form of weight four vanishing at the cusp, hence `0`.
  have hH : quarticH = 0 := by
    obtain ⟨g, hg⟩ := modularForm_of_slash_invariant (k := 4) quarticH_per
      mdifferentiable_quarticH isBoundedAtImInfty_quarticH
    have hbddg : IsBoundedAtImInfty (⇑g : ℍ → ℂ) := by
      rw [hg]; exact isBoundedAtImInfty_quarticH
    have hholg : MDiff (⇑g : ℍ → ℂ) := by rw [hg]; exact mdifferentiable_quarticH
    have hperg : Function.Periodic ((⇑g : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) 1 :=
      SlashInvariantFormClass.periodic_comp_ofComplex (f := g) one_mem_strictPeriods_SL
    have hanal : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (⇑g : ℍ → ℂ)) 0 :=
      UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hperg hholg hbddg
    have hcoeff : (UpperHalfPlane.qExpansion 1 (⇑g : ℍ → ℂ)).coeff 0 = 0 := by
      rw [UpperHalfPlane.qExpansion_coeff_zero one_pos hanal hperg]
      rw [show UpperHalfPlane.valueAtInfty (⇑g : ℍ → ℂ) = 0 by
        rw [UpperHalfPlane.valueAtInfty, hg]
        exact tendsto_quarticH.limUnder_eq]
    have hrank : Module.finrank ℂ (ModularForm 𝒮ℒ 4) = 1 :=
      Module.rank_eq_one_iff_finrank_eq_one.mp ModularForm.levelOne_weight_four_rank_one
    have hE4ne : ModularForm.E₄ ≠ 0 :=
      EisensteinSeries.E_ne_zero (k := 4) (by norm_num) ⟨2, rfl⟩
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ModularForm.E₄ hE4ne).mp hrank g
    have hcoe : (⇑(c • ModularForm.E₄) : ℍ → ℂ) = c • (⇑ModularForm.E₄ : ℍ → ℂ) := rfl
    have hcq : (UpperHalfPlane.qExpansion 1 (c • (⇑ModularForm.E₄ : ℍ → ℂ))).coeff 0 = c := by
      rw [UpperHalfPlane.qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero
        ModularForm.E₄ one_pos one_mem_strictPeriods_SL) c,
        PowerSeries.coeff_smul, E4_qExpansion_coeff 0]
      simp
    have hc0 : c = 0 := by
      have h : (UpperHalfPlane.qExpansion 1 (c • (⇑ModularForm.E₄ : ℍ → ℂ))).coeff 0 = 0 := by
        rw [← hcoe, hc]
        exact hcoeff
      rwa [hcq] at h
    have hg0 : g = 0 := by rw [← hc, hc0, zero_smul]
    funext τ
    have h1 : (⇑g : ℍ → ℂ) τ = quarticH τ := congr_fun hg τ
    rw [← h1, hg0]
    simp
  -- Hence `G = 0`, which is the identity.
  have hz : quarticG z = 0 := by
    have h := congr_fun hH z
    simp only [quarticH, Pi.zero_apply] at h
    exact sq_eq_zero_iff.mp h
  simp only [quarticG] at hz
  have hmain : theta3 z ^ 4 = theta4 z ^ 4 + theta2 z ^ 4 := by
    linear_combination hz
  simpa only [Work.Kernels.UFun, Work.Kernels.WFun, Work.Kernels.VFun, Work.Kernels.theta00Fun,
    Work.Kernels.theta01Fun, Work.Kernels.theta10Fun, Work.Modular.theta3, Work.Modular.theta4,
    Work.Modular.theta2] using hmain

end Work.Kernels.TildeFacts
