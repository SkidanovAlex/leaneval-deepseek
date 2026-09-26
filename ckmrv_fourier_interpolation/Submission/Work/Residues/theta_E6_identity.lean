import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.TildeFacts.theta_quartic
import Submission.Work.Modular.thetaSeries_E8_eq_E4
import Submission.Work.Modular.E6_qExpansion_coeff
import Submission.Work.Modular.ThetaFuncs
import Submission.Work.Modular.theta2_S_smul
import Submission.Work.Modular.theta4_S_smul
import Submission.Work.Modular.theta2_at_cusp
import Submission.Work.Modular.modularForm_of_slash_invariant

/-!
# The weight-six Eisenstein series in terms of the Jacobi theta quartics

We prove CKMRV's identity `E₆ = -U³ + (3/2)U²W + (3/2)UW² - W³`, where
`U = θ₀₀⁴ = θ₃⁴` and `W = θ₀₁⁴ = θ₄⁴` (so that `V = θ₁₀⁴ = θ₂⁴` and `U = W + V`).

The proof follows the template of `thetaSeries_E8_eq_E4`: the right-hand side is a
holomorphic function on `ℍ`, invariant under the slash action of `SL(2, ℤ)` of weight `6`
(hence, being bounded at the cusp, is the underlying function of a level-one modular form
`g` of weight `6`), and its value at the cusp `i∞` is `1`.  Since `dim M₆ = 1` and `E₆` has
the same constant term, `g = E₆`.
-/

namespace Work.Residues

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm Manifold Bundle
open Filter

noncomputable section

/-- The candidate weight-six modular form `-U³ + (3/2)U²W + (3/2)UW² - W³`. -/
def R6 : UpperHalfPlane → ℂ := fun τ =>
  - (Work.Kernels.UFun τ ^ 3)
    + (3 : ℂ) / 2 * (Work.Kernels.UFun τ ^ 2 * Work.Kernels.WFun τ)
    + (3 : ℂ) / 2 * (Work.Kernels.UFun τ * Work.Kernels.WFun τ ^ 2)
    - Work.Kernels.WFun τ ^ 3

/-! ## Rewriting the theta quartics -/

private lemma UFun_eq_theta3 (τ : UpperHalfPlane) :
    Work.Kernels.UFun τ = Work.Modular.theta3 τ ^ 4 := rfl

private lemma WFun_eq_theta4 (τ : UpperHalfPlane) :
    Work.Kernels.WFun τ = Work.Modular.theta4 τ ^ 4 := rfl

private lemma VFun_eq_theta2 (τ : UpperHalfPlane) :
    Work.Kernels.VFun τ = Work.Modular.theta2 τ ^ 4 := rfl

/-- The square of the automorphy factor `(-iτ)^{1/2}` raised to the fourth power is `-τ²`. -/
private lemma auFactor_pow_four (τ : UpperHalfPlane) :
    ((-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ 4 = -((τ : ℂ) ^ 2) := by
  have h4 : (((4 : ℕ) : ℂ) * (1 / 2)) = ((2 : ℕ) : ℂ) := by norm_num
  rw [← Complex.cpow_nat_mul, h4, Complex.cpow_natCast]
  rw [mul_pow, show (-Complex.I : ℂ) ^ 2 = -1 by
    rw [show (-Complex.I : ℂ) = (-1 : ℂ) * Complex.I by ring, mul_pow, Complex.I_sq,
      show ((-1 : ℂ)) ^ 2 = 1 by norm_num, one_mul]]
  ring

/-! ## Transformation laws of `R6` -/

private lemma UFun_T (τ : UpperHalfPlane) :
    Work.Kernels.UFun (ModularGroup.T • τ) = Work.Kernels.WFun τ := by
  rw [UFun_eq_theta3, Work.Modular.theta3_T_smul, ← WFun_eq_theta4]

private lemma WFun_T (τ : UpperHalfPlane) :
    Work.Kernels.WFun (ModularGroup.T • τ) = Work.Kernels.UFun τ := by
  rw [WFun_eq_theta4, Work.Modular.theta4_T_smul, ← UFun_eq_theta3]

private lemma R6_T_smul (τ : UpperHalfPlane) : R6 (ModularGroup.T • τ) = R6 τ := by
  unfold R6
  rw [UFun_T τ, WFun_T τ]
  ring

private lemma UFun_S (τ : UpperHalfPlane) :
    Work.Kernels.UFun (ModularGroup.S • τ) = -((τ : ℂ) ^ 2) * Work.Kernels.UFun τ := by
  rw [UFun_eq_theta3, Work.Modular.theta3_S_smul, mul_pow, auFactor_pow_four τ,
    ← UFun_eq_theta3]

private lemma WFun_S (τ : UpperHalfPlane) :
    Work.Kernels.WFun (ModularGroup.S • τ) = -((τ : ℂ) ^ 2) * Work.Kernels.VFun τ := by
  rw [WFun_eq_theta4, Work.Modular.theta4_S_smul, mul_pow, auFactor_pow_four τ,
    ← VFun_eq_theta2]

private lemma VFun_S (τ : UpperHalfPlane) :
    Work.Kernels.VFun (ModularGroup.S • τ) = -((τ : ℂ) ^ 2) * Work.Kernels.WFun τ := by
  rw [VFun_eq_theta2, Work.Modular.theta2_S_smul, mul_pow, auFactor_pow_four τ,
    ← WFun_eq_theta4]

private lemma R6_S_smul (τ : UpperHalfPlane) :
    R6 (ModularGroup.S • τ) = (τ : ℂ) ^ 6 * R6 τ := by
  have hV : Work.Kernels.VFun τ = Work.Kernels.UFun τ - Work.Kernels.WFun τ := by
    rw [Work.Kernels.TildeFacts.theta_quartic τ]; ring
  unfold R6
  rw [UFun_S τ, WFun_S τ, hV]
  ring

/-! ## `R6` is a holomorphic level-one modular form of weight `6` -/

private lemma R6_slash_T : R6 ∣[(6 : ℤ)] ModularGroup.T = R6 := by
  funext z
  rw [ModularForm.slash_action_eq'_iff, R6_T_smul z]
  have h10 : ((ModularGroup.T : SL(2, ℤ)) 1 0 : ℂ) = 0 := by simp [ModularGroup.coe_T]
  have h11 : ((ModularGroup.T : SL(2, ℤ)) 1 1 : ℂ) = 1 := by simp [ModularGroup.coe_T]
  rw [h10, h11]
  simp

private lemma R6_slash_S : R6 ∣[(6 : ℤ)] ModularGroup.S = R6 := by
  funext z
  rw [ModularForm.slash_action_eq'_iff, R6_S_smul z]
  have h10 : ((ModularGroup.S : SL(2, ℤ)) 1 0 : ℂ) = 1 := by simp [ModularGroup.coe_S]
  have h11 : ((ModularGroup.S : SL(2, ℤ)) 1 1 : ℂ) = 0 := by simp [ModularGroup.coe_S]
  rw [h10, h11]
  simp

private lemma R6_per : ∀ γ : SL(2, ℤ), R6 ∣[(6 : ℤ)] γ = R6 :=
  SlashInvariantForm.slash_action_generators_SL2Z R6_slash_S R6_slash_T

private lemma mdifferentiable_R6 : MDiff R6 := by
  have hU : MDiff (fun τ : UpperHalfPlane => Work.Kernels.UFun τ) := by
    have h : MDiff (fun τ : UpperHalfPlane => Work.Modular.theta3 τ ^ 4) :=
      Work.Modular.mdifferentiable_theta3.pow 4
    simpa only [UFun_eq_theta3] using h
  have hW : MDiff (fun τ : UpperHalfPlane => Work.Kernels.WFun τ) := by
    have h : MDiff (fun τ : UpperHalfPlane => Work.Modular.theta4 τ ^ 4) :=
      Work.Modular.mdifferentiable_theta4.pow 4
    simpa only [WFun_eq_theta4] using h
  have h1 : MDiff (fun τ : UpperHalfPlane => Work.Kernels.UFun τ ^ 3) := hU.pow 3
  have h2 : MDiff (fun τ : UpperHalfPlane =>
      Work.Kernels.UFun τ ^ 2 * Work.Kernels.WFun τ) := (hU.pow 2).mul hW
  have h3 : MDiff (fun τ : UpperHalfPlane =>
      Work.Kernels.UFun τ * Work.Kernels.WFun τ ^ 2) := hU.mul (hW.pow 2)
  have h4 : MDiff (fun τ : UpperHalfPlane => Work.Kernels.WFun τ ^ 3) := hW.pow 3
  have h2c : MDiff (fun τ : UpperHalfPlane =>
      ((3 : ℂ) / 2 * (Work.Kernels.UFun τ ^ 2 * Work.Kernels.WFun τ) : ℂ)) :=
    MDifferentiable.const_smul ((3 : ℂ) / 2) h2
  have h3c : MDiff (fun τ : UpperHalfPlane =>
      ((3 : ℂ) / 2 * (Work.Kernels.UFun τ * Work.Kernels.WFun τ ^ 2) : ℂ)) :=
    MDifferentiable.const_smul ((3 : ℂ) / 2) h3
  unfold R6
  exact ((h1.neg.add h2c).add h3c).sub h4

private lemma tendsto_R6 : Tendsto R6 atImInfty (nhds 1) := by
  have hU : Tendsto (fun τ : UpperHalfPlane => Work.Kernels.UFun τ) atImInfty (nhds 1) := by
    have h := Work.Modular.tendsto_theta3_atImInfty.pow 4
    simp only [one_pow] at h
    simpa only [UFun_eq_theta3] using h
  have hW : Tendsto (fun τ : UpperHalfPlane => Work.Kernels.WFun τ) atImInfty (nhds 1) := by
    have h := Work.Modular.tendsto_theta4_atImInfty.pow 4
    simp only [one_pow] at h
    simpa only [WFun_eq_theta4] using h
  have h1 := hU.pow 3
  have h2 := (hU.pow 2).mul hW
  have h3 := hU.mul (hW.pow 2)
  have h4 := hW.pow 3
  have hmain : Tendsto (fun τ : UpperHalfPlane =>
      - (Work.Kernels.UFun τ ^ 3)
        + (3 : ℂ) / 2 * (Work.Kernels.UFun τ ^ 2 * Work.Kernels.WFun τ)
        + (3 : ℂ) / 2 * (Work.Kernels.UFun τ * Work.Kernels.WFun τ ^ 2)
        - Work.Kernels.WFun τ ^ 3) atImInfty
      (nhds (-((1 : ℂ) ^ 3) + (3 : ℂ) / 2 * ((1 : ℂ) ^ 2 * 1)
        + (3 : ℂ) / 2 * (1 * (1 : ℂ) ^ 2) - (1 : ℂ) ^ 3)) :=
    ((h1.neg.add (h2.const_mul ((3 : ℂ) / 2))).add
      (h3.const_mul ((3 : ℂ) / 2))).sub h4
  rw [show (-((1 : ℂ) ^ 3) + (3 : ℂ) / 2 * ((1 : ℂ) ^ 2 * 1)
        + (3 : ℂ) / 2 * (1 * (1 : ℂ) ^ 2) - (1 : ℂ) ^ 3 : ℂ) = 1 by norm_num] at hmain
  exact hmain

private lemma isBoundedAtImInfty_R6 : IsBoundedAtImInfty R6 := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  have hnorm : Tendsto (fun z : UpperHalfPlane => ‖R6 z‖) atImInfty (nhds 1) := by
    simpa using tendsto_R6.norm
  have h1 : {z : UpperHalfPlane | ‖R6 z‖ ≤ 2} ∈ atImInfty := by
    have hmem2 : Set.Iic (2 : ℝ) ∈ nhds (1 : ℝ) :=
      mem_of_superset (IsOpen.mem_nhds isOpen_Iio (by norm_num)) Set.Iio_subset_Iic_self
    have h := hnorm.eventually hmem2
    filter_upwards [h] with z hz
    exact hz
  rw [UpperHalfPlane.atImInfty_mem] at h1
  obtain ⟨A, hA⟩ := h1
  exact ⟨2, A, fun z hz => hA z hz⟩

/-- The weight-six Eisenstein series in terms of the Jacobi theta quartics
`U = θ₀₀⁴`, `W = θ₀₁⁴` (with `U = W + V`, `V = θ₁₀⁴`):  `E₆ = -U³ + (3/2)U²W + (3/2)UW² - W³`. -/
theorem theta_E6_identity (z : UpperHalfPlane) :
    Work.Kernels.E6Fun z =
      - (Work.Kernels.UFun z ^ 3)
        + (3 : ℂ) / 2 * (Work.Kernels.UFun z ^ 2 * Work.Kernels.WFun z)
        + (3 : ℂ) / 2 * (Work.Kernels.UFun z * Work.Kernels.WFun z ^ 2)
        - Work.Kernels.WFun z ^ 3 := by
  obtain ⟨g, hg⟩ := Work.Modular.modularForm_of_slash_invariant (k := 6) R6_per
    mdifferentiable_R6 isBoundedAtImInfty_R6
  have hbddg : IsBoundedAtImInfty (⇑g : UpperHalfPlane → ℂ) := by
    rw [hg]; exact isBoundedAtImInfty_R6
  have hholg : MDiff (⇑g : UpperHalfPlane → ℂ) := by
    rw [hg]; exact mdifferentiable_R6
  have hperg : Function.Periodic ((⇑g : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex (f := g) one_mem_strictPeriods_SL
  have hanal : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (⇑g : UpperHalfPlane → ℂ)) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hperg hholg hbddg
  have hcoeff : (UpperHalfPlane.qExpansion 1 (⇑g : UpperHalfPlane → ℂ)).coeff 0 = 1 := by
    rw [UpperHalfPlane.qExpansion_coeff_zero one_pos hanal hperg]
    rw [show UpperHalfPlane.valueAtInfty (⇑g : UpperHalfPlane → ℂ) = 1 by
      rw [UpperHalfPlane.valueAtInfty, hg]
      exact tendsto_R6.limUnder_eq]
  have hrank : Module.finrank ℂ (ModularForm 𝒮ℒ 6) = 1 :=
    Module.rank_eq_one_iff_finrank_eq_one.mp ModularForm.levelOne_weight_six_rank_one
  have hE6ne : ModularForm.E₆ ≠ 0 :=
    EisensteinSeries.E_ne_zero (k := 6) (by norm_num) (by norm_num : Even 6)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ModularForm.E₆ hE6ne).mp hrank g
  have hcoe : (⇑(c • ModularForm.E₆) : UpperHalfPlane → ℂ) =
      c • (⇑ModularForm.E₆ : UpperHalfPlane → ℂ) := rfl
  have hcq : (UpperHalfPlane.qExpansion 1 (c • (⇑ModularForm.E₆ : UpperHalfPlane → ℂ))).coeff 0
      = c := by
    rw [UpperHalfPlane.qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero
      ModularForm.E₆ one_pos one_mem_strictPeriods_SL) c,
      PowerSeries.coeff_smul, Work.Modular.E6_qExpansion_coeff 0]
    simp
  have hc1 : c = 1 := by
    have h : (UpperHalfPlane.qExpansion 1 (c • (⇑ModularForm.E₆ : UpperHalfPlane → ℂ))).coeff 0
        = 1 := by
      rw [← hcoe, hc]
      exact hcoeff
    rwa [hcq] at h
  have hgE6 : g = ModularForm.E₆ := by rw [← hc, hc1, one_smul]
  have hfun : Work.Kernels.E6Fun = R6 :=
    calc Work.Kernels.E6Fun = (⇑ModularForm.E₆ : UpperHalfPlane → ℂ) := rfl
      _ = (⇑g : UpperHalfPlane → ℂ) := by rw [hgE6]
      _ = R6 := hg
  show Work.Kernels.E6Fun z = R6 z
  rw [hfun]

end
end Work.Residues
