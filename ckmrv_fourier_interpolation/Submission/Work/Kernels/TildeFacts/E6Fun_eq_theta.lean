import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Modular.modularForm_of_slash_invariant
import Submission.Work.Modular.ThetaFuncs
import Submission.Work.Modular.theta2_S_smul
import Submission.Work.Modular.theta4_S_smul
import Submission.Work.Modular.theta2_at_cusp
import Submission.Work.Kernels.TildeFacts.theta_quartic
import Submission.Work.Modular.E6_qExpansion_coeff

/-!
# `E₆` in terms of the fourth powers of the Jacobi theta functions

We prove the level-one identity

`E₆ = (θ₀₁⁴ - θ₁₀⁴)(θ₁₀⁸ + θ₀₁⁸ + (5/2) θ₁₀⁴ θ₀₁⁴)`,

i.e. `E₆ = (W - V)(V² + W² + (5/2) V W)` with `W = θ₀₁⁴`, `V = θ₁₀⁴`.
Equivalently, using Jacobi's quartic identity `θ₀₀⁴ = θ₀₁⁴ + θ₁₀⁴`
(`theta_quartic`), this is `E₆ = ½ (U + V)(U + W)(W - V)` with `U = θ₀₀⁴`.

## Strategy

Write `G₆ = ½ (θ₃⁴ + θ₂⁴)(θ₃⁴ + θ₄⁴)(θ₄⁴ - θ₂⁴)` in the classical theta notation
(`θ₃ = θ₀₀`, `θ₄ = θ₀₁`, `θ₂ = θ₁₀`).

* On `T : τ ↦ τ + 1` we have `θ₃ ↦ θ₄`, `θ₄ ↦ θ₃`, `θ₂ ↦ e^{iπ/4} θ₂`, so the three
  factors of `G₆` are simply permuted: `G₆` is `T`-invariant.
* On `S : τ ↦ -1/τ` Jacobi's imaginary transformation gives
  `θ₃ ↦ α θ₃`, `θ₄ ↦ α θ₂`, `θ₂ ↦ α θ₄` with `α = (-iτ)^{1/2}`, `α⁴ = -τ²`, so the two
  factors carrying `θ₄`, `θ₂` swap and `G₆(S•τ) = τ⁶ G₆(τ)`.
* Hence `G₆` is slash-invariant of weight `6` for `SL(2, ℤ)`; it is holomorphic and bounded
  at the cusp `i∞` (with value `1`), so `modularForm_of_slash_invariant` produces a level-one
  modular form `g` of weight `6` with `⇑g = G₆`.
* The constant term of `G₆` at the cusp is `1`, and `dim M₆ = 1`
  (`ModularForm.levelOne_weight_six_rank_one`), so `g = E₆`.
* Finally Jacobi's quartic identity `θ₃⁴ = θ₄⁴ + θ₂⁴` shows `G₆` equals the right hand side.
-/

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Real Topology
open Filter Work.Modular

namespace Work.Kernels.TildeFacts

/-- The candidate modular form of weight six, in the manifestly `T`-invariant product form
`G₆ = ½ (θ₃⁴ + θ₂⁴)(θ₃⁴ + θ₄⁴)(θ₄⁴ - θ₂⁴)`. -/
private noncomputable def G6 : ℍ → ℂ :=
  fun τ => (1 / 2) * (theta3 τ ^ 4 + theta2 τ ^ 4) * (theta3 τ ^ 4 + theta4 τ ^ 4)
    * (theta4 τ ^ 4 - theta2 τ ^ 4)

/-- The function appearing in the statement,
`F₆ = (θ₄⁴ - θ₂⁴)(θ₂⁸ + θ₄⁸ + (5/2) θ₂⁴ θ₄⁴)`. -/
private noncomputable def F6 : ℍ → ℂ :=
  fun τ => (theta4 τ ^ 4 - theta2 τ ^ 4)
    * (theta2 τ ^ 8 + theta4 τ ^ 8 + (5 / 2) * theta2 τ ^ 4 * theta4 τ ^ 4)

/-! ## Transformation laws -/

/-- The fourth power of `e^{iπ/4}` is `-1`. -/
private lemma exp_pi_I_div_four_pow_four :
    (Complex.exp (Real.pi * Complex.I / 4)) ^ 4 = -1 := by
  rw [← Complex.exp_nat_mul]
  rw [show (4 : ℕ) * (Real.pi * Complex.I / 4) = Real.pi * Complex.I by ring]
  exact Complex.exp_pi_mul_I

/-- The fourth power of the automorphy factor: `((-iτ)^{1/2})⁴ = -τ²`. -/
private lemma auFactor_pow_four (τ : ℍ) :
    ((-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ 4 = -(τ : ℂ) ^ 2 := by
  have h4 : (((4 : ℕ) : ℂ) * (1 / 2)) = ((2 : ℕ) : ℂ) := by norm_num
  rw [← Complex.cpow_nat_mul, h4, Complex.cpow_natCast]
  rw [mul_pow, show (-Complex.I : ℂ) ^ 2 = -1 by
    rw [show (-Complex.I : ℂ) = (-1 : ℂ) * Complex.I by ring, mul_pow, Complex.I_sq,
      show ((-1 : ℂ)) ^ 2 = 1 by norm_num, one_mul]]
  ring

/-- `G₆` is invariant under `T : τ ↦ τ + 1`. -/
private lemma G6_T_smul (τ : ℍ) : G6 (ModularGroup.T • τ) = G6 τ := by
  have h3 : theta3 (ModularGroup.T • τ) = theta4 τ := theta3_T_smul τ
  have h4 : theta4 (ModularGroup.T • τ) = theta3 τ := theta4_T_smul τ
  have h2 : theta2 (ModularGroup.T • τ) =
      Complex.exp (Real.pi * Complex.I / 4) * theta2 τ := theta2_T_smul τ
  simp only [G6, h3, h4, h2, mul_pow, exp_pi_I_div_four_pow_four]
  ring

/-- `G₆` transforms with the weight-six automorphy factor under `S : τ ↦ -1/τ`. -/
private lemma G6_S_smul (τ : ℍ) : G6 (ModularGroup.S • τ) = (τ : ℂ) ^ 6 * G6 τ := by
  have h3 : theta3 (ModularGroup.S • τ) =
      (-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) * theta3 τ := theta3_S_smul τ
  have h4 : theta4 (ModularGroup.S • τ) =
      (-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) * theta2 τ := theta4_S_smul τ
  have h2 : theta2 (ModularGroup.S • τ) =
      (-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) * theta4 τ := theta2_S_smul τ
  simp only [G6, h3, h4, h2, mul_pow, auFactor_pow_four]
  ring

/-! ## Slash invariance -/

private lemma G6_slash_T : G6 ∣[(6 : ℤ)] ModularGroup.T = G6 := by
  funext z
  rw [ModularForm.slash_action_eq'_iff, G6_T_smul z]
  have h10 : ((ModularGroup.T : SL(2, ℤ)) 1 0 : ℂ) = 0 := by simp [ModularGroup.coe_T]
  have h11 : ((ModularGroup.T : SL(2, ℤ)) 1 1 : ℂ) = 1 := by simp [ModularGroup.coe_T]
  rw [h10, h11]
  simp

private lemma G6_slash_S : G6 ∣[(6 : ℤ)] ModularGroup.S = G6 := by
  funext z
  rw [ModularForm.slash_action_eq'_iff, G6_S_smul z]
  have h10 : ((ModularGroup.S : SL(2, ℤ)) 1 0 : ℂ) = 1 := by simp [ModularGroup.coe_S]
  have h11 : ((ModularGroup.S : SL(2, ℤ)) 1 1 : ℂ) = 0 := by simp [ModularGroup.coe_S]
  rw [h10, h11]
  simp

private lemma G6_per : ∀ γ : SL(2, ℤ), G6 ∣[(6 : ℤ)] γ = G6 :=
  SlashInvariantForm.slash_action_generators_SL2Z G6_slash_S G6_slash_T

/-! ## Holomorphy, and behaviour at the cusp -/

private lemma mdifferentiable_G6 : MDiff G6 := by
  have h3 : MDiff (fun τ : ℍ => theta3 τ ^ 4) := mdifferentiable_theta3.pow 4
  have h4 : MDiff (fun τ : ℍ => theta4 τ ^ 4) := mdifferentiable_theta4.pow 4
  have h2 : MDiff (fun τ : ℍ => theta2 τ ^ 4) := mdifferentiable_theta2.pow 4
  have h1 : MDiff (fun τ : ℍ => (1 / 2 : ℂ) * (theta3 τ ^ 4 + theta2 τ ^ 4)) :=
    mdifferentiable_const.mul (h3.add h2)
  have h2' : MDiff (fun τ : ℍ => (1 / 2 : ℂ) * (theta3 τ ^ 4 + theta2 τ ^ 4)
      * (theta3 τ ^ 4 + theta4 τ ^ 4)) :=
    h1.mul (h3.add h4)
  have h3' : MDiff (fun τ : ℍ => (1 / 2 : ℂ) * (theta3 τ ^ 4 + theta2 τ ^ 4)
      * (theta3 τ ^ 4 + theta4 τ ^ 4) * (theta4 τ ^ 4 - theta2 τ ^ 4)) :=
    h2'.mul (h4.sub h2)
  exact h3'

private lemma tendsto_G6 : Tendsto G6 atImInfty (nhds 1) := by
  have h3 : Tendsto (fun τ : ℍ => theta3 τ ^ 4) atImInfty (nhds ((1 : ℂ) ^ 4)) :=
    tendsto_theta3_atImInfty.pow 4
  have h4 : Tendsto (fun τ : ℍ => theta4 τ ^ 4) atImInfty (nhds ((1 : ℂ) ^ 4)) :=
    tendsto_theta4_atImInfty.pow 4
  have h2 : Tendsto (fun τ : ℍ => theta2 τ ^ 4) atImInfty (nhds ((0 : ℂ) ^ 4)) :=
    theta2_at_cusp.pow 4
  have hc : Tendsto (fun _ : ℍ => (1 / 2 : ℂ)) atImInfty (nhds (1 / 2 : ℂ)) :=
    tendsto_const_nhds
  have hmain : Tendsto
      (fun τ : ℍ => (1 / 2 : ℂ) * (theta3 τ ^ 4 + theta2 τ ^ 4)
        * (theta3 τ ^ 4 + theta4 τ ^ 4) * (theta4 τ ^ 4 - theta2 τ ^ 4))
      atImInfty (nhds 1) := by
    have h := ((hc.mul (h3.add h2)).mul (h3.add h4)).mul (h4.sub h2)
    convert h using 1
    norm_num
  exact hmain

private lemma isBoundedAtImInfty_G6 : IsBoundedAtImInfty G6 := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  have hnorm : Tendsto (fun z : ℍ => ‖G6 z‖) atImInfty (nhds 1) := by
    simpa using tendsto_G6.norm
  have h1 : {z : ℍ | ‖G6 z‖ ≤ 2} ∈ atImInfty := by
    have hmem2 : Set.Iic (2 : ℝ) ∈ nhds (1 : ℝ) :=
      mem_of_superset (isOpen_Iio.mem_nhds (by norm_num)) Set.Iio_subset_Iic_self
    have h := hnorm.eventually hmem2
    filter_upwards [h] with z hz
    exact hz
  rw [UpperHalfPlane.atImInfty_mem] at h1
  obtain ⟨A, hA⟩ := h1
  exact ⟨2, A, fun z hz => hA z hz⟩

/-! ## Identifying `G₆` with `E₆` -/

private lemma E6Fun_eq_G6 : Work.Kernels.E6Fun = G6 := by
  obtain ⟨g, hg⟩ := modularForm_of_slash_invariant (k := 6) G6_per
    mdifferentiable_G6 isBoundedAtImInfty_G6
  have hbddg : IsBoundedAtImInfty (⇑g : ℍ → ℂ) := by
    rw [hg]; exact isBoundedAtImInfty_G6
  have hholg : MDiff (⇑g : ℍ → ℂ) := by rw [hg]; exact mdifferentiable_G6
  have hperg : Function.Periodic ((⇑g : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex (f := g) one_mem_strictPeriods_SL
  have hanal : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (⇑g : ℍ → ℂ)) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hperg hholg hbddg
  have hcoeff : (UpperHalfPlane.qExpansion 1 (⇑g : ℍ → ℂ)).coeff 0 = 1 := by
    rw [UpperHalfPlane.qExpansion_coeff_zero one_pos hanal hperg]
    rw [show UpperHalfPlane.valueAtInfty (⇑g : ℍ → ℂ) = 1 by
      rw [UpperHalfPlane.valueAtInfty, hg]
      exact tendsto_G6.limUnder_eq]
  have hrank : Module.finrank ℂ (ModularForm 𝒮ℒ 6) = 1 :=
    Module.rank_eq_one_iff_finrank_eq_one.mp ModularForm.levelOne_weight_six_rank_one
  have hE6ne : ModularForm.E₆ ≠ 0 :=
    EisensteinSeries.E_ne_zero (k := 6) (by norm_num) ⟨3, rfl⟩
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ModularForm.E₆ hE6ne).mp hrank g
  have hcoe : (⇑(c • ModularForm.E₆) : ℍ → ℂ) = c • (⇑ModularForm.E₆ : ℍ → ℂ) := rfl
  have hcq : (UpperHalfPlane.qExpansion 1 (c • (⇑ModularForm.E₆ : ℍ → ℂ))).coeff 0 = c := by
    rw [UpperHalfPlane.qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero
      ModularForm.E₆ one_pos one_mem_strictPeriods_SL) c,
      PowerSeries.coeff_smul, Work.Modular.E6_qExpansion_coeff 0]
    simp
  have hc1 : c = 1 := by
    have h : (UpperHalfPlane.qExpansion 1 (c • (⇑ModularForm.E₆ : ℍ → ℂ))).coeff 0 = 1 := by
      rw [← hcoe, hc]
      exact hcoeff
    rwa [hcq] at h
  have hgE6 : g = ModularForm.E₆ := by rw [← hc, hc1, one_smul]
  have hE6eq : (⇑ModularForm.E₆ : ℍ → ℂ) = G6 := by rw [← hgE6, hg]
  exact hE6eq

/-! ## The quartic identity relates `G₆` and the stated right hand side -/

/-- Jacobi's quartic identity `θ₃⁴ = θ₄⁴ + θ₂⁴`. -/
private lemma theta3_pow_four (τ : ℍ) : theta3 τ ^ 4 = theta4 τ ^ 4 + theta2 τ ^ 4 := by
  have h := theta_quartic τ
  simpa only [Work.Kernels.UFun, Work.Kernels.WFun, Work.Kernels.VFun, Work.Kernels.theta00Fun,
    Work.Kernels.theta01Fun, Work.Kernels.theta10Fun, Work.Modular.theta3, Work.Modular.theta4,
    Work.Modular.theta2] using h

private lemma G6_eq_F6 (τ : ℍ) : G6 τ = F6 τ := by
  simp only [G6, F6, theta3_pow_four τ]
  ring

private lemma F6_eq_theta (z : ℍ) :
    F6 z = (Work.Kernels.WFun z - Work.Kernels.VFun z) *
      (Work.Kernels.VFun z ^ 2 + Work.Kernels.WFun z ^ 2
        + (5 / 2) * Work.Kernels.VFun z * Work.Kernels.WFun z) := by
  simp only [F6, Work.Kernels.WFun, Work.Kernels.VFun, Work.Kernels.theta01Fun,
    Work.Kernels.theta10Fun, Work.Modular.theta4, Work.Modular.theta2]
  ring

/-- `E₆` in terms of the fourth powers of the Jacobi theta functions:
`E₆ = (θ₀₁⁴-θ₁₀⁴)(θ₁₀⁸+θ₀₁⁸+(5/2)θ₁₀⁴θ₀₁⁴)`, i.e.
`E₆ = (W-V)(V²+W²+(5/2)VW)` with `W = θ₀₁⁴`, `V = θ₁₀⁴`; equivalently
`E₆ = ½(U+V)(U+W)(W-V)` with `U = θ₀₀⁴`. -/
theorem E6Fun_eq_theta (z : UpperHalfPlane) :
    Work.Kernels.E6Fun z = (Work.Kernels.WFun z - Work.Kernels.VFun z) *
      (Work.Kernels.VFun z ^ 2 + Work.Kernels.WFun z ^ 2
        + (5 / 2) * Work.Kernels.VFun z * Work.Kernels.WFun z) := by
  rw [E6Fun_eq_G6, G6_eq_F6 z, F6_eq_theta z]

end Work.Kernels.TildeFacts
