import Mathlib
import Submission.Work.Modular.Basic
import Submission.Work.Modular.Lattice
import Submission.Work.Modular.ThetaFuncs
import Submission.Work.Modular.modularForm_of_slash_invariant
import Submission.Work.Modular.E4_qExpansion_coeff
import Submission.Work.Modular.theta4_S_smul
import Submission.Work.Modular.theta2_S_smul
import Submission.Work.Modular.theta2_at_cusp
import Submission.Work.Modular.thetaSeries_E8_decomposition

/-!
# The magic of dimension eight: `Θ_{E₈} = E₄`

We prove that the theta series of the `E₈` lattice in the standard model
(`Submission.Work.Modular.Lattice`) equals the normalized weight-four Eisenstein series
`E₄ = 1 + 240 ∑ σ₃(n) qⁿ`.

## Strategy

* By the classical decomposition `Θ_{E₈} = (1/2)(θ₂⁸ + θ₃⁸ + θ₄⁸)` of the `E₈` theta series
  into eighth powers of the Jacobi theta functions (`thetaSeries_E8_decomposition`), it is
  enough to identify `ThetaF := (θ₂⁸ + θ₃⁸ + θ₄⁸)/2` with `E₄`.
* `ThetaF` is invariant under the slash action of `SL(2, ℤ)` of weight `4`: on the generator
  `T : τ ↦ τ + 1` because `θ₃ ↦ θ₄`, `θ₄ ↦ θ₃`, `θ₂ ↦ e^{iπ/4} θ₂` (and `(e^{iπ/4})⁸ = 1`),
  and on the generator `S : τ ↦ -1/τ` because each `θᵢ` is multiplied by `(-iτ)^{1/2}`
  (Jacobi's imaginary transformation), and `((-iτ)^{1/2})⁸ = τ⁴`.
* `ThetaF` is holomorphic and bounded at the cusp `i∞` (where it tends to `1`), so
  `modularForm_of_slash_invariant` produces a level-one modular form `g` of weight `4` with
  `⇑g = ThetaF`; its constant term is `(qExpansion 1 ⇑g).coeff 0 = 1`.
* `dim M₄ = 1` (`ModularForm.levelOne_weight_four_rank_one`), so `g = c • E₄`; comparing
  constant terms gives `c = 1`, whence `ThetaF = ⇑E₄ = E₄`.
-/

namespace Work.Modular

open UpperHalfPlane ModularForm
open scoped Real MatrixGroups ModularForm Manifold Topology
open Filter

/-- The candidate modular form `(θ₃⁸ + θ₄⁸ + θ₂⁸) / 2`. -/
noncomputable def ThetaF : ℍ → ℂ :=
  fun τ => (1 / 2) * (theta3 τ ^ 8 + theta4 τ ^ 8 + theta2 τ ^ 8)

lemma ThetaF_T_smul (τ : ℍ) : ThetaF (ModularGroup.T • τ) = ThetaF τ := by
  have h : (Complex.exp (π * Complex.I / 4)) ^ 8 = 1 := by
    rw [← Complex.exp_nat_mul]
    rw [show (8 : ℕ) * (π * Complex.I / 4) = 2 * π * Complex.I by ring]
    exact Complex.exp_two_pi_mul_I
  simp only [ThetaF, theta3_T_smul, theta4_T_smul, theta2_T_smul, mul_pow, h]
  ring

lemma ThetaF_S_smul (τ : ℍ) : ThetaF (ModularGroup.S • τ) = (τ : ℂ) ^ 4 * ThetaF τ := by
  have h : ((-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ 8 = (τ : ℂ) ^ 4 := by
    have h4 : (((8 : ℕ) : ℂ) * (1 / 2)) = ((4 : ℕ) : ℂ) := by norm_num
    rw [← Complex.cpow_nat_mul, h4, Complex.cpow_natCast]
    rw [mul_pow, show (-Complex.I : ℂ) ^ 4 = 1 by
      rw [show (-Complex.I : ℂ) = (-1 : ℂ) * Complex.I by ring, mul_pow, Complex.I_pow_four,
        show (-1 : ℂ) ^ 4 = 1 by norm_num, one_mul]]
    ring
  simp only [ThetaF, theta3_S_smul, theta4_S_smul, theta2_S_smul, mul_pow, h]
  ring

lemma ThetaF_slash_T : ThetaF ∣[(4 : ℤ)] ModularGroup.T = ThetaF := by
  funext z
  rw [ModularForm.slash_action_eq'_iff, ThetaF_T_smul z]
  have h10 : ((ModularGroup.T : SL(2, ℤ)) 1 0 : ℂ) = 0 := by simp [ModularGroup.coe_T]
  have h11 : ((ModularGroup.T : SL(2, ℤ)) 1 1 : ℂ) = 1 := by simp [ModularGroup.coe_T]
  rw [h10, h11]
  simp

lemma ThetaF_slash_S : ThetaF ∣[(4 : ℤ)] ModularGroup.S = ThetaF := by
  funext z
  rw [ModularForm.slash_action_eq'_iff, ThetaF_S_smul z]
  have h10 : ((ModularGroup.S : SL(2, ℤ)) 1 0 : ℂ) = 1 := by simp [ModularGroup.coe_S]
  have h11 : ((ModularGroup.S : SL(2, ℤ)) 1 1 : ℂ) = 0 := by simp [ModularGroup.coe_S]
  rw [h10, h11]
  simp

lemma ThetaF_per : ∀ γ : SL(2, ℤ), ThetaF ∣[(4 : ℤ)] γ = ThetaF :=
  SlashInvariantForm.slash_action_generators_SL2Z ThetaF_slash_S ThetaF_slash_T

lemma mdifferentiable_ThetaF : MDiff ThetaF := by
  have h3 : MDiff (fun τ : ℍ => theta3 τ ^ 8) := mdifferentiable_theta3.pow 8
  have h4 : MDiff (fun τ : ℍ => theta4 τ ^ 8) := mdifferentiable_theta4.pow 8
  have h2 : MDiff (fun τ : ℍ => theta2 τ ^ 8) := mdifferentiable_theta2.pow 8
  have hsum : MDiff (fun τ : ℍ => theta3 τ ^ 8 + theta4 τ ^ 8 + theta2 τ ^ 8) :=
    (h3.add h4).add h2
  have hc : MDiff (fun _ : ℍ => (1 / 2 : ℂ)) := mdifferentiable_const
  have h := hc.mul hsum
  unfold ThetaF
  exact h

lemma tendsto_ThetaF : Filter.Tendsto ThetaF UpperHalfPlane.atImInfty (nhds 1) := by
  have h3 : Filter.Tendsto (fun τ : ℍ => theta3 τ ^ 8) UpperHalfPlane.atImInfty
      (nhds ((1 : ℂ) ^ 8)) := tendsto_theta3_atImInfty.pow 8
  have h4 : Filter.Tendsto (fun τ : ℍ => theta4 τ ^ 8) UpperHalfPlane.atImInfty
      (nhds ((1 : ℂ) ^ 8)) := tendsto_theta4_atImInfty.pow 8
  have h2 : Filter.Tendsto (fun τ : ℍ => theta2 τ ^ 8) UpperHalfPlane.atImInfty
      (nhds ((0 : ℂ) ^ 8)) := theta2_at_cusp.pow 8
  have hsum := (h3.add h4).add h2
  have hc : Filter.Tendsto (fun _ : ℍ => (1 / 2 : ℂ)) UpperHalfPlane.atImInfty
      (nhds (1 / 2 : ℂ)) := tendsto_const_nhds
  have hfin : Filter.Tendsto
      (fun τ : ℍ => (1 / 2 : ℂ) * (theta3 τ ^ 8 + theta4 τ ^ 8 + theta2 τ ^ 8))
      UpperHalfPlane.atImInfty (nhds 1) := by
    have h := hc.mul hsum
    convert h using 1
    norm_num
  rw [show ThetaF = (fun τ : ℍ => (1 / 2 : ℂ) * (theta3 τ ^ 8 + theta4 τ ^ 8 + theta2 τ ^ 8))
      from rfl]
  exact hfin

lemma isBoundedAtImInfty_ThetaF : UpperHalfPlane.IsBoundedAtImInfty ThetaF := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  have hnorm : Filter.Tendsto (fun z : ℍ => ‖ThetaF z‖) UpperHalfPlane.atImInfty (nhds 1) := by
    simpa using tendsto_ThetaF.norm
  have h1 : {z : ℍ | ‖ThetaF z‖ ≤ 2} ∈ UpperHalfPlane.atImInfty := by
    have hmem2 : Set.Iic (2 : ℝ) ∈ nhds (1 : ℝ) :=
      mem_of_superset (IsOpen.mem_nhds isOpen_Iio (by norm_num)) Set.Iio_subset_Iic_self
    have h := hnorm.eventually hmem2
    filter_upwards [h] with z hz
    exact hz
  rw [UpperHalfPlane.atImInfty_mem] at h1
  obtain ⟨A, hA⟩ := h1
  exact ⟨2, A, fun z hz => hA z hz⟩

/-- **The magic of dimension eight**: the theta series of the `E₈` lattice is the Eisenstein
series `E₄`.  (`Θ_{E₈}` is a level-one modular form of weight `4` by
`modularForm_of_slash_invariant`, its constant term is `1`, and `dim M₄ = 1`.) -/
theorem thetaSeries_E8_eq_E4 : thetaSeries E8 = E4 := by
  obtain ⟨g, hg⟩ := modularForm_of_slash_invariant (k := 4) ThetaF_per
    mdifferentiable_ThetaF isBoundedAtImInfty_ThetaF
  have hbddg : UpperHalfPlane.IsBoundedAtImInfty (⇑g : ℍ → ℂ) := by
    rw [hg]; exact isBoundedAtImInfty_ThetaF
  have hholg : MDiff (⇑g : ℍ → ℂ) := by rw [hg]; exact mdifferentiable_ThetaF
  have hperg : Function.Periodic ((⇑g : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex (f := g) one_mem_strictPeriods_SL
  have hanal : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (⇑g : ℍ → ℂ)) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hperg hholg hbddg
  have hcoeff : (UpperHalfPlane.qExpansion 1 (⇑g : ℍ → ℂ)).coeff 0 = 1 := by
    rw [UpperHalfPlane.qExpansion_coeff_zero one_pos hanal hperg]
    rw [show UpperHalfPlane.valueAtInfty (⇑g : ℍ → ℂ) = 1 by
      rw [UpperHalfPlane.valueAtInfty, hg]
      exact tendsto_ThetaF.limUnder_eq]
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
  have hc1 : c = 1 := by
    have h : (UpperHalfPlane.qExpansion 1 (c • (⇑ModularForm.E₄ : ℍ → ℂ))).coeff 0 = 1 := by
      rw [← hcoe, hc]
      exact hcoeff
    rwa [hcq] at h
  have hgE4 : g = ModularForm.E₄ := by rw [← hc, hc1, one_smul]
  have hdec : ∀ τ : ℍ, thetaSeries E8 τ = ThetaF τ := fun τ => by
    rw [show ThetaF = (fun τ : ℍ => (1 / 2 : ℂ) * (theta3 τ ^ 8 + theta4 τ ^ 8 + theta2 τ ^ 8))
      from rfl]
    exact thetaSeries_E8_decomposition τ
  funext τ
  rw [hdec τ, ← hg, hgE4]

end Work.Modular
