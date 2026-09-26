import Mathlib
import Submission.Work.Modular.Basic
import Submission.Work.Modular.E2_S_smul
import Submission.Work.Modular.E2_T_smul
import Submission.Work.Modular.E2_qExpansion_coeff
import Submission.Work.Modular.E4_qExpansion_coeff
import Submission.Work.Modular.modularForm_of_slash_invariant
import Submission.Work.Modular.qExpansion_normalizedDerivOfComplex
import Submission.Work.Modular.E2_tendsto_atImInfty
import Submission.Work.Modular.D_E2_tendsto_atImInfty
import Submission.Work.Modular.E4_tendsto_atImInfty

/-!
# Ramanujan's identity for `E₂`

`D E₂ = (E₂² - E₄)/12`, where `D = (2πi)⁻¹ d/dτ` is `Derivative.normalizedDerivOfComplex`.

The proof follows the classical Sturm-bound route.  Write
`H = D E₂ - (E₂² - E₄)/12`.  Applying `D` to the `S`-transformation law of `E₂`
(`E2_S_smul`) via `Derivative.normalizedDerivOfComplex_SL_slash`, together with
`ModularForm.mul_slash_SL2` for the square of `E₂` and the modularity of `E₄`, shows
`H ∣[4] S = H`; since `H` is also invariant under `T` (`E2_T_smul`) and `S`, `T`
generate `SL(2, ℤ)` (`SlashInvariantForm.slash_action_generators_SL2Z`), `H` is a
level-one modular form of weight `4` (`Work.Modular.modularForm_of_slash_invariant`).
It vanishes at the cusp `i∞` (the `q`-expansion of `D E₂` has vanishing constant term,
while `E₂`, `E₄ → 1`), so it is a cusp form; since the space of level-one cusp forms
of weight `4` is trivial, `H = 0`.
-/

namespace Work.Modular

open UpperHalfPlane ModularForm
open scoped Manifold MatrixGroups ModularForm Topology

lemma two_mul_inv_two_pi_I : (2:ℂ) * (2 * (Real.pi : ℂ) * Complex.I)⁻¹ = -Complex.I / Real.pi := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by simp [Complex.ofReal_eq_zero]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp
  try rw [Complex.I_sq]
  ring

lemma six_div_pi_mul_inv_two_pi_I :
    (6*Complex.I/Real.pi) * (2 * (Real.pi:ℂ) * Complex.I)⁻¹ = 3/(Real.pi:ℂ)^2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by simp [Complex.ofReal_eq_zero]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp
  try rw [Complex.I_sq]
  ring

lemma MDiff_inv_coe : MDiff (fun z : ℍ => ((z:ℂ))⁻¹) := by
  have h : MDiff ((fun z : ℍ => ((z:ℂ)))⁻¹) :=
    (UpperHalfPlane.mdifferentiable_coe).inv (fun z => z.ne_zero)
  exact h

lemma D_inv_coe : Derivative.normalizedDerivOfComplex (fun z : ℍ => ((z:ℂ))⁻¹) =
    fun z : ℍ => -((2 * Real.pi * Complex.I)⁻¹) / (z:ℂ)^2 := by
  ext z
  have hcomp : (fun w : ℂ => ((UpperHalfPlane.ofComplex w : ℍ) : ℂ)⁻¹) =ᶠ[𝓝 (z:ℂ)]
      fun w : ℂ => w⁻¹ := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  change (2 * Real.pi * Complex.I)⁻¹ * deriv (fun w : ℂ => ((UpperHalfPlane.ofComplex w : ℍ) : ℂ)⁻¹) (z:ℂ)
      = -((2 * Real.pi * Complex.I)⁻¹) / (z:ℂ)^2
  rw [Filter.EventuallyEq.deriv_eq hcomp, deriv_inv]
  ring

lemma D_const_div (c : ℂ) :
    Derivative.normalizedDerivOfComplex (fun z : ℍ => c / (z:ℂ)) =
      fun z : ℍ => -(c * (2 * Real.pi * Complex.I)⁻¹) / (z:ℂ)^2 := by
  have hfun : (fun z : ℍ => c / (z:ℂ)) = c • (fun z : ℍ => ((z:ℂ))⁻¹) := by
    ext z; simp [div_eq_mul_inv]
  rw [hfun, Derivative.normalizedDerivOfComplex_smul c _ MDiff_inv_coe, D_inv_coe]
  ext z
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma E2_slash_S_fun : E2 ∣[(2:ℤ)] ModularGroup.S =
    fun z : ℍ => E2 z - 6 * Complex.I / (Real.pi * (z : ℂ)) := by
  ext z
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_S, E2_S_smul z]
  rw [zpow_neg, zpow_ofNat]
  have hz : (z:ℂ) ≠ 0 := z.ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := by simp [Complex.ofReal_eq_zero]
  field_simp

lemma E2_slash_T_fun : E2 ∣[(2:ℤ)] ModularGroup.T = E2 := by
  ext z
  rw [ModularForm.SL_slash_apply, denom_T, E2_T_smul z]
  simp

lemma E4_slash_S : E4 ∣[(4:ℤ)] ModularGroup.S = E4 := by
  have h := SlashInvariantForm.slash_action_eqn (ModularForm.E₄)
    (ModularGroup.S : GL (Fin 2) ℝ) ⟨ModularGroup.S, rfl⟩
  rw [ModularForm.SL_slash]
  exact h

lemma E4_slash_T : E4 ∣[(4:ℤ)] ModularGroup.T = E4 := by
  have h := SlashInvariantForm.slash_action_eqn (ModularForm.E₄)
    (ModularGroup.T : GL (Fin 2) ℝ) ⟨ModularGroup.T, rfl⟩
  rw [ModularForm.SL_slash]
  exact h

noncomputable def corr : ℍ → ℂ :=
  fun z => Complex.I * E2 z / (Real.pi * (z:ℂ)) + 3 / (Real.pi^2 * (z:ℂ)^2)

lemma D_E2_slash_S :
    Derivative.normalizedDerivOfComplex E2 ∣[(4:ℤ)] ModularGroup.S =
      Derivative.normalizedDerivOfComplex E2 - corr := by
  unfold corr
  have hmdiv : MDiff (fun z : ℍ => (6*Complex.I/Real.pi) / (z:ℂ)) := by
    have h' : MDiff ((fun _ : ℍ => (6*Complex.I/Real.pi)) / (fun z : ℍ => ((z:ℂ)))) :=
      (mdifferentiable_const (c := 6*Complex.I/Real.pi)).div
        (UpperHalfPlane.mdifferentiable_coe) (fun z => z.ne_zero)
    exact h'
  have hdu : Derivative.normalizedDerivOfComplex (fun z : ℍ => E2 z - 6*Complex.I/(Real.pi*(z:ℂ)))
      = Derivative.normalizedDerivOfComplex E2 + (fun z : ℍ => 3/(Real.pi^2*(z:ℂ)^2)) := by
    have hsub : (fun z : ℍ => E2 z - 6*Complex.I/(Real.pi*(z:ℂ)))
        = E2 - (fun z : ℍ => (6*Complex.I/Real.pi)/(z:ℂ)) := by
      ext z
      simp only [Pi.sub_apply]
      have hz : (z:ℂ) ≠ 0 := z.ne_zero
      have hpi : (Real.pi : ℂ) ≠ 0 := by simp [Complex.ofReal_eq_zero]
      field_simp
    rw [hsub, Derivative.normalizedDerivOfComplex_sub E2 _ E2_mdifferentiable hmdiv,
      D_const_div (6*Complex.I/Real.pi)]
    rw [show (fun z : ℍ => -(6*Complex.I/Real.pi * (2 * Real.pi * Complex.I)⁻¹) / (z:ℂ)^2)
        = fun z : ℍ => -(3/(Real.pi^2 * (z:ℂ)^2)) from by
      funext z; rw [six_div_pi_mul_inv_two_pi_I]; ring]
    ext z; simp only [Pi.sub_apply, Pi.add_apply]; ring
  have h := Derivative.normalizedDerivOfComplex_SL_slash (k := (2:ℤ)) (F := E2) E2_mdifferentiable (γ := ModularGroup.S)
  have hS10 : ((ModularGroup.S : SL(2,ℤ)) 1 0 : ℤ) = 1 := by decide
  simp only [hS10, ModularGroup.denom_S] at h
  rw [E2_slash_S_fun] at h
  have hk : (2:ℤ) + 2 = 4 := by norm_num
  rw [hk] at h
  rw [hdu] at h
  rw [← eq_sub_iff_add_eq.mp h]
  ext z
  simp only [Pi.add_apply, Pi.sub_apply]
  have hz : (z:ℂ) ≠ 0 := z.ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := by simp [Complex.ofReal_eq_zero]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

lemma D_E2_slash_T :
    Derivative.normalizedDerivOfComplex E2 ∣[(4:ℤ)] ModularGroup.T =
      Derivative.normalizedDerivOfComplex E2 := by
  have h := Derivative.normalizedDerivOfComplex_SL_slash (k := (2:ℤ)) (F := E2) E2_mdifferentiable (γ := ModularGroup.T)
  have hT10 : ((ModularGroup.T : SL(2,ℤ)) 1 0 : ℤ) = 0 := by decide
  simp only [hT10, Int.cast_zero, zero_div, mul_zero, zero_mul] at h
  have hk : (2:ℤ) + 2 = 4 := by norm_num
  rw [hk] at h
  rw [E2_slash_T_fun] at h
  have hc : (fun z : ℍ => (0:ℂ)) = 0 := by funext z; rfl
  rw [hc, sub_zero] at h
  exact h.symm

lemma quad_slash_S : (fun z : ℍ => (E2 z^2 - E4 z)/12) ∣[(4:ℤ)] ModularGroup.S
    = (fun z : ℍ => (E2 z^2 - E4 z)/12) - corr := by
  have hE2sq : (E2 ^ 2) ∣[(4:ℤ)] ModularGroup.S = (E2 ∣[(2:ℤ)] ModularGroup.S) ^ 2 := by
    have h := ModularForm.mul_slash_SL2 (2:ℤ) (2:ℤ) ModularGroup.S E2 E2
    simpa [pow_two] using h
  have hdec : (fun z : ℍ => (E2 z^2 - E4 z)/12) = (12:ℂ)⁻¹ • (E2 ^ 2 - E4) := by
    ext z; simp [div_eq_mul_inv, mul_comm]
  rw [hdec, ModularForm.SL_smul_slash]
  have hcomb : (E2 ^ 2 - E4) ∣[(4:ℤ)] ModularGroup.S = (E2 ∣[(2:ℤ)] ModularGroup.S) ^ 2 - E4 := by
    have h2 : (E2 ^ 2 - E4) ∣[(4:ℤ)] ModularGroup.S
        = (E2 ^ 2) ∣[(4:ℤ)] ModularGroup.S - E4 ∣[(4:ℤ)] ModularGroup.S := by
      simp [sub_eq_add_neg]
    rw [h2, hE2sq, E4_slash_S]
  rw [hcomb, E2_slash_S_fun]
  ext z
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.pow_apply, smul_eq_mul]
  unfold corr
  have hz : (z:ℂ) ≠ 0 := z.ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := by simp [Complex.ofReal_eq_zero]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

lemma quad_slash_T : (fun z : ℍ => (E2 z^2 - E4 z)/12) ∣[(4:ℤ)] ModularGroup.T
    = (fun z : ℍ => (E2 z^2 - E4 z)/12) := by
  have hE2sq : (E2 ^ 2) ∣[(4:ℤ)] ModularGroup.T = (E2 ∣[(2:ℤ)] ModularGroup.T) ^ 2 := by
    have h := ModularForm.mul_slash_SL2 (2:ℤ) (2:ℤ) ModularGroup.T E2 E2
    simpa [pow_two] using h
  have hdec : (fun z : ℍ => (E2 z^2 - E4 z)/12) = (12:ℂ)⁻¹ • (E2 ^ 2 - E4) := by
    ext z; simp [div_eq_mul_inv, mul_comm]
  rw [hdec, ModularForm.SL_smul_slash]
  have hcomb : (E2 ^ 2 - E4) ∣[(4:ℤ)] ModularGroup.T = E2 ^ 2 - E4 := by
    have h2 : (E2 ^ 2 - E4) ∣[(4:ℤ)] ModularGroup.T
        = (E2 ^ 2) ∣[(4:ℤ)] ModularGroup.T - E4 ∣[(4:ℤ)] ModularGroup.T := by
      simp [sub_eq_add_neg]
    rw [h2, hE2sq, E4_slash_T, E2_slash_T_fun]
  rw [hcomb]

noncomputable def ramanujanH : ℍ → ℂ :=
  Derivative.normalizedDerivOfComplex E2 - (fun z : ℍ => (E2 z^2 - E4 z)/12)

lemma ramanujanH_slash_S : ramanujanH ∣[(4:ℤ)] ModularGroup.S = ramanujanH := by
  show (Derivative.normalizedDerivOfComplex E2 - (fun z : ℍ => (E2 z^2 - E4 z)/12)) ∣[(4:ℤ)] ModularGroup.S
    = Derivative.normalizedDerivOfComplex E2 - (fun z : ℍ => (E2 z^2 - E4 z)/12)
  have h1 : (Derivative.normalizedDerivOfComplex E2 - (fun z : ℍ => (E2 z^2 - E4 z)/12)) ∣[(4:ℤ)] ModularGroup.S
      = (Derivative.normalizedDerivOfComplex E2 ∣[(4:ℤ)] ModularGroup.S)
        - ((fun z : ℍ => (E2 z^2 - E4 z)/12) ∣[(4:ℤ)] ModularGroup.S) := by
    simp [sub_eq_add_neg]
  rw [h1, D_E2_slash_S, quad_slash_S]
  ring

lemma ramanujanH_slash_T : ramanujanH ∣[(4:ℤ)] ModularGroup.T = ramanujanH := by
  show (Derivative.normalizedDerivOfComplex E2 - (fun z : ℍ => (E2 z^2 - E4 z)/12)) ∣[(4:ℤ)] ModularGroup.T
    = Derivative.normalizedDerivOfComplex E2 - (fun z : ℍ => (E2 z^2 - E4 z)/12)
  have h1 : (Derivative.normalizedDerivOfComplex E2 - (fun z : ℍ => (E2 z^2 - E4 z)/12)) ∣[(4:ℤ)] ModularGroup.T
      = (Derivative.normalizedDerivOfComplex E2 ∣[(4:ℤ)] ModularGroup.T)
        - ((fun z : ℍ => (E2 z^2 - E4 z)/12) ∣[(4:ℤ)] ModularGroup.T) := by
    simp [sub_eq_add_neg]
  rw [h1, D_E2_slash_T, quad_slash_T]

lemma ramanujanH_mdiff : MDiff ramanujanH := by
  have h1 : MDiff (Derivative.normalizedDerivOfComplex E2) :=
    Derivative.normalizedDerivOfComplex_mdifferentiable E2_mdifferentiable
  have hq : MDiff (E2 ^ 2 : ℍ → ℂ) := by
    simpa [pow_two] using E2_mdifferentiable.mul E2_mdifferentiable
  have hE4 : MDiff E4 := ModularForm.E₄.holo'
  have h2 : MDiff ((12:ℂ)⁻¹ • (E2 ^ 2 - E4)) :=
    MDifferentiable.const_smul (12:ℂ)⁻¹ (hq.sub hE4)
  have h2' : MDiff ((fun z : ℍ => (E2 z^2 - E4 z)/12) : ℍ → ℂ) := by
    have heq : ((fun z : ℍ => (E2 z^2 - E4 z)/12) : ℍ → ℂ) = (12:ℂ)⁻¹ • (E2 ^ 2 - E4) := by
      ext z; simp [div_eq_mul_inv, mul_comm]
    rw [heq]
    exact h2
  exact h1.sub h2'

lemma ramanujanH_isZeroAtImInfty : IsZeroAtImInfty ramanujanH := by
  have h1 : Filter.Tendsto (fun z : ℍ => (E2 z ^ 2 - E4 z)) UpperHalfPlane.atImInfty (𝓝 (0:ℂ)) := by
    have hmul : Filter.Tendsto (fun z : ℍ => E2 z * E2 z) UpperHalfPlane.atImInfty (𝓝 ((1:ℂ) * 1)) :=
      E2_tendsto_atImInfty.mul E2_tendsto_atImInfty
    have h := hmul.sub E4_tendsto_atImInfty
    simpa [pow_two] using h
  have h2 : Filter.Tendsto (fun z : ℍ => (E2 z ^ 2 - E4 z)/12) UpperHalfPlane.atImInfty (𝓝 (0:ℂ)) := by
    have h := h1.div_const (12:ℂ)
    simpa using h
  show Filter.Tendsto (fun z : ℍ => Derivative.normalizedDerivOfComplex E2 z - (E2 z ^ 2 - E4 z)/12)
    UpperHalfPlane.atImInfty (𝓝 (0:ℂ))
  simpa using D_E2_tendsto_atImInfty.sub h2

theorem ramanujan_E2 :
    Derivative.normalizedDerivOfComplex E2 = fun z : ℍ => (E2 z ^ 2 - E4 z) / 12 := by
  have hslash : ∀ γ : SL(2, ℤ), ramanujanH ∣[(4:ℤ)] γ = ramanujanH :=
    SlashInvariantForm.slash_action_generators_SL2Z ramanujanH_slash_S ramanujanH_slash_T
  obtain ⟨g, hg⟩ := modularForm_of_slash_invariant hslash ramanujanH_mdiff
    ramanujanH_isZeroAtImInfty.isBoundedAtImInfty
  have hcoeff : (UpperHalfPlane.qExpansion 1 g).coeff 0 = 0 := by
    rw [UpperHalfPlane.qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero g one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex g one_mem_strictPeriods_SL)]
    rw [show UpperHalfPlane.valueAtInfty (⇑g) = UpperHalfPlane.valueAtInfty ramanujanH from by rw [hg]]
    exact UpperHalfPlane.IsZeroAtImInfty.valueAtInfty_eq_zero ramanujanH_isZeroAtImInfty
  have hzeroC : ∀ x : CuspForm 𝒮ℒ 4, x = 0 :=
    rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (k := 4) (by norm_num))
  have hgc : ModularForm.toCuspForm g hcoeff = 0 := hzeroC _
  have hgz : (⇑g : ℍ → ℂ) = 0 := by
    ext z
    have hzz := DFunLike.congr_fun hgc z
    simpa [ModularForm.toCuspForm_apply] using hzz
  have hH0 : ramanujanH = 0 := hg.symm.trans hgz
  exact sub_eq_zero.mp hH0

end Work.Modular
