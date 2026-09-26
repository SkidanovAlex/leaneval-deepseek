import Mathlib
import Submission.Work.Residues.ThetaEpt
import Submission.Work.Kernels.LogLambda.LogExtension
import Submission.Work.Kernels.LogLambda.LogLaws
import Submission.Work.Kernels.LogLambda.LambdaLaws
import Submission.Work.Kernels.LogLambda.LogGrowth.Lfun_sub_pi_I_bound
import Submission.Work.Kernels.LogLambda.ThetaLower.ratio_estimate
import Submission.Work.Analysis.DiscreteValues.eq_const_of_isPreconnected

namespace Work.Residues

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups Manifold Modular ModularForm

noncomputable section

/-! ## The expansion of `U = θ₀₀⁴` -/

theorem UFun_expansion :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖Work.Kernels.UFun τ - 1 - 8 * Ept τ‖ ≤ C * ‖Ept τ‖ ^ 2 := by
  obtain ⟨CA, hCA, hA⟩ := theta00Fun_expansion
  refine ⟨4 * CA + 6 * (3 + CA) ^ 2 + 4 * (3 + CA) ^ 3 + (3 + CA) ^ 4 + 1, by positivity, ?_⟩
  intro τ hτ
  have he1 : ‖Ept τ‖ ≤ 1 := le_of_lt (norm_Ept_lt_one τ)
  have he0 : 0 ≤ ‖Ept τ‖ := norm_nonneg _
  have hδ : ‖Work.Kernels.theta00Fun τ - 1 - 2 * Ept τ‖ ≤ CA * ‖Ept τ‖ ^ 2 := by
    have h4 : ‖Ept τ‖ ^ 4 ≤ ‖Ept τ‖ ^ 2 :=
      pow_le_pow_of_le_one he0 he1 (by norm_num : 2 ≤ 4)
    calc ‖Work.Kernels.theta00Fun τ - 1 - 2 * Ept τ‖ ≤ CA * ‖Ept τ‖ ^ 4 := hA τ hτ
      _ ≤ CA * ‖Ept τ‖ ^ 2 := mul_le_mul_of_nonneg_left h4 (le_of_lt hCA)
  have hU : Work.Kernels.UFun τ = (Work.Kernels.theta00Fun τ) ^ 4 := rfl
  rw [hU]
  rw [show Work.Kernels.theta00Fun τ
      = 1 + (2 * Ept τ + (Work.Kernels.theta00Fun τ - 1 - 2 * Ept τ)) by ring]
  set x : ℂ := 2 * Ept τ + (Work.Kernels.theta00Fun τ - 1 - 2 * Ept τ) with hx
  have hxδ : x - 2 * Ept τ = Work.Kernels.theta00Fun τ - 1 - 2 * Ept τ := by rw [hx]; ring
  have hK0 : (0 : ℝ) ≤ 3 + CA := by linarith
  have hxnorm : ‖x‖ ≤ (3 + CA) * ‖Ept τ‖ := by
    have h1 : ‖x‖ ≤ ‖2 * Ept τ‖ + ‖x - 2 * Ept τ‖ := by
      have h := norm_add_le (2 * Ept τ) (x - 2 * Ept τ)
      rw [add_sub_cancel] at h
      exact h
    have h2 : ‖(2 : ℂ) * Ept τ‖ = 2 * ‖Ept τ‖ := by rw [norm_mul, Complex.norm_ofNat]
    have h3 : ‖x - 2 * Ept τ‖ ≤ CA * ‖Ept τ‖ ^ 2 := by rw [hxδ]; exact hδ
    have h4 : CA * ‖Ept τ‖ ^ 2 ≤ CA * ‖Ept τ‖ :=
      mul_le_mul_of_nonneg_left
        (by simpa using pow_le_pow_of_le_one he0 he1 (by norm_num : 1 ≤ 2))
        (le_of_lt hCA)
    have h5 : (2 : ℝ) * ‖Ept τ‖ + CA * ‖Ept τ‖ ≤ (3 + CA) * ‖Ept τ‖ := by
      have : (2 : ℝ) * ‖Ept τ‖ + CA * ‖Ept τ‖ = (2 + CA) * ‖Ept τ‖ := by ring
      rw [this]; apply mul_le_mul_of_nonneg_right (by linarith) he0
    linarith [h1, h2, h3, h4, h5]
  have hkey : (1 + x) ^ 4 - 1 - 8 * Ept τ
      = 4 * (x - 2 * Ept τ) + (6 * x ^ 2 + 4 * x ^ 3 + x ^ 4) := by ring
  rw [hkey]
  have t1 : ‖4 * (x - 2 * Ept τ)‖ ≤ 4 * CA * ‖Ept τ‖ ^ 2 := by
    rw [norm_mul, Complex.norm_ofNat]
    calc 4 * ‖x - 2 * Ept τ‖ ≤ 4 * (CA * ‖Ept τ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (by rw [hxδ]; exact hδ) (by norm_num)
      _ = 4 * CA * ‖Ept τ‖ ^ 2 := by ring
  have hx2 : ‖x‖ ^ 2 ≤ ((3 + CA) * ‖Ept τ‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg x) hxnorm 2
  have t2 : ‖x ^ 2‖ ≤ (3 + CA) ^ 2 * ‖Ept τ‖ ^ 2 := by
    rw [norm_pow]
    calc ‖x‖ ^ 2 ≤ ((3 + CA) * ‖Ept τ‖) ^ 2 := hx2
      _ = (3 + CA) ^ 2 * ‖Ept τ‖ ^ 2 := by ring
  have hx3 : ‖x‖ ^ 3 ≤ ((3 + CA) * ‖Ept τ‖) ^ 3 :=
    pow_le_pow_left₀ (norm_nonneg x) hxnorm 3
  have t3 : ‖x ^ 3‖ ≤ (3 + CA) ^ 3 * ‖Ept τ‖ ^ 2 := by
    rw [norm_pow]
    have he : ‖Ept τ‖ ^ 3 ≤ ‖Ept τ‖ ^ 2 :=
      pow_le_pow_of_le_one he0 he1 (by norm_num : 2 ≤ 3)
    calc ‖x‖ ^ 3 ≤ ((3 + CA) * ‖Ept τ‖) ^ 3 := hx3
      _ = (3 + CA) ^ 3 * ‖Ept τ‖ ^ 3 := by ring
      _ ≤ (3 + CA) ^ 3 * ‖Ept τ‖ ^ 2 := mul_le_mul_of_nonneg_left he (pow_nonneg hK0 3)
  have hx4 : ‖x‖ ^ 4 ≤ ((3 + CA) * ‖Ept τ‖) ^ 4 :=
    pow_le_pow_left₀ (norm_nonneg x) hxnorm 4
  have t4 : ‖x ^ 4‖ ≤ (3 + CA) ^ 4 * ‖Ept τ‖ ^ 2 := by
    rw [norm_pow]
    have he : ‖Ept τ‖ ^ 4 ≤ ‖Ept τ‖ ^ 2 :=
      pow_le_pow_of_le_one he0 he1 (by norm_num : 2 ≤ 4)
    calc ‖x‖ ^ 4 ≤ ((3 + CA) * ‖Ept τ‖) ^ 4 := hx4
      _ = (3 + CA) ^ 4 * ‖Ept τ‖ ^ 4 := by ring
      _ ≤ (3 + CA) ^ 4 * ‖Ept τ‖ ^ 2 := mul_le_mul_of_nonneg_left he (pow_nonneg hK0 4)
  have t5 : ‖6 * x ^ 2‖ ≤ 6 * ((3 + CA) ^ 2 * ‖Ept τ‖ ^ 2) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left t2 (by norm_num)
  have t6 : ‖4 * x ^ 3‖ ≤ 4 * ((3 + CA) ^ 3 * ‖Ept τ‖ ^ 2) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left t3 (by norm_num)
  have tt := norm_add_le (4 * (x - 2 * Ept τ)) (6 * x ^ 2 + 4 * x ^ 3 + x ^ 4)
  have tt2 := norm_add_le (6 * x ^ 2 + 4 * x ^ 3) (x ^ 4)
  have tt3 := norm_add_le (6 * x ^ 2) (4 * x ^ 3)
  have hfin : ‖4 * (x - 2 * Ept τ) + (6 * x ^ 2 + 4 * x ^ 3 + x ^ 4)‖
      ≤ (4 * CA + 6 * (3 + CA) ^ 2 + 4 * (3 + CA) ^ 3 + (3 + CA) ^ 4) * ‖Ept τ‖ ^ 2 := by
    linarith [tt, tt2, tt3, t1, t5, t6, t4]
  nlinarith [hfin, sq_nonneg ‖Ept τ‖, hCA]

/-! ## The expansion of `V = θ₁₀⁴` -/

theorem VFun_expansion :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖Work.Kernels.VFun τ - 16 * Ept τ‖ ≤ C * ‖Ept τ‖ ^ 3 := by
  refine ⟨1280, by norm_num, ?_⟩
  intro τ hτ
  have hy : 0 < (τ : ℂ).im := by simpa using τ.im_pos
  set s : ℂ := jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) / 2 with hs
  have hESQ : ‖Ept τ‖ ^ 2 ≤ 1 / 2 := by
    have hr2 : ‖Ept τ‖ ^ 2 ≤ Real.exp (-(2 * Real.pi)) := norm_Ept_sq_le τ hτ
    have h1 : Real.exp (-(2 * Real.pi)) ≤ 1 / 2 := by
      have h2e : (2 : ℝ) * Real.exp (-(2 * Real.pi)) < 1 := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
        have := Real.add_one_le_exp (2 * Real.pi)
        nlinarith [Real.pi_gt_three]
      linarith
    linarith
  have hr : Real.exp (-(2 * Real.pi * (τ : ℂ).im)) = ‖Ept τ‖ ^ 2 := by
    rw [pow_two, norm_Ept τ, UpperHalfPlane.coe_im, ← Real.exp_add]
    congr 1
    ring
  have hsbound : ‖s - 1‖ ≤ 2 * ‖Ept τ‖ ^ 2 := by
    have h := Work.Kernels.LogLambda.ThetaLower.ratio_estimate (τ : ℂ) hy
    rw [← hs, hr] at h
    have hden : 0 < 1 - ‖Ept τ‖ ^ 2 := by linarith
    rw [le_div_iff₀ hden] at h
    nlinarith
  have hs_norm : ‖s‖ ≤ 3 := by
    have h1 : ‖s‖ ≤ ‖s - 1‖ + 1 := by
      have h := norm_add_le (s - 1) 1
      rw [sub_add_cancel] at h
      simpa using h
    have h2 : ‖Ept τ‖ ^ 2 ≤ 1 := by nlinarith [norm_Ept_lt_one τ, norm_nonneg (Ept τ)]
    nlinarith
  have hexp4 : (Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4)) ^ 4 = Ept τ := by
    rw [← Complex.exp_nat_mul, Ept]
    congr 1
    ring
  have hV : Work.Kernels.VFun τ = Ept τ * (2 * s) ^ 4 := by
    rw [show Work.Kernels.VFun τ
        = (Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4)
            * jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)) ^ 4 from rfl,
      mul_pow, hexp4]
    have hj : jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) = 2 * s := by rw [hs]; ring
    rw [hj]
  rw [hV]
  have hkey : Ept τ * (2 * s) ^ 4 - 16 * Ept τ = 16 * Ept τ * (s ^ 4 - 1) := by ring
  rw [hkey, norm_mul, norm_mul, Complex.norm_ofNat]
  have hpoly : ‖s ^ 3 + s ^ 2 + s + 1‖ ≤ 40 := by
    have h3 : ‖s ^ 3‖ ≤ 27 := by
      rw [norm_pow]
      calc ‖s‖ ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ (norm_nonneg s) hs_norm 3
        _ = 27 := by norm_num
    have h2 : ‖s ^ 2‖ ≤ 9 := by
      rw [norm_pow]
      calc ‖s‖ ^ 2 ≤ 3 ^ 2 := pow_le_pow_left₀ (norm_nonneg s) hs_norm 2
        _ = 9 := by norm_num
    have h0 : ‖(1 : ℂ)‖ = 1 := norm_one
    calc ‖s ^ 3 + s ^ 2 + s + 1‖ ≤ ‖s ^ 3‖ + ‖s ^ 2‖ + ‖s‖ + 1 := by
          have a := norm_add_le (s ^ 3 + s ^ 2 + s) 1
          have b := norm_add_le (s ^ 3 + s ^ 2) s
          have c := norm_add_le (s ^ 3) (s ^ 2)
          rw [h0] at a
          linarith
      _ ≤ 27 + 9 + 3 + 1 := by linarith
      _ = 40 := by norm_num
  have hs4 : ‖s ^ 4 - 1‖ ≤ 40 * ‖s - 1‖ := by
    have hfac : s ^ 4 - 1 = (s - 1) * (s ^ 3 + s ^ 2 + s + 1) := by ring
    rw [hfac, norm_mul]
    calc ‖s - 1‖ * ‖s ^ 3 + s ^ 2 + s + 1‖ ≤ ‖s - 1‖ * 40 :=
          mul_le_mul_of_nonneg_left hpoly (norm_nonneg _)
      _ = 40 * ‖s - 1‖ := by ring
  have hE : 0 ≤ ‖Ept τ‖ := norm_nonneg _
  calc 16 * ‖Ept τ‖ * ‖s ^ 4 - 1‖
      ≤ 16 * ‖Ept τ‖ * (40 * ‖s - 1‖) := by nlinarith
    _ ≤ 16 * ‖Ept τ‖ * (40 * (2 * ‖Ept τ‖ ^ 2)) := by nlinarith
    _ = 1280 * ‖Ept τ‖ ^ 3 := by ring

/-! ## The transformation law of `Λ_S` -/

lemma thetaC00_add_one (z : ℂ) :
    Work.Kernels.LogLambda.thetaC00 (z + 1) = Work.Kernels.LogLambda.thetaC01 z :=
  (Work.Kernels.LogLambda.thetaC01_eq_thetaC00_add_one z).symm

lemma thetaC01_add_one (z : ℂ) :
    Work.Kernels.LogLambda.thetaC01 (z + 1) = Work.Kernels.LogLambda.thetaC00 z := by
  rw [Work.Kernels.LogLambda.thetaC01_eq_thetaC00_add_one (z + 1)]
  show jacobiTheta (z + 1 + 1) = jacobiTheta z
  rw [show z + 1 + 1 = 2 + z by ring, jacobiTheta_two_add]

lemma LamS_add_one {z : ℂ} (hz : 1 / 2 < z.im) :
    Work.Kernels.LogLambda.LamS (z + 1) = -Work.Kernels.LogLambda.LamS z := by
  rw [Work.Kernels.LogLambda.LamS, Work.Kernels.LogLambda.LamS,
    thetaC01_add_one z, thetaC00_add_one z]
  ring

/-! ## Identification of `𝓛_S` with `Λ_S` -/

theorem LogLambdaData_LS_eq_LamS (ℓ : Work.Kernels.LogLambdaData) :
    ∀ τ : ℍ, 1 / 2 < τ.im → ℓ.L_S τ = Work.Kernels.LogLambda.LamS (τ : ℂ) := by
  set W := Work.Kernels.LogLambda.W with hW
  let F : ℂ → ℂ := fun z =>
    if h : (1 / 2 : ℝ) < z.im then
      ℓ.L_S ⟨z, lt_trans (by norm_num) h⟩ - Work.Kernels.LogLambda.LamS z
    else 0
  have hF_apply : ∀ z (hz : (1 / 2 : ℝ) < z.im),
      F z = ℓ.L_S ⟨z, lt_trans (by norm_num) hz⟩ - Work.Kernels.LogLambda.LamS z := by
    intro z hz
    simp only [F]
    rw [dif_pos hz]
  have hcont : ContinuousOn F W := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hphi : Continuous (fun w : W =>
        ℓ.L_S ⟨w.1, lt_trans (by norm_num) w.2⟩ - Work.Kernels.LogLambda.LamS w.1) :=
      (((MDifferentiable.continuous ℓ.holo_S).comp
          (Continuous.upperHalfPlaneMk continuous_subtype_val
            (fun w : W => lt_trans (by norm_num) w.2))).sub
        (continuousOn_iff_continuous_domRestrict.mp
          Work.Kernels.LogLambda.continuousOn_LamS_W))
    have hEq : W.domRestrict F = fun w : W =>
        ℓ.L_S ⟨w.1, lt_trans (by norm_num) w.2⟩ - Work.Kernels.LogLambda.LamS w.1 := by
      funext w
      show F w.1 = _
      rw [hF_apply w.1 w.2]
    rw [hEq]
    exact hphi
  have hval : ∀ z ∈ W, ∃ n : ℤ, F z = n * (2 * Real.pi * Complex.I) := by
    intro z hz
    have hzpos : 0 < z.im := lt_trans (by norm_num) hz
    have hexp : Complex.exp (F z) = 1 := by
      rw [hF_apply z hz, Complex.exp_sub, ℓ.exp_L_S ⟨z, lt_trans (by norm_num) hz⟩,
        Work.Kernels.LogLambda.exp_LamS_W z hz]
      exact div_self (Work.Kernels.LogLambda.lamSC_ne_zero hzpos)
    exact Complex.exp_eq_one_iff.mp hexp
  have hbase : (2 * Complex.I : ℂ) ∈ W := by
    show (1 / 2 : ℝ) < (2 * Complex.I : ℂ).im
    rw [Complex.mul_I_im]
    norm_num
  have hconst := Work.Analysis.DiscreteValues.eq_const_of_isPreconnected
    Work.Kernels.LogLambda.isPreconnected_W hcont hval hbase
  have hF_T : ∀ z ∈ W, F (z + 1) = - F z := by
    intro z hz
    have hz1 : (1 / 2 : ℝ) < (z + 1).im := by
      simp only [Complex.add_im, Complex.one_im, add_zero]; exact hz
    rw [hF_apply (z + 1) hz1, hF_apply z hz]
    set τ := (⟨z, lt_trans (by norm_num) hz⟩ : ℍ) with hτdef
    set τ₁ := (⟨z + 1, lt_trans (by norm_num) hz1⟩ : ℍ) with hτ1def
    have hτ1_eq : τ₁ = ModularGroup.T • τ := by
      apply UpperHalfPlane.ext
      rw [Work.Kernels.coe_T_smul]
    have hslash : ℓ.L_S τ₁ = - ℓ.L_S τ := by
      rw [hτ1_eq]
      have h := Work.Kernels.slash_apply' ℓ.L_S 0 ModularGroup.T τ
      have h0 := ℓ.slash_T_S τ
      rw [h] at h0
      simpa using h0
    rw [hslash, LamS_add_one hz]
    ring
  have hF2I : F (2 * Complex.I) = 0 := by
    have h2I1 : (2 * Complex.I + 1 : ℂ) ∈ W := by
      show (1 / 2 : ℝ) < (2 * Complex.I + 1 : ℂ).im
      rw [Complex.add_im, Complex.mul_I_im, Complex.one_im, add_zero]
      norm_num
    have e1 : F (2 * Complex.I + 1) = F (2 * Complex.I) := hconst _ h2I1
    have e2 : F (2 * Complex.I + 1) = - F (2 * Complex.I) := hF_T _ hbase
    have hkey : F (2 * Complex.I) = - F (2 * Complex.I) := e1.symm.trans e2
    rw [eq_neg_iff_add_eq_zero] at hkey
    exact add_self_eq_zero.mp hkey
  intro τ hτ
  have hzW : (τ : ℂ) ∈ W := by
    show (1 / 2 : ℝ) < (τ : ℂ).im
    rw [UpperHalfPlane.coe_im]
    exact hτ
  have hc := hconst (τ : ℂ) hzW
  rw [hF_apply (τ : ℂ) hτ, hF2I] at hc
  have hgoal : ℓ.L_S (⟨(τ : ℂ), lt_trans (by norm_num) hτ⟩ : ℍ)
      = Work.Kernels.LogLambda.LamS (τ : ℂ) := sub_eq_zero.mp hc
  have hτeq : (⟨(τ : ℂ), lt_trans (by norm_num) hτ⟩ : ℍ) = τ := by
    apply UpperHalfPlane.ext
    rfl
  rwa [hτeq] at hgoal

end

end Work.Residues
