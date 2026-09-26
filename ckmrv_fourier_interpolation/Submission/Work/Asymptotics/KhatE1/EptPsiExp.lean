import Mathlib
import Submission.Work.Asymptotics.KhatE1.EptThetaExp
import Submission.Work.Asymptotics.KhatE1.EptUpgrade
import Submission.Work.Asymptotics.KhatE1.EptSmallDefs
import Submission.Work.Residues.LamSExpansion
import Submission.Work.Residues.ThetaAux
import Submission.Work.Rigidity.boundedAtImInfty_of_periodic_inP
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Kernels.KernelFacts.psi2_T2

/-!
# The first-order cusp expansions of `𝓛_S`, `𝓛 - 𝓛_S/2`, `ψ₂` and `ψ₄`
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle
open Filter
open scoped Topology

noncomputable section

/-! ## The `T`-translation laws -/

private lemma jFun_T (z : ℂ) : Work.Kernels.jFun ModularGroup.T z = 1 := by
  rw [Work.Kernels.jFun_apply]
  have h0 : (ModularGroup.T : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 = 0 := by decide
  have h1 : (ModularGroup.T : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1 = 1 := by decide
  rw [h0, h1]; simp

private lemma T_smul_eq_vadd_one (τ : UpperHalfPlane) : ModularGroup.T • τ = (1 : ℝ) +ᵥ τ := by
  simpa using UpperHalfPlane.modular_T_zpow_smul τ (1 : ℤ)

lemma L_vadd_one (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    ℓ.L ((1 : ℝ) +ᵥ τ) = ℓ.L τ - ℓ.L_S τ + (Real.pi : ℂ) * Complex.I := by
  have h := ℓ.slash_T τ
  rw [Work.Kernels.slash_apply', jFun_T, T_smul_eq_vadd_one τ] at h
  simpa using h

lemma LS_vadd_one (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    ℓ.L_S ((1 : ℝ) +ᵥ τ) = -ℓ.L_S τ := by
  have h := ℓ.slash_T_S τ
  rw [Work.Kernels.slash_apply', jFun_T, T_smul_eq_vadd_one τ] at h
  simpa using h

lemma qParamFun_vadd_one (τ : UpperHalfPlane) :
    Work.Kernels.qParamFun ((1 : ℝ) +ᵥ τ) = Work.Kernels.qParamFun τ := by
  have hcoe : (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) = (τ : ℂ) + 1 := by
    push_cast [UpperHalfPlane.coe_vadd]; ring
  rw [Work.Kernels.qParamFun, Work.Kernels.qParamFun, hcoe]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) + 1)
      = 2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) + 2 * (Real.pi : ℂ) * Complex.I by ring]
  rw [Complex.exp_add]
  have h2 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I) = 1 := by
    have h : (2 * (Real.pi : ℂ) * Complex.I) = Complex.I * ((2 * Real.pi : ℝ) : ℂ) := by
      push_cast; ring
    rw [show (2 * (Real.pi : ℂ) * Complex.I) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.exp_ofReal_mul_I]
    simp [Real.cos_two_pi, Real.sin_two_pi]
  rw [h2, mul_one]

/-! ## `𝓛_S = -16 Ept + O(Ept³)` -/

lemma isSmall_LSRem (ℓ : Work.Kernels.LogLambdaData) :
    IsSmall (fun τ : UpperHalfPlane => ℓ.L_S τ + 16 * Work.Residues.Ept τ) 3 := by
  obtain ⟨C, hC, hb⟩ := Work.Residues.LamSExpansion
  refine ⟨max C 1, 0, by positivity, le_rfl, fun τ hτ => ?_⟩
  rw [Real.rpow_zero, mul_one]
  change ‖ℓ.L_S τ + 16 * Work.Residues.Ept τ‖ ≤ max C 1 * ‖Work.Residues.Ept τ‖ ^ 3
  have h1 : ℓ.L_S τ = Work.Kernels.LogLambda.LamS (τ : ℂ) :=
    Work.Residues.LogLambdaData_LS_eq_LamS ℓ τ (by linarith)
  rw [h1]
  calc ‖Work.Kernels.LogLambda.LamS (τ : ℂ) + 16 * Work.Residues.Ept τ‖
      ≤ C * ‖Work.Residues.Ept τ‖ ^ 3 := hb τ hτ
    _ ≤ max C 1 * ‖Work.Residues.Ept τ‖ ^ 3 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-! ## `InP` of the basic atoms -/

lemma inP_Ept : Work.Kernels.InP Work.Residues.Ept := by
  refine ⟨?_, ?_⟩
  · exact Complex.differentiable_exp.comp_mdifferentiable
      (mdifferentiable_const.mul Work.Kernels.KernelGrowth.InP_coe.1)
  · refine Work.Kernels.ModerateGrowthOn.of_bound (C := 1) (fun τ _ => ?_)
    rw [Work.Residues.norm_Ept]
    exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, τ.im_pos])

lemma inP_qParamFun : Work.Kernels.InP Work.Kernels.qParamFun := by
  refine ⟨?_, ?_⟩
  · have hlin : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
        (fun τ : UpperHalfPlane => (2 * (Real.pi : ℂ) * Complex.I) * (τ : ℂ)) :=
      mdifferentiable_const.mul Work.Kernels.KernelGrowth.InP_coe.1
    exact Complex.differentiable_exp.comp_mdifferentiable hlin
  · refine Work.Kernels.ModerateGrowthOn.of_bound (C := 1) (fun τ _ => ?_)
    rw [Work.Asymptotics.qParamFun_eq_qParam, Function.Periodic.norm_qParam]
    simp only [div_one]
    rw [Real.exp_le_one_iff]
    have him : (0:ℝ) < (τ : ℂ).im := by simpa using τ.im_pos
    nlinarith [Real.pi_pos, him]

/-! ## The periodicity of `2ρ - 𝓛_S - 24q` -/

/-- `2(𝓛 - πiτ - cuspC) - 𝓛_S - 24q`, the even part of `2(𝓛-πiτ-cuspC)`. -/
noncomputable def LsubPeriodic (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  2 * (ℓ.L τ - (Real.pi : ℂ) * Complex.I * (τ : ℂ) - Work.Asymptotics.Compact.cuspC ℓ)
    - ℓ.L_S τ - 24 * Work.Kernels.qParamFun τ

lemma LsubPeriodic_vadd_one (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    LsubPeriodic ℓ ((1 : ℝ) +ᵥ τ) = LsubPeriodic ℓ τ := by
  simp only [LsubPeriodic, L_vadd_one ℓ τ, LS_vadd_one ℓ τ, qParamFun_vadd_one τ]
  push_cast [UpperHalfPlane.coe_vadd]
  ring

lemma inP_LsubPeriodic (ℓ : Work.Kernels.LogLambdaData) : Work.Kernels.InP (LsubPeriodic ℓ) := by
  have hcoe : Work.Kernels.InP (fun τ : UpperHalfPlane => (τ : ℂ)) :=
    Work.Kernels.KernelGrowth.InP_coe
  have hL : Work.Kernels.InP (fun τ : UpperHalfPlane => ℓ.L τ) := ⟨ℓ.holo, ℓ.memP⟩
  have hLS : Work.Kernels.InP (fun τ : UpperHalfPlane => ℓ.L_S τ) := ⟨ℓ.holo_S, ℓ.memP_S⟩
  have hlin : Work.Kernels.InP (fun τ : UpperHalfPlane =>
      (Real.pi : ℂ) * Complex.I * (τ : ℂ)) :=
    hcoe.const_mul ((Real.pi : ℂ) * Complex.I)
  exact (((((hL.sub hlin).sub (Work.Kernels.InP.const (Work.Asymptotics.Compact.cuspC ℓ))).const_mul
    2).sub hLS).sub (inP_qParamFun.const_mul (24 : ℂ)))

lemma isSmall_LsubPeriodic_three (ℓ : Work.Kernels.LogLambdaData) :
    IsSmall (LsubPeriodic ℓ) 3 := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.Compact.cuspC_spec ℓ
  have hρ : IsSmall (fun τ : UpperHalfPlane => ℓ.L τ
      - ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ
          - 8 * Work.Residues.Ept τ + 12 * Work.Residues.Ept τ ^ 2)) 3 := by
    refine ⟨max C 1, 0, by positivity, le_rfl, fun τ hτ => ?_⟩
    rw [Real.rpow_zero, mul_one]
    change ‖ℓ.L τ - ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ
        - 8 * Work.Residues.Ept τ + 12 * Work.Residues.Ept τ ^ 2)‖
      ≤ max C 1 * ‖Work.Residues.Ept τ‖ ^ 3
    calc ‖ℓ.L τ - ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ
          - 8 * Work.Residues.Ept τ + 12 * Work.Residues.Ept τ ^ 2)‖
        ≤ C * ‖Work.Residues.Ept τ‖ ^ 3 := hb τ hτ
      _ ≤ max C 1 * ‖Work.Residues.Ept τ‖ ^ 3 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hLS := isSmall_LSRem ℓ
  have h2 : IsSmall (fun τ : UpperHalfPlane =>
      2 * (ℓ.L τ - ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ
            - 8 * Work.Residues.Ept τ + 12 * Work.Residues.Ept τ ^ 2))
        - (ℓ.L_S τ + 16 * Work.Residues.Ept τ)) 3 :=
    (hρ.const_mul 2).sub hLS
  refine h2.congr (fun τ => ?_)
  simp only [LsubPeriodic]
  rw [← ept_sq_apply τ]
  ring

lemma isSmall_LsubPeriodic (ℓ : Work.Kernels.LogLambdaData) : IsSmall (LsubPeriodic ℓ) 4 := by
  obtain ⟨C, N, hC, hN, hb⟩ := isSmall_LsubPeriodic_three ℓ
  have hbdd := Work.Rigidity.boundedAtImInfty_of_periodic_inP (inP_LsubPeriodic ℓ)
    (LsubPeriodic_vadd_one ℓ)
  have hper : Function.Periodic (fun w : ℂ => LsubPeriodic ℓ (UpperHalfPlane.ofComplex w)) 1 := by
    intro z
    simp only [Function.comp_apply]
    by_cases hz : 0 < z.im
    · have hz' : 0 < (z + 1).im := by simpa using hz
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz',
        UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      have hcoe : (⟨z + 1, hz'⟩ : ℍ) = (1 : ℝ) +ᵥ (⟨z, hz⟩ : ℍ) := by
        apply UpperHalfPlane.coe_inj.mp
        rw [UpperHalfPlane.coe_vadd]
        push_cast
        ring
      rw [hcoe, LsubPeriodic_vadd_one]
    · have hzle : z.im ≤ 0 := not_lt.mp hz
      have hz' : (z + 1).im ≤ 0 := by simpa using hzle
      rw [UpperHalfPlane.ofComplex_apply_of_im_nonpos hz',
        UpperHalfPlane.ofComplex_apply_of_im_nonpos hzle]
  obtain ⟨A, B, hB, hbound⟩ :=
    IsSmall.periodic_decay hper (inP_LsubPeriodic ℓ) hbdd ⟨C, N, hC, hN, hb⟩
  refine ⟨max B (C * Real.exp (Real.pi * A) + 1), max N 0, ?_, le_max_right _ _, fun τ hτ => ?_⟩
  · have h2 : (0:ℝ) < C * Real.exp (Real.pi * A) + 1 := by positivity
    exact lt_of_lt_of_le h2 (le_max_right _ _)
  have hsc : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hscN : (Work.Kernels.scale τ) ^ N ≤ (Work.Kernels.scale τ) ^ max N 0 :=
    Real.rpow_le_rpow_of_exponent_le hsc (le_max_left _ _)
  have hsc1 : (1:ℝ) ≤ (Work.Kernels.scale τ) ^ max N 0 :=
    Real.one_le_rpow hsc (le_max_right _ _)
  rcases le_or_gt A τ.im with hA | hA
  · have h := hbound τ hA
    have h4 : ‖Work.Kernels.qParamFun τ‖ ^ ((3 + 1) / 2) = ‖Work.Residues.Ept τ‖ ^ 4 := by
      rw [show (3 + 1) / 2 = 2 by norm_num, norm_qParamFun_eq]
      ring
    rw [h4] at h
    have hE4 : (0:ℝ) ≤ ‖Work.Residues.Ept τ‖ ^ 4 := by positivity
    calc ‖LsubPeriodic ℓ τ‖ ≤ B * ‖Work.Residues.Ept τ‖ ^ 4 := h
      _ ≤ B * ((Work.Kernels.scale τ) ^ max N 0 * ‖Work.Residues.Ept τ‖ ^ 4) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hE4 hsc1) hB
      _ = B * (Work.Kernels.scale τ) ^ max N 0 * ‖Work.Residues.Ept τ‖ ^ 4 := by ring
      _ ≤ (max B (C * Real.exp (Real.pi * A) + 1)) * (Work.Kernels.scale τ) ^ max N 0
            * ‖Work.Residues.Ept τ‖ ^ 4 := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
            (by positivity)
          exact le_max_left _ _
  · have h := hb τ hτ
    have hE3 : ‖Work.Residues.Ept τ‖ ^ 3
        ≤ Real.exp (Real.pi * A) * ‖Work.Residues.Ept τ‖ ^ 4 := by
      have h1 : (1:ℝ) ≤ Real.exp (Real.pi * A) * ‖Work.Residues.Ept τ‖ := by
        have hA' : 0 < A - τ.im := by linarith
        rw [Work.Residues.norm_Ept, ← Real.exp_add]
        exact Real.one_le_exp (by nlinarith [Real.pi_pos, hA'])
      calc ‖Work.Residues.Ept τ‖ ^ 3 = ‖Work.Residues.Ept τ‖ ^ 3 * 1 := by ring
        _ ≤ ‖Work.Residues.Ept τ‖ ^ 3 * (Real.exp (Real.pi * A) * ‖Work.Residues.Ept τ‖) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = Real.exp (Real.pi * A) * ‖Work.Residues.Ept τ‖ ^ 4 := by ring
    have hE4 : (0:ℝ) ≤ ‖Work.Residues.Ept τ‖ ^ 4 := by positivity
    calc ‖LsubPeriodic ℓ τ‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Residues.Ept τ‖ ^ 3 := h
      _ ≤ C * (Work.Kernels.scale τ) ^ max N 0 * ‖Work.Residues.Ept τ‖ ^ 3 := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscN hC.le) (by positivity)
      _ ≤ C * (Work.Kernels.scale τ) ^ max N 0
            * (Real.exp (Real.pi * A) * ‖Work.Residues.Ept τ‖ ^ 4) :=
          mul_le_mul_of_nonneg_left hE3 (by positivity)
      _ = (C * Real.exp (Real.pi * A)) * (Work.Kernels.scale τ) ^ max N 0
            * ‖Work.Residues.Ept τ‖ ^ 4 := by ring
      _ ≤ max B (C * Real.exp (Real.pi * A) + 1) * (Work.Kernels.scale τ) ^ max N 0
            * ‖Work.Residues.Ept τ‖ ^ 4 := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
            (by positivity)
          have h2 : (0:ℝ) ≤ C * Real.exp (Real.pi * A) := by positivity
          linarith [le_max_right B (C * Real.exp (Real.pi * A) + 1)]

/-! ## The `psi` expansions -/

lemma isSmall_coe : IsSmall (fun τ : UpperHalfPlane => (τ : ℂ)) 0 := by
  refine ⟨1, 1, one_pos, by norm_num, fun τ _ => ?_⟩
  simpa using Work.Kernels.coe_norm_le_scale τ

lemma isSmall_piItau (ℓ : Work.Kernels.LogLambdaData) :
    IsSmall (fun τ : UpperHalfPlane =>
      (Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) 0 :=
  ((isSmall_coe.const_mul ((Real.pi : ℂ) * Complex.I)).add
    (IsSmall.const _)).mono_of 0 (by decide)

/-- The `E(z)²`-remainder of `ψ₂`. -/
noncomputable def xi2Rem (τ : UpperHalfPlane) : ℂ :=
  (Work.Kernels.UFun τ + Work.Kernels.WFun τ) - (2 + 48 * Work.Kernels.qParamFun τ)

/-- The `E(z)²`-remainder of `ψ₄`. -/
noncomputable def xi4Rem (τ : UpperHalfPlane) : ℂ :=
  Work.Kernels.xi4Fun τ - (2 - 288 * Work.Kernels.qParamFun τ)

/-- The remainder of `𝓛 - 𝓛_S/2`. -/
noncomputable def LplusRem (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (ℓ.L τ - ℓ.L_S τ / 2)
    - ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ
        + 12 * Work.Kernels.qParamFun τ)

/-- The remainder of `V · 𝓛_S`. -/
noncomputable def VLSRem (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  Work.Kernels.VFun τ * ℓ.L_S τ + 256 * Work.Kernels.qParamFun τ

/-- The remainder of `𝓛_S`. -/
noncomputable def LSRemK (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  ℓ.L_S τ + 16 * Work.Residues.Ept τ

/-- The remainder of `V`. -/
noncomputable def VRem (τ : UpperHalfPlane) : ℂ :=
  Work.Kernels.VFun τ - (16 * Work.Residues.Ept τ + 64 * Work.Residues.Ept τ ^ 3)

/-- The first-order model of `ψ₂`. -/
noncomputable def psi2Model (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
    + (48 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) + 408)
        * Work.Kernels.qParamFun τ

/-- The first-order model of `ψ₄`. -/
noncomputable def psi4Model (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
    - (288 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) + 744)
        * Work.Kernels.qParamFun τ

lemma isSmall_xi2Rem : IsSmall xi2Rem 4 := isSmall_xi2

lemma isSmall_xi4Rem : IsSmall xi4Rem 4 := isSmall_xi4

lemma isSmall_LplusRem (ℓ : Work.Kernels.LogLambdaData) : IsSmall (LplusRem ℓ) 4 := by
  have h := (isSmall_LsubPeriodic ℓ).const_mul ((1/2 : ℂ))
  refine h.congr (fun τ => ?_)
  simp only [LsubPeriodic, LplusRem]; ring

lemma isSmall_LSRem' (ℓ : Work.Kernels.LogLambdaData) : IsSmall (LSRemK ℓ) 3 :=
  isSmall_LSRem ℓ

lemma isSmall_VRem' : IsSmall VRem 4 := isSmall_VRem

lemma isSmall_vModel_one : IsSmall vModel 1 := by
  have h := (isSmall_ept.const_mul 16).add ((isSmall_ept.pow 3).const_mul 64 |>.mono_of 1 (by decide))
  refine h.mono_of 1 (by decide) |>.congr (fun τ => ?_)
  simp only [vModel]

lemma isSmall_VLSRem (ℓ : Work.Kernels.LogLambdaData) : IsSmall (VLSRem ℓ) 4 := by
  have hδ := isSmall_LSRem' ℓ
  have hV := isSmall_VRem'
  have hv := isSmall_vModel
  have h1 : IsSmall (fun τ : UpperHalfPlane => -1024 * Work.Residues.Ept τ ^ 4) 4 :=
    (isSmall_ept.pow 4).const_mul (-1024)
  have hv1 : IsSmall vModel 1 := isSmall_vModel_one
  have h2 : IsSmall (fun τ : UpperHalfPlane => vModel τ * LSRemK ℓ τ) 4 :=
    (hv1.mul hδ).mono_of 4 (by decide)
  have h3 : IsSmall (fun τ : UpperHalfPlane => (16:ℂ) * Work.Residues.Ept τ * VRem τ) 4 := by
    refine ((isSmall_ept.const_mul 16).mul hV).mono_of 4 (by decide) |>.congr (fun τ => by ring)
  have h4 : IsSmall (fun τ : UpperHalfPlane => VRem τ * LSRemK ℓ τ) 4 :=
    (hV.mul hδ).mono_of 4 (by decide)
  have hcomb : IsSmall (fun τ : UpperHalfPlane =>
      -1024 * Work.Residues.Ept τ ^ 4 + vModel τ * LSRemK ℓ τ
        - 16 * Work.Residues.Ept τ * VRem τ + VRem τ * LSRemK ℓ τ) 4 :=
    ((h1.add h2).sub h3).add h4
  refine hcomb.congr (fun τ => ?_)
  simp only [VLSRem, VRem, LSRemK, vModel]
  rw [← ept_sq_apply τ]
  ring

lemma isSmall_psi2Rem (ℓ : Work.Kernels.LogLambdaData) :
    IsSmall (fun τ : UpperHalfPlane => Work.Kernels.psi2 ℓ τ - psi2Model ℓ τ) 4 := by
  have hξ := isSmall_xi2Rem
  have hL := isSmall_LplusRem ℓ
  have hV := isSmall_VLSRem ℓ
  have hX := isSmall_piItau ℓ
  have hq := isSmall_qParam
  have hcomb : IsSmall (fun τ : UpperHalfPlane =>
      576 * Work.Kernels.qParamFun τ ^ 2 + xi2Rem τ
          * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
        + 12 * Work.Kernels.qParamFun τ * xi2Rem τ + 2 * LplusRem ℓ τ
        + 48 * Work.Kernels.qParamFun τ * LplusRem ℓ τ + xi2Rem τ * LplusRem ℓ τ
        - (3/2) * VLSRem ℓ τ) 4 := by
    have h1 : IsSmall (fun τ : UpperHalfPlane => 576 * Work.Kernels.qParamFun τ ^ 2) 4 :=
      (hq.pow 2).const_mul 576 |>.mono_of 4 (by decide)
    have h2 : IsSmall (fun τ : UpperHalfPlane => xi2Rem τ
        * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)) 4 :=
      (hξ.mul hX).mono_of 4 (by decide)
    have h3 : IsSmall (fun τ : UpperHalfPlane => 12 * Work.Kernels.qParamFun τ * xi2Rem τ) 4 := by
      refine ((hq.const_mul 12).mul hξ).mono_of 4 (by decide) |>.congr (fun τ => by ring)
    have h4 : IsSmall (fun τ : UpperHalfPlane => 2 * LplusRem ℓ τ) 4 := hL.const_mul 2
    have h5 : IsSmall (fun τ : UpperHalfPlane => 48 * Work.Kernels.qParamFun τ * LplusRem ℓ τ) 4 := by
      refine ((hq.const_mul 48).mul hL).mono_of 4 (by decide) |>.congr (fun τ => by ring)
    have h6 : IsSmall (fun τ : UpperHalfPlane => xi2Rem τ * LplusRem ℓ τ) 4 :=
      (hξ.mul hL).mono_of 4 (by decide)
    have h7 : IsSmall (fun τ : UpperHalfPlane => - (3/2) * VLSRem ℓ τ) 4 :=
      hV.const_mul (-(3/2))
    have hsum : IsSmall (fun τ : UpperHalfPlane =>
        (576 * Work.Kernels.qParamFun τ ^ 2 + xi2Rem τ
            * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
          + 12 * Work.Kernels.qParamFun τ * xi2Rem τ + 2 * LplusRem ℓ τ
          + 48 * Work.Kernels.qParamFun τ * LplusRem ℓ τ + xi2Rem τ * LplusRem ℓ τ)
          + (- (3/2) * VLSRem ℓ τ)) 4 :=
      (((((h1.add h2).add h3).add h4).add h5).add h6).add h7
    refine hsum.congr (fun τ => ?_)
    ring
  refine hcomb.congr (fun τ => ?_)
  -- the pointwise identity
  unfold Work.Kernels.psi2 Work.Kernels.xi2Fun
  rw [Work.Kernels.KernelFacts.xi2Fun_slash_S]
  simp only [psi2Model, xi2Rem, LplusRem, VLSRem, LSRemK, VRem, vModel]
  rw [Work.Kernels.TildeFacts.theta_quartic τ, ← ept_sq_apply τ]
  ring

lemma isSmall_psi4Rem (ℓ : Work.Kernels.LogLambdaData) :
    IsSmall (fun τ : UpperHalfPlane => Work.Kernels.psi4 ℓ τ - psi4Model ℓ τ) 4 := by
  have hξ2 := isSmall_xi2Rem
  have hξ4 := isSmall_xi4Rem
  have hL := isSmall_LplusRem ℓ
  have hV := isSmall_VLSRem ℓ
  have hX := isSmall_piItau ℓ
  have hq := isSmall_qParam
  have hcomb : IsSmall (fun τ : UpperHalfPlane =>
      -21888 * Work.Kernels.qParamFun τ ^ 2 + xi4Rem τ
          * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
        + 12 * Work.Kernels.qParamFun τ * xi4Rem τ + 2 * LplusRem ℓ τ
        - 288 * Work.Kernels.qParamFun τ * LplusRem ℓ τ + xi4Rem τ * LplusRem ℓ τ
        + 3 * VLSRem ℓ τ - 384 * Work.Kernels.qParamFun τ * xi2Rem τ
        + 72 * Work.Kernels.qParamFun τ * VLSRem ℓ τ
        + (3/2) * VLSRem ℓ τ * xi2Rem τ) 4 := by
    have h1 : IsSmall (fun τ : UpperHalfPlane => -21888 * Work.Kernels.qParamFun τ ^ 2) 4 := by
      refine ((hq.pow 2).const_mul (-21888)).mono_of 4 (by decide) |>.congr (fun τ => by ring)
    have h2 : IsSmall (fun τ : UpperHalfPlane => xi4Rem τ
        * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)) 4 :=
      (hξ4.mul hX).mono_of 4 (by decide)
    have h3 : IsSmall (fun τ : UpperHalfPlane => 12 * Work.Kernels.qParamFun τ * xi4Rem τ) 4 := by
      refine ((hq.const_mul 12).mul hξ4).mono_of 4 (by decide) |>.congr (fun τ => by ring)
    have h4 : IsSmall (fun τ : UpperHalfPlane => 2 * LplusRem ℓ τ) 4 := hL.const_mul 2
    have h5 : IsSmall (fun τ : UpperHalfPlane => 288 * Work.Kernels.qParamFun τ
        * LplusRem ℓ τ) 4 := by
      refine ((hq.const_mul 288).mul hL).mono_of 4 (by decide) |>.congr (fun τ => by ring)
    have h6 : IsSmall (fun τ : UpperHalfPlane => xi4Rem τ * LplusRem ℓ τ) 4 :=
      (hξ4.mul hL).mono_of 4 (by decide)
    have h7 : IsSmall (fun τ : UpperHalfPlane => 3 * VLSRem ℓ τ) 4 := hV.const_mul 3
    have h8 : IsSmall (fun τ : UpperHalfPlane => 384 * Work.Kernels.qParamFun τ
        * xi2Rem τ) 4 := by
      refine ((hq.const_mul 384).mul hξ2).mono_of 4 (by decide) |>.congr (fun τ => by ring)
    have h9 : IsSmall (fun τ : UpperHalfPlane => 72 * Work.Kernels.qParamFun τ
        * VLSRem ℓ τ) 4 := by
      refine ((hq.const_mul 72).mul hV).mono_of 4 (by decide) |>.congr (fun τ => by ring)
    have h10 : IsSmall (fun τ : UpperHalfPlane => (3/2) * VLSRem ℓ τ * xi2Rem τ) 4 := by
      refine ((hV.const_mul (3/2)).mul hξ2).mono_of 4 (by decide) |>.congr (fun τ => by ring)
    refine ((((((((h1.add h2).add h3).add h4).sub h5).add h6).add h7).sub h8).add h9).add h10 |>.congr
      (fun τ => ?_)
    ring
  refine hcomb.congr (fun τ => ?_)
  simp only [Work.Kernels.psi4]
  rw [Work.Kernels.KernelFacts.xi4S_apply]
  simp only [psi4Model, xi4Rem, xi2Rem, Work.Kernels.xi4Fun, LplusRem, VLSRem]
  rw [Work.Kernels.TildeFacts.theta_quartic τ, ← ept_sq_apply τ]
  ring

end

end Work.Asymptotics.KhatE1
