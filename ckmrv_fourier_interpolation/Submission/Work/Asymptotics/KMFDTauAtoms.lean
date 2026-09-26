import Mathlib
import Submission.Work.Asymptotics.KMFDDefs
import Submission.Work.Asymptotics.DeltaFun_upper_sharp
import Submission.Work.FunnelNumerics.Delta_funnel_bounds
import Submission.Work.Asymptotics.psi_InP

set_option maxHeartbeats 1000000

namespace Work.Asymptotics

open UpperHalfPlane
open Work.Kernels
open Work.Residues (Ept tpar)

noncomputable section

/-! ## Elementary exponential identities -/

private lemma kmfd_exp_neg_cancel (A : ℝ) : Real.exp A * Real.exp (-A) = 1 := by
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

private lemma kmfd_exp_sq_cancel (A : ℝ) :
    Real.exp A * Real.exp A * Real.exp (-A) = Real.exp A := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

private lemma kmfd_scale_nonneg (τ : ℍ) (N : ℝ) : (0 : ℝ) ≤ (scale τ) ^ N :=
  Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N


/-! ## The contour `z = i t` -/

/-- On the contour `z = i t`, `z.im = t`. -/
theorem kmfd_im_of_contour {z : ℍ} {t : ℝ} (hz : (z : ℂ) = (t : ℂ) * Complex.I) : z.im = t := by
  have h := congrArg Complex.im hz
  simp [UpperHalfPlane.coe_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im] at h
  linarith [h]

/-- `‖Ept z‖ = exp (-π t)` on the contour `z = i t`. -/
theorem kmfd_norm_Ept_of_contour {z : ℍ} {t : ℝ} (hz : (z : ℂ) = (t : ℂ) * Complex.I) :
    ‖Ept z‖ = Real.exp (-(Real.pi * t)) := by
  rw [Work.Residues.norm_Ept, kmfd_im_of_contour hz]

/-- `‖(z : ℂ)‖ = t` on the contour `z = i t`, for `t ≥ 0`. -/
theorem kmfd_norm_coe_of_contour {z : ℍ} {t : ℝ} (hz : (z : ℂ) = (t : ℂ) * Complex.I)
    (ht : 0 ≤ t) : ‖(z : ℂ)‖ = t := by
  rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht]

/-! ## The individual atom bounds -/

/-- `‖j(τ)‖ ≤ (27/4) e^{2π Im τ}` on the funnel. -/
private lemma kmfd_j_le : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ →
    ‖jInvariantFun τ‖ ≤ C * Real.exp (2 * Real.pi * τ.im) := by
  refine ⟨27 / 4, by norm_num, fun τ hτ => ?_⟩
  have hΔlow : (1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * τ.im)) ≤ ‖DeltaFun τ‖ := by
    have h := Work.FunnelNumerics.Delta_funnel_bounds.1 τ (Funnel.im_two hτ)
    rwa [norm_qParamFun] at h
  have hE4b : ‖E4Fun τ‖ ≤ 3 / 2 := Work.FunnelNumerics.E4_funnel_bounds.1 τ hτ
  have hnum : ‖E4Fun τ ^ 3‖ ≤ (3 / 2) ^ 3 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hE4b 3
  have hpos : 0 < (1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * τ.im)) := by positivity
  have hcoe : jInvariantFun τ = E4Fun τ ^ 3 / DeltaFun τ := rfl
  rw [hcoe, norm_div]
  have hinv : (‖DeltaFun τ‖)⁻¹ ≤ ((1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * τ.im)))⁻¹ :=
    inv_anti₀ hpos hΔlow
  have hrec : ((1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * τ.im)))⁻¹
      = 2 * Real.exp (2 * Real.pi * τ.im) := by
    rw [Real.exp_neg]
    field_simp
  rw [hrec] at hinv
  calc ‖E4Fun τ ^ 3‖ / ‖DeltaFun τ‖ = ‖E4Fun τ ^ 3‖ * (‖DeltaFun τ‖)⁻¹ := by ring
    _ ≤ (3 / 2) ^ 3 * (2 * Real.exp (2 * Real.pi * τ.im)) :=
        mul_le_mul hnum hinv (by positivity) (by positivity)
    _ = (27 / 4) * Real.exp (2 * Real.pi * τ.im) := by norm_num; ring

/-- `‖Δ(τ)‖ ≤ 2 e^{-2π Im τ}` on the funnel. -/
private lemma kmfd_Delta_le : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ →
    ‖DeltaFun τ‖ ≤ C * Real.exp (-(2 * Real.pi * τ.im)) :=
  ⟨2, by norm_num, fun τ hτ => DeltaFun_upper_sharp τ (Funnel.im_one hτ)⟩

/-- `‖E₄(τ)‖ ≤ 3/2` on the funnel. -/
private lemma kmfd_E4_le : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ → ‖E4Fun τ‖ ≤ C :=
  ⟨3 / 2, by norm_num, fun τ hτ => Work.FunnelNumerics.E4_funnel_bounds.1 τ hτ⟩

/-- `‖E₄(τ)³‖ ≤ 27/8` on the funnel. -/
private lemma kmfd_E4cube_le : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ → ‖E4Fun τ ^ 3‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := kmfd_E4_le
  refine ⟨C ^ 3, by positivity, fun τ hτ => ?_⟩
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h τ hτ) 3

/-- `‖E₆(τ)‖ ≤ C` on the funnel. -/
private lemma kmfd_E6_le : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ → ‖E6Fun τ‖ ≤ C :=
  exists_E6_Funnel_bound

/-- `‖ψ₂(τ)‖` and `‖ψ₄(τ)‖` grow at most like a power of `scale τ` on the funnel. -/
private lemma kmfd_psi_scale (ℓ : LogLambdaData) :
    (∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖psi2 ℓ τ‖ ≤ C * (scale τ) ^ N) ∧
    (∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖psi4 ℓ τ‖ ≤ C * (scale τ) ^ N) := by
  have h2 := (psi_InP ℓ).1.2
  have h4 := (psi_InP ℓ).2.2
  obtain ⟨α2, N2, hα2, hN2, hb2⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale Set.univ (Work.Kernels.psi2 ℓ)).mp h2
  obtain ⟨α4, N4, hα4, hN4, hb4⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale Set.univ (Work.Kernels.psi4 ℓ)).mp h4
  constructor
  · refine ⟨α2 + 1, N2, by linarith, hN2, fun τ hτ => ?_⟩
    have h1 := hb2 τ (Set.mem_univ τ)
    have h3 : (0:ℝ) ≤ (scale τ) ^ N2 :=
      Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N2
    nlinarith [h1, h3, hα2]
  · refine ⟨α4 + 1, N4, by linarith, hN4, fun τ hτ => ?_⟩
    have h1 := hb4 τ (Set.mem_univ τ)
    have h3 : (0:ℝ) ≤ (scale τ) ^ N4 :=
      Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N4
    nlinarith [h1, h3, hα4]

/-- `‖ψ₂(τ)E₁₀(τ)‖ ≤ C (scale τ)^N` on the funnel. -/
private lemma kmfd_psi2E10_le (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖psi2 ℓ τ * E10Fun τ‖ ≤ C * (scale τ) ^ N := by
  obtain ⟨C2, N2, hC2, hN2, h2⟩ := (kmfd_psi_scale ℓ).1
  obtain ⟨C4, hC4, h4⟩ := kmfd_E4_le
  obtain ⟨C6, hC6, h6⟩ := kmfd_E6_le
  refine ⟨C2 * (C4 * C6), N2, by positivity, hN2, fun τ hτ => ?_⟩
  have hE10 : ‖E10Fun τ‖ ≤ C4 * C6 := by
    rw [show E10Fun τ = E4Fun τ * E6Fun τ from rfl, norm_mul]
    exact mul_le_mul (h4 τ hτ) (h6 τ hτ) (norm_nonneg _) hC4.le
  calc ‖psi2 ℓ τ * E10Fun τ‖ = ‖psi2 ℓ τ‖ * ‖E10Fun τ‖ := norm_mul _ _
    _ ≤ (C2 * (scale τ) ^ N2) * (C4 * C6) :=
        mul_le_mul (h2 τ hτ) hE10 (norm_nonneg _) (mul_nonneg hC2.le (kmfd_scale_nonneg τ N2))
    _ = C2 * (C4 * C6) * (scale τ) ^ N2 := by ring

/-- `‖ψ₄(τ)E₈(τ)‖ ≤ C (scale τ)^N` on the funnel. -/
private lemma kmfd_psi4E8_le (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖psi4 ℓ τ * E8Fun τ‖ ≤ C * (scale τ) ^ N := by
  obtain ⟨C4p, N4p, hC4p, hN4p, h4p⟩ := (kmfd_psi_scale ℓ).2
  obtain ⟨C4, hC4, h4⟩ := kmfd_E4_le
  refine ⟨C4p * (C4 * C4), N4p, by positivity, hN4p, fun τ hτ => ?_⟩
  have hE8 : ‖E8Fun τ‖ ≤ C4 * C4 := by
    rw [show E8Fun τ = E4Fun τ ^ 2 from rfl, norm_pow, pow_two]
    exact mul_le_mul (h4 τ hτ) (h4 τ hτ) (norm_nonneg _) hC4.le
  calc ‖psi4 ℓ τ * E8Fun τ‖ = ‖psi4 ℓ τ‖ * ‖E8Fun τ‖ := norm_mul _ _
    _ ≤ (C4p * (scale τ) ^ N4p) * (C4 * C4) :=
        mul_le_mul (h4p τ hτ) hE8 (norm_nonneg _) (mul_nonneg hC4p.le (kmfd_scale_nonneg τ N4p))
    _ = C4p * (C4 * C4) * (scale τ) ^ N4p := by ring

/-- `ψ₂E₁₀ - ψ₄E₈ = O((scale τ)^N e^{-2π Im τ})` on the funnel. -/
private lemma kmfd_psi_le (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ‖
        ≤ C * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) := by
  obtain ⟨CX, hCX, hX⟩ :=
    Work.FunnelNumerics.cusp_bound_two (S := Work.Residues.S_X)
      (by unfold Work.Residues.S_X; fun_prop) 2
  obtain ⟨CY, hCY, hY⟩ :=
    Work.FunnelNumerics.cusp_bound_two (S := Work.Residues.S_Y)
      (by unfold Work.Residues.S_Y; fun_prop) 1
  obtain ⟨CL, NL, hCL, hNL, hL⟩ := Work.FunnelNumerics.L_scale_bound ℓ
  obtain ⟨CS, hCS, hLS⟩ := Work.FunnelNumerics.LS_tpar_bound ℓ
  refine ⟨CL * CX + CS * CY + 1, NL, by positivity, hNL, fun τ hτ => ?_⟩
  have hτ2 : 2 ≤ τ.im := Funnel.im_two hτ
  have hXb : ‖Work.Residues.Xfun τ‖ ≤ CX * tpar τ ^ 2 := by
    rw [Work.Residues.Xfun_eq]; exact hX τ hτ2
  have hYb : ‖Work.Residues.Yfun τ‖ ≤ CY * tpar τ := by
    rw [Work.Residues.Yfun_eq]
    simpa only [pow_one] using hY τ hτ2
  have hLb : ‖ℓ.L τ‖ ≤ CL * (scale τ) ^ NL := hL τ
  have hLSb : ‖ℓ.L_S τ‖ ≤ CS * tpar τ := hLS τ hτ2
  have hs1 : (1:ℝ) ≤ (scale τ) ^ NL :=
    Real.one_le_rpow (Work.Kernels.one_le_scale τ) hNL
  have htp : tpar τ = Real.exp (-(Real.pi * τ.im)) := rfl
  have htp2 : tpar τ ^ 2 = Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [htp, sq, ← Real.exp_add]
    congr 1
    ring
  have h1 : ‖ℓ.L τ * Work.Residues.Xfun τ‖
      ≤ CL * CX * (scale τ) ^ NL * Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [norm_mul]
    calc ‖ℓ.L τ‖ * ‖Work.Residues.Xfun τ‖
        ≤ (CL * (scale τ) ^ NL) * (CX * tpar τ ^ 2) :=
          mul_le_mul hLb hXb (norm_nonneg _) (mul_nonneg hCL.le (kmfd_scale_nonneg τ NL))
      _ = CL * CX * (scale τ) ^ NL * tpar τ ^ 2 := by ring
      _ = CL * CX * (scale τ) ^ NL * Real.exp (-(2 * Real.pi * τ.im)) := by rw [htp2]
  have h2 : ‖ℓ.L_S τ * Work.Residues.Yfun τ‖ ≤ CS * CY * tpar τ ^ 2 := by
    rw [norm_mul]
    calc ‖ℓ.L_S τ‖ * ‖Work.Residues.Yfun τ‖
        ≤ (CS * tpar τ) * (CY * tpar τ) :=
          mul_le_mul hLSb hYb (norm_nonneg _) (mul_nonneg hCS.le (Work.Residues.tpar_pos τ).le)
      _ = CS * CY * tpar τ ^ 2 := by ring
  have hkey : ‖psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ‖
      = ‖ℓ.L τ * Work.Residues.Xfun τ + ℓ.L_S τ * Work.Residues.Yfun τ‖ := by
    rw [show psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ
        = -(psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ) by ring,
      Work.Residues.psi4E8_sub ℓ τ, norm_neg]
  rw [hkey]
  have hexp0 : (0:ℝ) < Real.exp (-(2 * Real.pi * τ.im)) := Real.exp_pos _
  calc ‖ℓ.L τ * Work.Residues.Xfun τ + ℓ.L_S τ * Work.Residues.Yfun τ‖
      ≤ ‖ℓ.L τ * Work.Residues.Xfun τ‖ + ‖ℓ.L_S τ * Work.Residues.Yfun τ‖ := norm_add_le _ _
    _ ≤ CL * CX * (scale τ) ^ NL * Real.exp (-(2 * Real.pi * τ.im)) + CS * CY * tpar τ ^ 2 :=
        add_le_add h1 h2
    _ ≤ (CL * CX + CS * CY + 1) * (scale τ) ^ NL * Real.exp (-(2 * Real.pi * τ.im)) := by
        rw [htp2]
        have h3 : CS * CY * Real.exp (-(2 * Real.pi * τ.im))
            ≤ CS * CY * (scale τ) ^ NL * Real.exp (-(2 * Real.pi * τ.im)) := by
          have hnn : (0:ℝ) ≤ CS * CY * Real.exp (-(2 * Real.pi * τ.im)) := by positivity
          calc CS * CY * Real.exp (-(2 * Real.pi * τ.im))
              = CS * CY * Real.exp (-(2 * Real.pi * τ.im)) * 1 := by ring
            _ ≤ CS * CY * Real.exp (-(2 * Real.pi * τ.im)) * (scale τ) ^ NL :=
                mul_le_mul_of_nonneg_left hs1 hnn
            _ = CS * CY * (scale τ) ^ NL * Real.exp (-(2 * Real.pi * τ.im)) := by ring
        nlinarith [h3, hexp0]

/-- `‖j(τ)(ψ₂E₁₀ - ψ₄E₈)‖ ≤ C (scale τ)^N` on the funnel. -/
private lemma kmfd_jpsi_le (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖jInvariantFun τ * (psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ)‖
        ≤ C * (scale τ) ^ N := by
  obtain ⟨Cj, hCj, hj⟩ := kmfd_j_le
  obtain ⟨Cp, Np, hCp, hNp, hp⟩ := kmfd_psi_le ℓ
  refine ⟨Cj * Cp, Np, by positivity, hNp, fun τ hτ => ?_⟩
  rw [norm_mul]
  have hexp := kmfd_exp_neg_cancel (2 * Real.pi * τ.im)
  calc ‖jInvariantFun τ‖ * ‖psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ‖
      ≤ (Cj * Real.exp (2 * Real.pi * τ.im))
          * (Cp * (scale τ) ^ Np * Real.exp (-(2 * Real.pi * τ.im))) :=
        mul_le_mul (hj τ hτ) (hp τ hτ) (norm_nonneg _) (by positivity)
    _ = Cj * Cp * (scale τ) ^ Np := by
        rw [show (Cj * Real.exp (2 * Real.pi * τ.im))
              * (Cp * (scale τ) ^ Np * Real.exp (-(2 * Real.pi * τ.im)))
            = Cj * Cp * (scale τ) ^ Np
              * (Real.exp (2 * Real.pi * τ.im) * Real.exp (-(2 * Real.pi * τ.im))) by ring,
          hexp, mul_one]

/-- `‖j(τ)²Δ(τ)‖ ≤ C e^{2π Im τ}` on the funnel. -/
private lemma kmfd_j2Delta_le : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ →
    ‖jInvariantFun τ ^ 2 * DeltaFun τ‖ ≤ C * Real.exp (2 * Real.pi * τ.im) := by
  obtain ⟨Cj, hCj, hj⟩ := kmfd_j_le
  obtain ⟨Cd, hCd, hd⟩ := kmfd_Delta_le
  refine ⟨Cj * Cj * Cd, by positivity, fun τ hτ => ?_⟩
  rw [norm_mul, norm_pow]
  have h1 := hj τ hτ
  have h2 := hd τ hτ
  have hexp := kmfd_exp_sq_cancel (2 * Real.pi * τ.im)
  calc ‖jInvariantFun τ‖ ^ 2 * ‖DeltaFun τ‖
      ≤ (Cj * Real.exp (2 * Real.pi * τ.im)) ^ 2
          * (Cd * Real.exp (-(2 * Real.pi * τ.im))) := by
        refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2 (norm_nonneg _)
          (by positivity)
    _ = Cj * Cj * Cd * Real.exp (2 * Real.pi * τ.im) := by
        rw [show (Cj * Real.exp (2 * Real.pi * τ.im)) ^ 2
              * (Cd * Real.exp (-(2 * Real.pi * τ.im)))
            = Cj * Cj * Cd
              * (Real.exp (2 * Real.pi * τ.im) * Real.exp (2 * Real.pi * τ.im)
                  * Real.exp (-(2 * Real.pi * τ.im))) by ring,
          hexp]

/-- `‖j(τ)Δ(τ)‖ ≤ C` on the funnel. -/
private lemma kmfd_jDelta_le : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ →
    ‖jInvariantFun τ * DeltaFun τ‖ ≤ C := by
  obtain ⟨Cj, hCj, hj⟩ := kmfd_j_le
  obtain ⟨Cd, hCd, hd⟩ := kmfd_Delta_le
  refine ⟨Cj * Cd, by positivity, fun τ hτ => ?_⟩
  rw [norm_mul]
  have hexp := kmfd_exp_neg_cancel (2 * Real.pi * τ.im)
  calc ‖jInvariantFun τ‖ * ‖DeltaFun τ‖
      ≤ (Cj * Real.exp (2 * Real.pi * τ.im)) * (Cd * Real.exp (-(2 * Real.pi * τ.im))) :=
        mul_le_mul (hj τ hτ) (hd τ hτ) (norm_nonneg _) (by positivity)
    _ = Cj * Cd := by
        rw [show (Cj * Real.exp (2 * Real.pi * τ.im)) * (Cd * Real.exp (-(2 * Real.pi * τ.im)))
            = Cj * Cd * (Real.exp (2 * Real.pi * τ.im) * Real.exp (-(2 * Real.pi * τ.im))) by ring,
          hexp, mul_one]

/-- `‖j(τ) ψ₂E₁₀‖ ≤ C (scale τ)^N e^{2π Im τ}` on the funnel. -/
private lemma kmfd_jpsi2E10_le (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖jInvariantFun τ * (psi2 ℓ τ * E10Fun τ)‖
        ≤ C * (scale τ) ^ N * Real.exp (2 * Real.pi * τ.im) := by
  obtain ⟨Cj, hCj, hj⟩ := kmfd_j_le
  obtain ⟨Cp, Np, hCp, hNp, hp⟩ := kmfd_psi2E10_le ℓ
  refine ⟨Cj * Cp, Np, by positivity, hNp, fun τ hτ => ?_⟩
  rw [norm_mul]
  calc ‖jInvariantFun τ‖ * ‖psi2 ℓ τ * E10Fun τ‖
      ≤ (Cj * Real.exp (2 * Real.pi * τ.im)) * (Cp * (scale τ) ^ Np) :=
        mul_le_mul (hj τ hτ) (hp τ hτ) (norm_nonneg _) (by positivity)
    _ = Cj * Cp * (scale τ) ^ Np * Real.exp (2 * Real.pi * τ.im) := by ring

/-- `‖j(τ) ψ₄E₈‖ ≤ C (scale τ)^N e^{2π Im τ}` on the funnel. -/
private lemma kmfd_jpsi4E8_le (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖jInvariantFun τ * (psi4 ℓ τ * E8Fun τ)‖
        ≤ C * (scale τ) ^ N * Real.exp (2 * Real.pi * τ.im) := by
  obtain ⟨Cj, hCj, hj⟩ := kmfd_j_le
  obtain ⟨Cp, Np, hCp, hNp, hp⟩ := kmfd_psi4E8_le ℓ
  refine ⟨Cj * Cp, Np, by positivity, hNp, fun τ hτ => ?_⟩
  rw [norm_mul]
  calc ‖jInvariantFun τ‖ * ‖psi4 ℓ τ * E8Fun τ‖
      ≤ (Cj * Real.exp (2 * Real.pi * τ.im)) * (Cp * (scale τ) ^ Np) :=
        mul_le_mul (hj τ hτ) (hp τ hτ) (norm_nonneg _) (by positivity)
    _ = Cj * Cp * (scale τ) ^ Np * Real.exp (2 * Real.pi * τ.im) := by ring

/-- **Growth of the `τ`-atoms on the funnel.** -/
theorem kmfd_atoms (ℓ : LogLambdaData) : KMFDAtoms ℓ :=
  ⟨kmfd_j_le, kmfd_Delta_le, kmfd_E4cube_le, kmfd_E4_le, kmfd_E6_le,
    (kmfd_psi_scale ℓ).1, (kmfd_psi_scale ℓ).2, kmfd_psi2E10_le ℓ, kmfd_psi4E8_le ℓ,
    kmfd_psi_le ℓ, kmfd_jpsi_le ℓ, kmfd_j2Delta_le, kmfd_jDelta_le,
    kmfd_jpsi2E10_le ℓ, kmfd_jpsi4E8_le ℓ⟩

end

end Work.Asymptotics
