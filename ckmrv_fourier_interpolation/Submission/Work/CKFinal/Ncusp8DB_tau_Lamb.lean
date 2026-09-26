import Mathlib
import Submission.Work.FunnelNumerics.Lamb_funnel_bound
import Submission.Work.Asymptotics.psi_InP
import Submission.Work.Kernels.Kernels
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Asymptotics.KPlusFunnel.ZFacts

namespace Work.CKFinal

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

noncomputable section

/-!
# The bound `Δ · Λ = O((1+|τ|)^A e^{-2π Im τ})`

The product `Δ(τ)Λ(τ)` decays like the square of the cusp parameter on the funnel.  Off the
funnel it only has moderate growth: `Δ Λ = 𝓛 P₂ + 𝓛_S Q₂` with `P₂, Q₂ ∈ 𝒫` and `𝓛, 𝓛_S ∈ 𝒫`.
On the strip `1/3 ≤ Im τ ≤ 2` the exponential factor on the right is bounded below, so the
moderate-growth bound suffices; above height `2` we use the sharp funnel-type decay, which
(the proof shows) needs only `2 ≤ Im τ` and not membership in the fundamental domain.
-/

/-! ## The sharp decay for `Im τ ≥ 2` -/

/-- On `{Im τ ≥ 2}` the product `Δ Λ` is `O(S τ^N · e^{-2π Im τ})`.  This is
`Lamb_funnel_bound` with the hypothesis `τ ∈ 𝒟` removed: its proof never uses it. -/
theorem Lamb_tail_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, 2 ≤ τ.im →
      ‖Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ‖ ≤
        C * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) := by
  obtain ⟨CL, NL, hCL, hNL, hL⟩ := Work.FunnelNumerics.L_scale_bound ℓ
  obtain ⟨CS, hCS, hLS⟩ := Work.FunnelNumerics.LS_tpar_bound ℓ
  obtain ⟨CP, hCP, hP⟩ := Work.FunnelNumerics.P2fun_cusp_bound
  obtain ⟨CQ, hCQ, hQ⟩ := Work.FunnelNumerics.Q2fun_cusp_bound
  refine ⟨CL * CP + CS * CQ, NL, by positivity, hNL, fun τ hτ2 => ?_⟩
  have hexp : Real.exp (-(2 * Real.pi * τ.im)) = (Work.Residues.tpar τ) ^ 2 :=
    (Work.Residues.tpar_pow_two τ).symm
  rw [Work.FunnelNumerics.Delta_mul_Lamb_eq ℓ τ, hexp]
  set t := Work.Residues.tpar τ with ht
  have ht0 : 0 ≤ t := (Work.Residues.tpar_pos τ).le
  have ht1 : t ≤ 1 := Work.Residues.tpar_le_one τ
  have hs1 : (1 : ℝ) ≤ (Work.Kernels.scale τ) ^ NL :=
    Real.one_le_rpow (Work.Kernels.one_le_scale τ) hNL
  have hs0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ NL :=
    Real.rpow_nonneg (Work.Kernels.scale_pos τ).le NL
  have hA : ‖ℓ.L τ‖ ≤ CL * (Work.Kernels.scale τ) ^ NL := hL τ
  have hB : ‖Work.Residues.P2fun τ‖ ≤ CP * t ^ 2 := by
    have := hP τ hτ2; rwa [← ht] at this
  have hC : ‖ℓ.L_S τ‖ ≤ CS * t := by
    have := hLS τ hτ2; rwa [← ht] at this
  have hDd : ‖Work.Residues.Q2fun τ‖ ≤ CQ * t := by
    have := hQ τ hτ2; rwa [← ht] at this
  calc ‖ℓ.L τ * Work.Residues.P2fun τ + ℓ.L_S τ * Work.Residues.Q2fun τ‖
      ≤ ‖ℓ.L τ * Work.Residues.P2fun τ‖ + ‖ℓ.L_S τ * Work.Residues.Q2fun τ‖ :=
        norm_add_le _ _
    _ = ‖ℓ.L τ‖ * ‖Work.Residues.P2fun τ‖ + ‖ℓ.L_S τ‖ * ‖Work.Residues.Q2fun τ‖ := by
        rw [norm_mul, norm_mul]
    _ ≤ (CL * (Work.Kernels.scale τ) ^ NL) * (CP * t ^ 2) + (CS * t) * (CQ * t) :=
        add_le_add (mul_le_mul hA hB (norm_nonneg _) (by positivity))
          (mul_le_mul hC hDd (norm_nonneg _) (by positivity))
    _ = CL * CP * (Work.Kernels.scale τ) ^ NL * t ^ 2 + CS * CQ * t ^ 2 := by ring
    _ ≤ CL * CP * (Work.Kernels.scale τ) ^ NL * t ^ 2
          + CS * CQ * (Work.Kernels.scale τ) ^ NL * t ^ 2 := by
        have h1 : CS * CQ * t ^ 2
            ≤ CS * CQ * (Work.Kernels.scale τ) ^ NL * t ^ 2 := by
          have h0 : (0 : ℝ) ≤ CS * CQ * t ^ 2 := by positivity
          calc CS * CQ * t ^ 2 = CS * CQ * t ^ 2 * 1 := by ring
            _ ≤ CS * CQ * t ^ 2 * (Work.Kernels.scale τ) ^ NL :=
                mul_le_mul_of_nonneg_left hs1 h0
            _ = CS * CQ * (Work.Kernels.scale τ) ^ NL * t ^ 2 := by ring
        linarith
    _ = (CL * CP + CS * CQ) * (Work.Kernels.scale τ) ^ NL * t ^ 2 := by ring

/-! ## Moderate growth of `Δ Λ` on the whole upper half plane -/

private lemma xi2_mem_InP : Work.Kernels.InP Work.Kernels.xi2Fun := by
  rw [show Work.Kernels.xi2Fun =
      (fun τ : ℍ => Work.Kernels.UFun τ + Work.Kernels.WFun τ) from rfl]
  exact (Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.pow 4).add
    (Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.pow 4)

private lemma xi4_mem_InP : Work.Kernels.InP Work.Kernels.xi4Fun := by
  rw [show Work.Kernels.xi4Fun =
      (fun τ : ℍ => Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2
        - 2 * Work.Kernels.VFun τ ^ 2) from rfl]
  exact (((Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.pow 4).pow 2).add
      ((Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.pow 4).pow 2)).sub
    (((Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.pow 4).pow 2).const_mul 2)

private lemma E14_mem_InP : Work.Kernels.InP Work.Kernels.E14Fun := by
  rw [show Work.Kernels.E14Fun =
      (fun τ : ℍ => Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ) from rfl]
  exact (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.pow 2).mul
    Work.Kernels.ClassicalFacts.E6Fun_mem_InP

private lemma P2fun_mem_InP : Work.Kernels.InP Work.Residues.P2fun := by
  rw [show Work.Residues.P2fun =
      (fun τ : ℍ => Work.Kernels.xi4Fun τ * Work.Kernels.E4Fun τ ^ 3
        - Work.Kernels.xi2Fun τ * Work.Kernels.E14Fun τ) from rfl]
  exact (xi4_mem_InP.mul (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.pow 3)).sub
    (xi2_mem_InP.mul E14_mem_InP)

private lemma Q2fun_mem_InP : Work.Kernels.InP Work.Residues.Q2fun := by
  rw [show Work.Residues.Q2fun =
      (fun τ : ℍ => (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ
          * Work.Kernels.E4Fun τ ^ 3
        - (Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ
          * Work.Kernels.E14Fun τ) from rfl]
  exact ((Work.Kernels.InP.slash xi4_mem_InP (4 : ℤ) ModularGroup.S).mul
      (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.pow 3)).sub
    ((Work.Kernels.InP.slash xi2_mem_InP (2 : ℤ) ModularGroup.S).mul E14_mem_InP)

/-- `Δ Λ ∈ 𝒫`: it is a sum of products of the moderate-growth atoms `𝓛, 𝓛_S, P₂, Q₂`. -/
private lemma Delta_mul_Lamb_mem_InP (ℓ : Work.Kernels.LogLambdaData) :
    Work.Kernels.InP (fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ) := by
  have hL : Work.Kernels.InP ℓ.L := ⟨ℓ.holo, ℓ.memP⟩
  have hLS : Work.Kernels.InP ℓ.L_S := ⟨ℓ.holo_S, ℓ.memP_S⟩
  rw [show (fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ) =
      (fun τ : ℍ => ℓ.L τ * Work.Residues.P2fun τ
        + ℓ.L_S τ * Work.Residues.Q2fun τ) from
    funext (Work.FunnelNumerics.Delta_mul_Lamb_eq ℓ)]
  exact (hL.mul P2fun_mem_InP).add (hLS.mul Q2fun_mem_InP)

/-- Moderate growth of `Δ Λ` on all of `ℍ`, in scale form. -/
private lemma Delta_mul_Lamb_moderate (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane,
      ‖Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ‖
        ≤ C * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨α, N, hα, hN, hbound⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale Set.univ
      (fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ)).mp
      (Delta_mul_Lamb_mem_InP ℓ).2
  refine ⟨α + 1, N, by linarith, hN, fun τ => ?_⟩
  calc ‖Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ‖
      ≤ α * (Work.Kernels.scale τ) ^ N := hbound τ (Set.mem_univ τ)
    _ ≤ (α + 1) * (Work.Kernels.scale τ) ^ N :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le N)

/-! ## The two-region glue -/

theorem Ncusp8DB_tau_Lamb (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ τ : UpperHalfPlane, (1 : ℝ) / 3 ≤ τ.im →
      ‖Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im)) := by
  obtain ⟨C₁, N₁, hC₁, hN₁, htail⟩ := Lamb_tail_bound ℓ
  obtain ⟨C₂, N₂, hC₂, hN₂, hmod⟩ := Delta_mul_Lamb_moderate ℓ
  set A : ℝ := max N₁ N₂ with hAdef
  have hA0 : 0 ≤ A := le_max_of_le_left hN₁
  set K : ℝ := C₁ + C₂ * Real.exp (4 * Real.pi) with hKdef
  have hK0 : 0 < K := by
    have := Real.exp_pos (4 * Real.pi); rw [hKdef]; nlinarith
  refine ⟨K * (4 : ℝ) ^ A, A, by positivity, hA0, fun τ hτ => ?_⟩
  have him_inv : (τ.im)⁻¹ ≤ 3 := by
    have h1 : (1 / 3 : ℝ) ≤ τ.im := hτ
    have := (inv_le_inv₀ τ.im_pos (by norm_num : (0 : ℝ) < 1 / 3)).mpr h1
    simpa using this
  have hscale : Work.Kernels.scale τ ≤ 4 * (1 + ‖(τ : ℂ)‖) := by
    rw [Work.Kernels.scale]
    nlinarith [him_inv, norm_nonneg (τ : ℂ)]
  have hscale_pow : (Work.Kernels.scale τ) ^ A
      ≤ (4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A := by
    have h4 : (0 : ℝ) ≤ 4 := by norm_num
    have hn : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by positivity
    have := Real.rpow_le_rpow (Work.Kernels.scale_pos τ).le hscale hA0
    rwa [Real.mul_rpow h4 hn] at this
  have hN₁A : (Work.Kernels.scale τ) ^ N₁ ≤ (Work.Kernels.scale τ) ^ A :=
    Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale τ) (le_max_left N₁ N₂)
  have hN₂A : (Work.Kernels.scale τ) ^ N₂ ≤ (Work.Kernels.scale τ) ^ A :=
    Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale τ) (le_max_right N₁ N₂)
  have hscale0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ A :=
    Real.rpow_nonneg (Work.Kernels.scale_pos τ).le A
  have hP0 : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A :=
    Real.rpow_nonneg (by positivity) A
  have hE0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * τ.im)) := (Real.exp_pos _).le
  by_cases h2 : 2 ≤ τ.im
  · have h1 : ‖Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ‖
        ≤ C₁ * (Work.Kernels.scale τ) ^ N₁ * Real.exp (-(2 * Real.pi * τ.im)) := htail τ h2
    have h2' : C₁ * (Work.Kernels.scale τ) ^ N₁ * Real.exp (-(2 * Real.pi * τ.im))
        ≤ C₁ * (Work.Kernels.scale τ) ^ A * Real.exp (-(2 * Real.pi * τ.im)) := by
      gcongr
    have h3 : C₁ * (Work.Kernels.scale τ) ^ A * Real.exp (-(2 * Real.pi * τ.im))
        ≤ C₁ * ((4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A)
            * Real.exp (-(2 * Real.pi * τ.im)) := by
      gcongr
    have h4 : C₁ * ((4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A)
          * Real.exp (-(2 * Real.pi * τ.im))
        ≤ K * (4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A
            * Real.exp (-(2 * Real.pi * τ.im)) := by
      have hle : C₁ ≤ K := by rw [hKdef]; nlinarith [Real.exp_pos (4 * Real.pi), hC₂]
      have h0 : (0 : ℝ) ≤ (4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A
          * Real.exp (-(2 * Real.pi * τ.im)) := by positivity
      calc C₁ * ((4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A)
            * Real.exp (-(2 * Real.pi * τ.im))
          = C₁ * ((4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A
              * Real.exp (-(2 * Real.pi * τ.im))) := by ring
        _ ≤ K * ((4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A
              * Real.exp (-(2 * Real.pi * τ.im))) := mul_le_mul_of_nonneg_right hle h0
        _ = K * (4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A
              * Real.exp (-(2 * Real.pi * τ.im)) := by ring
    linarith
  · push_neg at h2
    have himle : τ.im ≤ 2 := le_of_lt h2
    have h1 : ‖Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ‖
        ≤ C₂ * (Work.Kernels.scale τ) ^ N₂ := hmod τ
    have h2' : C₂ * (Work.Kernels.scale τ) ^ N₂ ≤ C₂ * (Work.Kernels.scale τ) ^ A := by
      gcongr
    have h3 : C₂ * (Work.Kernels.scale τ) ^ A
        ≤ C₂ * ((4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A) := by
      gcongr
    have hexp1 : (1 : ℝ) ≤ Real.exp (4 * Real.pi) * Real.exp (-(2 * Real.pi * τ.im)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith [Real.pi_pos]
    have h4 : C₂ * ((4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A)
        ≤ K * (4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A
            * Real.exp (-(2 * Real.pi * τ.im)) := by
      have hle : C₂ * Real.exp (4 * Real.pi) ≤ K := by
        rw [hKdef]; linarith
      have hEP0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * τ.im))
          * ((4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A) := by positivity
      have hmul1 : C₂ * ((4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A)
          ≤ (Real.exp (4 * Real.pi) * Real.exp (-(2 * Real.pi * τ.im)))
              * (C₂ * ((4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A)) := by
        have := mul_le_mul_of_nonneg_right hexp1
          (by positivity : (0 : ℝ) ≤ C₂ * ((4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A))
        simpa using this
      have hmul2 : (C₂ * Real.exp (4 * Real.pi))
            * (Real.exp (-(2 * Real.pi * τ.im)) * ((4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A))
          ≤ K * (Real.exp (-(2 * Real.pi * τ.im))
            * ((4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A)) :=
        mul_le_mul_of_nonneg_right hle hEP0
      calc C₂ * ((4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A)
          ≤ (Real.exp (4 * Real.pi) * Real.exp (-(2 * Real.pi * τ.im)))
              * (C₂ * ((4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A)) := hmul1
        _ = (C₂ * Real.exp (4 * Real.pi))
              * (Real.exp (-(2 * Real.pi * τ.im)) * ((4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A)) := by
              ring
        _ ≤ K * (Real.exp (-(2 * Real.pi * τ.im))
              * ((4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A)) := hmul2
        _ = K * (4 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A
              * Real.exp (-(2 * Real.pi * τ.im)) := by ring
    linarith

end

end Work.CKFinal
