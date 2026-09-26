import Mathlib
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Residues.LamSExpansion
import Submission.Work.Residues.DeltaExpansion
import Submission.Work.CKFinal.LineDecay.V0LS_continuous
import Submission.Work.CKFinal.LineDecay.funnelLowStrip_compact

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

noncomputable section

/-! ## The `𝓛_S`-piece of `𝒱₀` is `-𝒞` -/

/-- The norm of the `𝓛_S`-piece of `𝒱₀` (`NcV0_eq`, `Ncusp24_delta_funnel_zfree`) is the norm of
the auxiliary function `Ccore` of `Work.Residues.KMinusCuspDefs`, whose cusp bound
`Ccore_cusp` is available in the workspace. -/
private lemma norm_V0LS_eq_norm_Ccore (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    ‖Work.Residues.Ccore ℓ τ‖
      = ‖3456 * Work.Kernels.E4Fun τ ^ 3
        + (3 * Work.Kernels.jInvariantFun τ * Work.Residues.Yfun τ
            - 1728 * (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
                - 2 * Work.Kernels.WFun τ ^ 2) * Work.Kernels.E8Fun τ) * ℓ.L_S τ‖ := by
  have h : Work.Residues.Ccore ℓ τ
      = -(3456 * Work.Kernels.E4Fun τ ^ 3
        + (3 * Work.Kernels.jInvariantFun τ * Work.Residues.Yfun τ
            - 1728 * (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
                - 2 * Work.Kernels.WFun τ ^ 2) * Work.Kernels.E8Fun τ) * ℓ.L_S τ) := by
    rw [Work.Residues.Ccore_eq, Work.Residues.xi4Fun_slash_S_apply]
    ring
  rw [h, norm_neg]

/-! ## The theorem -/

theorem Ncusp24_V0LS_funnel (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖3456 * Work.Kernels.E4Fun τ ^ 3
        + (3 * Work.Kernels.jInvariantFun τ * Work.Residues.Yfun τ
            - 1728 * (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
                - 2 * Work.Kernels.WFun τ ^ 2) * Work.Kernels.E8Fun τ) * ℓ.L_S τ‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * τ.im)) ^ 2 := by
  obtain ⟨H, C₀, hC₀pos, hC₀bnd⟩ := Work.Residues.Ccore_cusp ℓ
  have hcont : Continuous (fun τ : UpperHalfPlane =>
      3456 * Work.Kernels.E4Fun τ ^ 3
        + (3 * Work.Kernels.jInvariantFun τ * Work.Residues.Yfun τ
            - 1728 * (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
                - 2 * Work.Kernels.WFun τ ^ 2) * Work.Kernels.E8Fun τ) * ℓ.L_S τ) :=
    V0LS_continuous ℓ
  rcases lt_or_ge H 2 with hH2 | hH2
  · refine ⟨C₀ + 1, 0, by linarith, le_refl 0, fun τ hτ => ?_⟩
    have hHle : H ≤ τ.im := le_trans hH2.le hτ.2
    have h := hC₀bnd τ hHle
    rw [Work.Residues.tpar, pow_zero, mul_one] at h
    rw [← norm_V0LS_eq_norm_Ccore ℓ τ, Real.rpow_zero, mul_one]
    calc ‖Work.Residues.Ccore ℓ τ‖
        ≤ C₀ * Real.exp (-(Real.pi * τ.im)) ^ 2 := h
      _ ≤ (C₀ + 1) * Real.exp (-(Real.pi * τ.im)) ^ 2 := by
          have h0 : (0 : ℝ) ≤ Real.exp (-(Real.pi * τ.im)) ^ 2 := by positivity
          nlinarith
  · obtain ⟨B, hB⟩ :=
      (funnelLowStrip_compact (H := H)).exists_bound_of_continuousOn hcont.continuousOn
    set B₀ : ℝ := max B 0 with hB₀def
    have hB₀nn : (0 : ℝ) ≤ B₀ := le_max_right _ _
    have hstrip : ∀ τ : UpperHalfPlane, |τ.re| ≤ 1 → 2 ≤ τ.im → τ.im ≤ H →
        ‖Work.Residues.Ccore ℓ τ‖ ≤ B₀ := by
      intro τ h1 h2 h3
      rw [norm_V0LS_eq_norm_Ccore ℓ τ]
      exact le_trans (hB τ ⟨h1, h2, h3⟩) (le_max_left _ _)
    refine ⟨max C₀ (B₀ * Real.exp (2 * Real.pi * H)) + 1, 0, by positivity, le_refl 0,
      fun τ hτ => ?_⟩
    have hre : |τ.re| ≤ 1 := le_of_lt (Work.Asymptotics.Funnel.re_abs_lt_one hτ)
    have him2 : (2 : ℝ) ≤ τ.im := hτ.2
    rw [← norm_V0LS_eq_norm_Ccore ℓ τ, Real.rpow_zero, mul_one]
    rcases lt_or_ge τ.im H with hlt | hge
    · -- low strip: bounded by compactness
      have hstripb := hstrip τ hre him2 (le_of_lt hlt)
      have hexp : (1 : ℝ) ≤ Real.exp (2 * Real.pi * H) * Real.exp (-(Real.pi * τ.im)) ^ 2 := by
        have h2 : Real.exp (-(Real.pi * τ.im)) ^ 2 = Real.exp (-(Real.pi * τ.im) * 2) := by
          rw [pow_two, ← Real.exp_add]
          congr 1; ring
        rw [h2, ← Real.exp_add, Real.one_le_exp_iff]
        nlinarith [Real.pi_pos, hlt.le]
      have hsq : (0 : ℝ) ≤ Real.exp (-(Real.pi * τ.im)) ^ 2 := pow_nonneg (Real.exp_pos _).le 2
      have hstep : B₀ ≤ (B₀ * Real.exp (2 * Real.pi * H)) * Real.exp (-(Real.pi * τ.im)) ^ 2 := by
        nlinarith [hexp, hB₀nn, hsq, mul_nonneg hB₀nn hsq]
      calc ‖Work.Residues.Ccore ℓ τ‖
          ≤ B₀ := hstripb
        _ ≤ (B₀ * Real.exp (2 * Real.pi * H)) * Real.exp (-(Real.pi * τ.im)) ^ 2 := hstep
        _ ≤ (max C₀ (B₀ * Real.exp (2 * Real.pi * H)) + 1)
              * Real.exp (-(Real.pi * τ.im)) ^ 2 := by
            have hle : B₀ * Real.exp (2 * Real.pi * H)
                ≤ max C₀ (B₀ * Real.exp (2 * Real.pi * H)) + 1 := by
              have := le_max_right C₀ (B₀ * Real.exp (2 * Real.pi * H))
              linarith
            exact mul_le_mul_of_nonneg_right hle hsq
    · -- deep region: the cusp bound
      have h := hC₀bnd τ hge
      rw [Work.Residues.tpar, pow_zero, mul_one] at h
      have h0 : (0 : ℝ) ≤ Real.exp (-(Real.pi * τ.im)) ^ 2 := by positivity
      calc ‖Work.Residues.Ccore ℓ τ‖
          ≤ C₀ * Real.exp (-(Real.pi * τ.im)) ^ 2 := h
        _ ≤ (max C₀ (B₀ * Real.exp (2 * Real.pi * H)) + 1)
              * Real.exp (-(Real.pi * τ.im)) ^ 2 := by
            have hle : C₀ ≤ max C₀ (B₀ * Real.exp (2 * Real.pi * H)) + 1 := by
              have := le_max_left C₀ (B₀ * Real.exp (2 * Real.pi * H))
              linarith
            exact mul_le_mul_of_nonneg_right hle h0

end

end Work.CKFinal.LineDecay
