import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.CKFinal.LineDecay.Ncusp8Clean
import Submission.Work.Asymptotics.KMinusCuspBallDefs
import Submission.Work.Asymptotics.KPlusFunnel.ZFacts
import Submission.Work.Asymptotics.KPlusXiDefs

namespace Work.CKFinal.LineDecay

noncomputable section

open UpperHalfPlane

/-- The CKMRV quotient bound `(quotientbounds1new)` for `K_-^{(8)}` on the half-region
`Im τ ≥ 1/2`: for `τ ∈ 𝒟`, `Im z ≥ 1/3` and `j τ ≠ j z`,
`‖z² K_-^{(8)}(τ, S·z)‖ ≤ C (1+‖τ‖)^A (1+‖z‖)^A e^{-π Im z} / ‖Δ(z)(jτ - jz)‖`.

This is the KMinus instance of the half-region bound.  It is stated here under its own name
because the module `Submission.Work.Asymptotics.KMinus_slash_bound_half` cannot be imported
together with `Submission.Work.CKFinal.LineDecay.Defs` (both closures contain a duplicate
definition of `Work.Asymptotics.continuous_scale`, from `KernelBoundAux` resp.
`MiddleRange.Basic`).  The proof does not need that import: `Work.Asymptotics.Ncusp_ident`
(`Ncusp ℓ 8 τ z = Δ(z)(jτ-jz)·z²K_-^{(8)}(τ,S·z)`) together with the decay bound
`ncusp8_decay_bound ℓ` (`Submission.Work.CKFinal.LineDecay.Ncusp8Clean`) and
`Work.Asymptotics.delta_lower_third` (`c‖q z‖ ≤ ‖Δ z‖`) give exactly this estimate; the same
argument is carried out (privately) as `kmins_slash_bound_low` in
`Submission.Work.CKFinal.LineDecay.P1_line_bound_eight`. -/
theorem KMinus_slash_bound_half_clean (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      ∀ (τ z : UpperHalfPlane), τ ∈ Work.Asymptotics.DomainD → (1 : ℝ) / 2 ≤ τ.im →
        (1 : ℝ) / 3 ≤ z.im →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
        ‖(z : ℂ) ^ 2 * Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • z)‖
          ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A
              * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
  obtain ⟨Cn, An, hCn, hAn, hN⟩ := ncusp8_decay_bound ℓ
  obtain ⟨cΔ, hcΔ, hΔlow⟩ := Work.Asymptotics.delta_lower_third
  refine ⟨Cn / cΔ + 1, An, by positivity, hAn, ?_⟩
  intro τ z hD hτ2 hz3 hne
  have hτ3 : (1 : ℝ) / 3 ≤ τ.im := by linarith
  have hΔz : Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) ≠ 0 :=
    mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z) (sub_ne_zero.mpr hne)
  have hkey : Work.Asymptotics.Ncusp ℓ 8 τ z
      = (Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z))
        * ((z : ℂ) ^ 2 * Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • z)) := by
    have h := Work.Asymptotics.Ncusp_ident ℓ 8 (Or.inl rfl) τ z hne
    rw [show -((2 : ℤ) - ((8 : ℕ) : ℤ) / 2) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast] at h
    exact h
  have hmul : ‖Work.Asymptotics.Ncusp ℓ 8 τ z‖
      = ‖Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
        * ‖(z : ℂ) ^ 2 * Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • z)‖ := by
    rw [hkey, norm_mul]
  have hΔτlow : cΔ * Real.exp (-(2 * Real.pi * τ.im)) ≤ ‖Work.Kernels.DeltaFun τ‖ := by
    have h := hΔlow τ hτ3
    rwa [Work.Asymptotics.norm_qParamFun] at h
  have hexp1 : Real.exp (-(Real.pi * (2 * τ.im + z.im)))
      = Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(Real.pi * z.im)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hnum : ‖Work.Asymptotics.Ncusp ℓ 8 τ z‖
      ≤ (Cn / cΔ + 1) * (1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
          * Real.exp (-(Real.pi * z.im)) := by
    have h1 := hN τ z hτ3 hz3
    rw [norm_mul] at h1
    have hstep : cΔ * Real.exp (-(2 * Real.pi * τ.im)) * ‖Work.Asymptotics.Ncusp ℓ 8 τ z‖
        ≤ (cΔ * Real.exp (-(2 * Real.pi * τ.im)))
            * ((Cn / cΔ) * (1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
                * Real.exp (-(Real.pi * z.im))) := by
      calc cΔ * Real.exp (-(2 * Real.pi * τ.im)) * ‖Work.Asymptotics.Ncusp ℓ 8 τ z‖
          ≤ ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Asymptotics.Ncusp ℓ 8 τ z‖ :=
            mul_le_mul_of_nonneg_right hΔτlow (norm_nonneg _)
        _ ≤ Cn * (1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
              * Real.exp (-(Real.pi * (2 * τ.im + z.im))) := h1
        _ = Cn * (1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
              * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(Real.pi * z.im))) := by
            rw [hexp1]
        _ = (cΔ * Real.exp (-(2 * Real.pi * τ.im)))
              * ((Cn / cΔ) * (1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
                  * Real.exp (-(Real.pi * z.im))) := by
            field_simp
    have hbase : ‖Work.Asymptotics.Ncusp ℓ 8 τ z‖
        ≤ (Cn / cΔ) * (1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
            * Real.exp (-(Real.pi * z.im)) :=
      le_of_mul_le_mul_left hstep (by positivity)
    refine le_trans hbase ?_
    have h1' : Cn / cΔ ≤ Cn / cΔ + 1 := by linarith
    have hnn : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
        * Real.exp (-(Real.pi * z.im)) := by positivity
    calc (Cn / cΔ) * (1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
            * Real.exp (-(Real.pi * z.im))
        = (Cn / cΔ) * ((1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
            * Real.exp (-(Real.pi * z.im))) := by ring
      _ ≤ (Cn / cΔ + 1) * ((1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
            * Real.exp (-(Real.pi * z.im))) := mul_le_mul_of_nonneg_right h1' hnn
      _ = (Cn / cΔ + 1) * (1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
            * Real.exp (-(Real.pi * z.im)) := by ring
  have hD'0 : (0 : ℝ) ≤ ‖Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := norm_nonneg _
  have hD'pos : (0 : ℝ) < ‖Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
    norm_pos_iff.mpr hΔz
  have hquot : ‖Work.Asymptotics.Ncusp ℓ 8 τ z‖
        / ‖Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
      = ‖(z : ℂ) ^ 2 * Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • z)‖ := by
    rw [hmul, mul_div_cancel_left₀ _ (ne_of_gt hD'pos)]
  rw [← hquot]
  exact div_le_div_of_nonneg_right hnum hD'0

end

end Work.CKFinal.LineDecay
