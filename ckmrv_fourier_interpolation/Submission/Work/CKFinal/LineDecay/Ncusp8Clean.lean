/-
# Clean copy of the `d = 8` `Ncusp` decay bound

`Submission/Work/CKFinal/Ncusp8_Delta_bound.lean` proves the `d = 8` bound
`‖Δ(τ) Ncusp ℓ 8 τ z‖ ≤ C (1+‖τ‖)^A (1+‖z‖)^A e^{-π(2 Im τ + Im z)}`, but its module imports
`Submission.Work.Asymptotics.KMinus_slash_bound_half`, whose import closure contains
`Work.Asymptotics.KernelBoundAux`; that module defines `Work.Asymptotics.continuous_scale`,
which clashes with the definition of the same name in `Work.Asymptotics.MiddleRange.Basic`
(imported, unavoidably, by `Work.CKFinal.LineDecay.Defs`).  This file reproduces the argument
of `Ncusp8_Delta_bound.lean` verbatim, with the one superfluous import removed and with the
auxiliary lemmas made `private`, under the name `ncusp8_decay_bound`.
-/
import Mathlib
import Submission.Work.Asymptotics.KMinusCuspBallDefs
import Submission.Work.Asymptotics.KMinusCuspBallLimit
import Submission.Work.Asymptotics.KMinusFunnelZBounds
import Submission.Work.Asymptotics.KMinusFunnelZBoundsLS
import Submission.Work.Asymptotics.psi_InP
import Submission.Work.FunnelNumerics.Lamb_funnel_bound
import Submission.Work.CKFinal.Ncusp8DB_tau_psi4
import Submission.Work.CKFinal.Ncusp8DB_tau_Lamb
import Submission.Work.CKFinal.Ncusp8DB_zfact

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

noncomputable section

set_option maxHeartbeats 1000000

private lemma DeltaFun_E4_bound_third :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, (1 : ℝ) / 3 ≤ τ.im →
      ‖Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ‖ ≤ C * Real.exp (-(2 * Real.pi * τ.im)) := by
  obtain ⟨CΔ, hCΔ, hΔ⟩ := Work.Asymptotics.delta_upper_third
  obtain ⟨C4, hC4, h4⟩ := Work.Asymptotics.E4Fun_bound_third
  refine ⟨CΔ * C4 + 1, by positivity, fun τ hτ => ?_⟩
  have hΔe : ‖Work.Kernels.DeltaFun τ‖ ≤ CΔ * Real.exp (-(2 * Real.pi * τ.im)) := by
    calc ‖Work.Kernels.DeltaFun τ‖ ≤ CΔ * ‖Work.Kernels.qParamFun τ‖ := hΔ τ hτ
      _ = CΔ * Real.exp (-(2 * Real.pi * τ.im)) := by rw [Work.Asymptotics.norm_qParamFun]
  have h4e : ‖Work.Kernels.E4Fun τ‖ ≤ C4 := h4 τ hτ
  rw [norm_mul]
  have hexp0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * τ.im)) := (Real.exp_pos _).le
  calc ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.E4Fun τ‖
      ≤ (CΔ * Real.exp (-(2 * Real.pi * τ.im))) * C4 :=
        mul_le_mul hΔe h4e (norm_nonneg _) (by positivity)
    _ = (CΔ * C4) * Real.exp (-(2 * Real.pi * τ.im)) := by ring
    _ ≤ (CΔ * C4 + 1) * Real.exp (-(2 * Real.pi * τ.im)) := by
        nlinarith [hexp0, mul_nonneg hCΔ.le hC4.le]

private lemma Delta_mul_T8 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) :
    Work.Kernels.DeltaFun τ * Work.Asymptotics.T8 ℓ τ z
      = -3456 * (Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ) *
            (Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z * ℓ.L_S z)
        + 1728 * (Work.Kernels.DeltaFun τ * Work.Kernels.psi4 ℓ τ) *
            (Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z * (-(Work.Kernels.VFun z)))
        + (Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ) *
            ((Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z *
                (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))
              - (Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z * (-(Work.Kernels.VFun z)))) := by
  have hDne : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hA0 : Work.Asymptotics.Alpha ℓ 8 0 τ = Work.Kernels.E4Fun τ := by
    simp only [Work.Asymptotics.Alpha, Work.Kernels.psiVec, Work.Asymptotics.vlen, Work.Kernels.fk,
      Matrix.cons_val_zero]
    norm_num
  have hA1 : Work.Asymptotics.Alpha ℓ 8 1 τ
      = Work.Kernels.psi2 ℓ τ * (Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ) := by
    simp only [Work.Asymptotics.Alpha, Work.Kernels.psiVec, Work.Asymptotics.vlen, Work.Kernels.fk,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hA2 : Work.Asymptotics.Alpha ℓ 8 2 τ = Work.Kernels.psi4 ℓ τ := by
    have hv : (Work.Asymptotics.vlen 8) 2 = 0 := by
      simp only [Work.Asymptotics.vlen, if_true]; decide
    simp only [Work.Asymptotics.Alpha, Work.Kernels.psiVec, Work.Kernels.fk, hv,
      Matrix.cons_val_two]
    norm_num
  have hLam : Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ
      = Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.psi2 ℓ τ * Work.Kernels.E14Fun τ := by
    rw [Work.Residues.Lamb_eq]
    rw [mul_div_cancel₀ _ hDne]
  rw [Work.Asymptotics.T8, hA0, hA1, hA2, hLam]
  simp only [Work.Kernels.jInvariantFun]
  field_simp [hDne]
  ring

private lemma fk_ulen8_zero (z : UpperHalfPlane) :
    Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z = Work.Kernels.E10Fun z := by
  rw [Work.Asymptotics.ulen8_zero, Work.Asymptotics.fk_ten_eq]

private lemma fk_ulen8_one (z : UpperHalfPlane) :
    Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z = Work.Kernels.E8Fun z := by
  rw [Work.Asymptotics.ulen8_one, Work.Asymptotics.fk_eight_eq]

private lemma fk_ulen8_two (z : UpperHalfPlane) :
    Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z = Work.Kernels.E6Fun z := by
  rw [Work.Asymptotics.ulen8_two, Work.Asymptotics.fk_six_eq]

/-- The three `z`-factors of `Δ τ · T₈`. -/
private lemma zfact_bounds (ℓ : Work.Kernels.LogLambdaData)
    (hz : ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im →
      ‖Work.Kernels.E10Fun z * ℓ.L_S z‖ ≤ C * Real.exp (-(Real.pi * z.im)) ∧
      ‖Work.Kernels.E8Fun z * Work.Kernels.VFun z‖ ≤ C * Real.exp (-(Real.pi * z.im)) ∧
      ‖Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖
        ≤ C * Real.exp (-(Real.pi * z.im))) :
    ∃ Cz : ℝ, 0 < Cz ∧ ∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im →
      ‖Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z * ℓ.L_S z‖
          ≤ Cz * Real.exp (-(Real.pi * z.im)) ∧
      ‖Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z * (-(Work.Kernels.VFun z))‖
          ≤ Cz * Real.exp (-(Real.pi * z.im)) ∧
      ‖Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z *
          (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖
          ≤ Cz * Real.exp (-(Real.pi * z.im)) := by
  obtain ⟨Cz, hCz, hzall⟩ := hz
  refine ⟨Cz, hCz, fun z hzz => ⟨?_, ?_, ?_⟩⟩
  · rw [fk_ulen8_zero]; exact (hzall z hzz).1
  · rw [fk_ulen8_one,
      show Work.Kernels.E8Fun z * (-(Work.Kernels.VFun z))
        = -(Work.Kernels.E8Fun z * Work.Kernels.VFun z) by ring, norm_neg]
    exact (hzall z hzz).2.1
  · rw [fk_ulen8_two]; exact (hzall z hzz).2.2

/-- Assembly: the target bound follows from the three ingredient bounds. -/
private lemma ncusp8_assembly (ℓ : Work.Kernels.LogLambdaData)
    (hψ4 : ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ τ : UpperHalfPlane, (1 : ℝ) / 3 ≤ τ.im →
      ‖Work.Kernels.DeltaFun τ * Work.Kernels.psi4 ℓ τ‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im)))
    (hΛ : ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ τ : UpperHalfPlane, (1 : ℝ) / 3 ≤ τ.im →
      ‖Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im)))
    (hz : ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im →
      ‖Work.Kernels.E10Fun z * ℓ.L_S z‖ ≤ C * Real.exp (-(Real.pi * z.im)) ∧
      ‖Work.Kernels.E8Fun z * Work.Kernels.VFun z‖ ≤ C * Real.exp (-(Real.pi * z.im)) ∧
      ‖Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖
        ≤ C * Real.exp (-(Real.pi * z.im))) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ τ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ τ.im →
      (1 : ℝ) / 3 ≤ z.im →
      ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Ncusp ℓ 8 τ z‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A *
            Real.exp (-(Real.pi * (2 * τ.im + z.im))) := by
  obtain ⟨Cψ, Aψ, hCψ, hAψpos, hψ⟩ := hψ4
  obtain ⟨CΛ, AΛ, hCΛ, hAΛpos, hΛb⟩ := hΛ
  obtain ⟨Cz, hCz, hzf⟩ := zfact_bounds ℓ hz
  obtain ⟨CE4, hCE4, hE4⟩ := DeltaFun_E4_bound_third
  refine ⟨‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ *
      (3456 * CE4 * Cz + 1728 * Cψ * Cz + CΛ * (2 * Cz)) + 1, max Aψ AΛ,
      by positivity, le_trans hAψpos (le_max_left _ _), ?_⟩
  intro τ z hτ hzτ
  set A : ℝ := max Aψ AΛ with hA
  set K : ℝ := 3456 * CE4 * Cz + 1728 * Cψ * Cz + CΛ * (2 * Cz) with hK
  set E2 : ℝ := Real.exp (-(2 * Real.pi * τ.im)) with hE2
  set E1 : ℝ := Real.exp (-(Real.pi * z.im)) with hE1
  have hE20 : 0 ≤ E2 := by rw [hE2]; positivity
  have hE10 : 0 ≤ E1 := by rw [hE1]; positivity
  have hsτ1 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by have := norm_nonneg (τ : ℂ); linarith
  have hsτ0 : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := le_trans zero_le_one hsτ1
  have hAψle : Aψ ≤ A := by rw [hA]; exact le_max_left _ _
  have hAΛle : AΛ ≤ A := by rw [hA]; exact le_max_right _ _
  have hsAψ : (1 + ‖(τ : ℂ)‖) ^ Aψ ≤ (1 + ‖(τ : ℂ)‖) ^ A :=
    Real.rpow_le_rpow_of_exponent_le hsτ1 hAψle
  have hsAΛ : (1 + ‖(τ : ℂ)‖) ^ AΛ ≤ (1 + ‖(τ : ℂ)‖) ^ A :=
    Real.rpow_le_rpow_of_exponent_le hsτ1 hAΛle
  have hpow_ge1 : (1 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A := Real.one_le_rpow hsτ1 (le_trans hAψpos hAψle)
  have hZ0 : ‖Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z * ℓ.L_S z‖ ≤ Cz * E1 :=
    (hzf z hzτ).1
  have hZ1 : ‖Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z * (-(Work.Kernels.VFun z))‖ ≤ Cz * E1 :=
    (hzf z hzτ).2.1
  have hZ2 : ‖Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z *
      (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖ ≤ Cz * E1 := (hzf z hzτ).2.2
  have hZ21 : ‖Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z *
        (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)
      - Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z * (-(Work.Kernels.VFun z))‖
      ≤ (2 * Cz) * E1 := by
    calc ‖Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z *
            (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)
          - Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z * (-(Work.Kernels.VFun z))‖
        ≤ ‖Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z *
            (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖
          + ‖Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z * (-(Work.Kernels.VFun z))‖ :=
          norm_sub_le _ _
      _ ≤ Cz * E1 + Cz * E1 := add_le_add hZ2 hZ1
      _ = (2 * Cz) * E1 := by ring
  have e1 : ‖(-3456 : ℂ) * (Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ) *
        (Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z * ℓ.L_S z)‖
      ≤ (3456 * CE4 * Cz) * (1 + ‖(τ : ℂ)‖) ^ A * (E2 * E1) := by
    rw [norm_mul, norm_mul, show ‖(-3456 : ℂ)‖ = 3456 by norm_num]
    calc 3456 * ‖Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ‖ *
            ‖Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z * ℓ.L_S z‖
        ≤ 3456 * (CE4 * E2) * (Cz * E1) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hE4 τ hτ) (by norm_num)) hZ0 (norm_nonneg _)
            (by positivity)
      _ = (3456 * CE4 * Cz) * (E2 * E1) := by ring
      _ ≤ (3456 * CE4 * Cz) * ((1 + ‖(τ : ℂ)‖) ^ A * (E2 * E1)) := by
          have hc : (0 : ℝ) ≤ 3456 * CE4 * Cz := by positivity
          have hx : (0 : ℝ) ≤ E2 * E1 := by positivity
          have hmul : E2 * E1 ≤ (1 + ‖(τ : ℂ)‖) ^ A * (E2 * E1) := by
            have h := mul_le_mul_of_nonneg_right hpow_ge1 hx
            simpa using h
          exact mul_le_mul_of_nonneg_left hmul hc
      _ = (3456 * CE4 * Cz) * (1 + ‖(τ : ℂ)‖) ^ A * (E2 * E1) := by ring
  have e2 : ‖(1728 : ℂ) * (Work.Kernels.DeltaFun τ * Work.Kernels.psi4 ℓ τ) *
        (Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z * (-(Work.Kernels.VFun z)))‖
      ≤ (1728 * Cψ * Cz) * (1 + ‖(τ : ℂ)‖) ^ A * (E2 * E1) := by
    rw [norm_mul, norm_mul, show ‖(1728 : ℂ)‖ = 1728 by norm_num]
    calc 1728 * ‖Work.Kernels.DeltaFun τ * Work.Kernels.psi4 ℓ τ‖ *
            ‖Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z * (-(Work.Kernels.VFun z))‖
        ≤ 1728 * (Cψ * (1 + ‖(τ : ℂ)‖) ^ Aψ * E2) * (Cz * E1) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hψ τ hτ) (by norm_num)) hZ1 (norm_nonneg _)
            (by positivity)
      _ = (1728 * Cψ * (1 + ‖(τ : ℂ)‖) ^ Aψ * Cz) * (E2 * E1) := by ring
      _ ≤ (1728 * Cψ * (1 + ‖(τ : ℂ)‖) ^ A * Cz) * (E2 * E1) := by
          have hx : (0 : ℝ) ≤ E2 * E1 := by positivity
          have h1 : 1728 * Cψ * (1 + ‖(τ : ℂ)‖) ^ Aψ
              ≤ 1728 * Cψ * (1 + ‖(τ : ℂ)‖) ^ A :=
            mul_le_mul_of_nonneg_left hsAψ (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hCz.le) hx
      _ = (1728 * Cψ * Cz) * (1 + ‖(τ : ℂ)‖) ^ A * (E2 * E1) := by ring
  have e3 : ‖(Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ) *
        ((Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z *
            (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))
          - (Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z * (-(Work.Kernels.VFun z))))‖
      ≤ (CΛ * (2 * Cz)) * (1 + ‖(τ : ℂ)‖) ^ A * (E2 * E1) := by
    rw [norm_mul]
    calc ‖Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ‖ *
            ‖(Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z *
                (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))
              - (Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z * (-(Work.Kernels.VFun z)))‖
        ≤ (CΛ * (1 + ‖(τ : ℂ)‖) ^ AΛ * E2) * ((2 * Cz) * E1) :=
          mul_le_mul (hΛb τ hτ) hZ21 (norm_nonneg _) (by positivity)
      _ = (CΛ * (2 * Cz) * (1 + ‖(τ : ℂ)‖) ^ AΛ) * (E2 * E1) := by ring
      _ ≤ (CΛ * (2 * Cz) * (1 + ‖(τ : ℂ)‖) ^ A) * (E2 * E1) := by
          have hx : (0 : ℝ) ≤ E2 * E1 := by positivity
          have h1 : CΛ * (2 * Cz) * (1 + ‖(τ : ℂ)‖) ^ AΛ
              ≤ CΛ * (2 * Cz) * (1 + ‖(τ : ℂ)‖) ^ A :=
            mul_le_mul_of_nonneg_left hsAΛ (by positivity)
          exact mul_le_mul_of_nonneg_right h1 hx
      _ = (CΛ * (2 * Cz)) * (1 + ‖(τ : ℂ)‖) ^ A * (E2 * E1) := by ring
  have hT8 : ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.T8 ℓ τ z‖
      ≤ K * (1 + ‖(τ : ℂ)‖) ^ A * (E2 * E1) := by
    rw [Delta_mul_T8]
    have htri : ‖(-3456 : ℂ) * (Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ) *
          (Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z * ℓ.L_S z)
        + (1728 : ℂ) * (Work.Kernels.DeltaFun τ * Work.Kernels.psi4 ℓ τ) *
          (Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z * (-(Work.Kernels.VFun z)))
        + (Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ) *
          ((Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z *
              (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))
            - (Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z * (-(Work.Kernels.VFun z))))‖
        ≤ (3456 * CE4 * Cz) * (1 + ‖(τ : ℂ)‖) ^ A * (E2 * E1)
          + (1728 * Cψ * Cz) * (1 + ‖(τ : ℂ)‖) ^ A * (E2 * E1)
          + (CΛ * (2 * Cz)) * (1 + ‖(τ : ℂ)‖) ^ A * (E2 * E1) := by
      refine le_trans (norm_add_le _ _) (add_le_add ?_ e3)
      exact le_trans (norm_add_le _ _) (add_le_add e1 e2)
    refine le_trans htri ?_
    have hsum : (3456 * CE4 * Cz) * (1 + ‖(τ : ℂ)‖) ^ A * (E2 * E1)
          + (1728 * Cψ * Cz) * (1 + ‖(τ : ℂ)‖) ^ A * (E2 * E1)
          + (CΛ * (2 * Cz)) * (1 + ‖(τ : ℂ)‖) ^ A * (E2 * E1)
        = K * (1 + ‖(τ : ℂ)‖) ^ A * (E2 * E1) := by
      rw [hK]; ring
    rw [hsum]
  have hN : Work.Kernels.DeltaFun τ * Work.Asymptotics.Ncusp ℓ 8 τ z
      = (2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹ *
          (Work.Kernels.DeltaFun τ * Work.Asymptotics.T8 ℓ τ z) := by
    rw [Work.Asymptotics.Ncusp_eight_expansion]; ring
  have hexp_eq : E2 * E1 = Real.exp (-(Real.pi * (2 * τ.im + z.im))) := by
    rw [hE2, hE1, ← Real.exp_add]; congr 1; ring
  have hsz : (1 : ℝ) ≤ 1 + ‖(z : ℂ)‖ := by have := norm_nonneg (z : ℂ); linarith
  have hszA : (1 : ℝ) ≤ (1 + ‖(z : ℂ)‖) ^ A := Real.one_le_rpow hsz (le_trans hAψpos hAψle)
  rw [hN, norm_mul]
  set C0 : ℝ := ‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ with hC0
  have hC00 : 0 ≤ C0 := by rw [hC0]; positivity
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hstep1 : C0 * ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.T8 ℓ τ z‖
      ≤ C0 * (K * (1 + ‖(τ : ℂ)‖) ^ A * (E2 * E1)) :=
    mul_le_mul_of_nonneg_left hT8 hC00
  rw [hexp_eq] at *
  refine le_trans hstep1 ?_
  have hCK0 : 0 ≤ C0 * K := mul_nonneg hC00 hK0
  have hB0 : 0 ≤ (1 + ‖(τ : ℂ)‖) ^ A := Real.rpow_nonneg hsτ0 A
  have hExp0 : 0 ≤ Real.exp (-(Real.pi * (2 * τ.im + z.im))) := (Real.exp_pos _).le
  have hBz0 : 0 ≤ (1 + ‖(z : ℂ)‖) ^ A := Real.rpow_nonneg (by positivity) A
  have hBBz : (1 + ‖(τ : ℂ)‖) ^ A ≤ (1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A := by
    have h := mul_le_mul_of_nonneg_left hszA hB0
    simpa using h
  have h1 : (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * (2 * τ.im + z.im)))
      ≤ ((1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A) *
          Real.exp (-(Real.pi * (2 * τ.im + z.im))) :=
    mul_le_mul_of_nonneg_right hBBz hExp0
  have h2 : C0 * K * ((1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * (2 * τ.im + z.im))))
      ≤ C0 * K * (((1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A) *
          Real.exp (-(Real.pi * (2 * τ.im + z.im)))) :=
    mul_le_mul_of_nonneg_left h1 hCK0
  have hX0 : 0 ≤ ((1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A) *
      Real.exp (-(Real.pi * (2 * τ.im + z.im))) :=
    mul_nonneg (mul_nonneg hB0 hBz0) hExp0
  have h3 : C0 * K * (((1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A) *
          Real.exp (-(Real.pi * (2 * τ.im + z.im))))
      ≤ (C0 * K + 1) * (((1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A) *
          Real.exp (-(Real.pi * (2 * τ.im + z.im)))) := by nlinarith [hX0]
  have he : C0 * (K * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * (2 * τ.im + z.im))))
      = C0 * K * ((1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * (2 * τ.im + z.im)))) := by ring
  rw [he]
  have hgoal : (C0 * K + 1) * (1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A *
        Real.exp (-(Real.pi * (2 * τ.im + z.im)))
      = (C0 * K + 1) * (((1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A) *
          Real.exp (-(Real.pi * (2 * τ.im + z.im)))) := by ring
  rw [hgoal]
  exact le_trans h2 h3

/-- **The requested bound.**  `Δ(τ) · Ncusp ℓ 8 τ z` decays like
`e^{-π(2 Im τ + Im z)}` up to a polynomial factor in `τ` and `z`, on `Im τ, Im z ≥ 1/3`. -/
theorem ncusp8_decay_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ τ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ τ.im → (1 : ℝ) / 3 ≤ z.im →
      ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Ncusp ℓ 8 τ z‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A *
            Real.exp (-(Real.pi * (2 * τ.im + z.im))) :=
  ncusp8_assembly ℓ (Ncusp8DB_tau_psi4 ℓ) (Ncusp8DB_tau_Lamb ℓ) (Ncusp8DB_zfact ℓ)

end

end Work.CKFinal.LineDecay
