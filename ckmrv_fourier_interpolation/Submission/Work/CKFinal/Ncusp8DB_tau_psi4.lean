import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.psi_InP
import Submission.Work.Asymptotics.KPlusFunnel.ZFacts
import Submission.Work.Asymptotics.KMinusFunnelZBounds

namespace Work.CKFinal

/-- `Δ · ψ₄` decays like the cusp parameter `e^{-2π Im τ}` up to a polynomial factor on the
region `Im τ ≥ 1/3`.

The two inputs are the classical `Δ = O(q)` bound `Work.Asymptotics.delta_upper_third`
(`‖Δ τ‖ ≤ C ‖q(τ)‖ = C e^{-2π Im τ}`) and the moderate growth of `ψ₄` supplied by
`Work.Asymptotics.psi_InP`, translated from the paper's form (4.1) into the polynomial form
`‖ψ₄ τ‖ ≤ α' (1 + ‖τ‖)^A`. -/
theorem Ncusp8DB_tau_psi4 (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ τ : UpperHalfPlane, (1 : ℝ) / 3 ≤ τ.im →
      ‖Work.Kernels.DeltaFun τ * Work.Kernels.psi4 ℓ τ‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im)) := by
  obtain ⟨CΔ, hCΔpos, hΔb⟩ := Work.Asymptotics.delta_upper_third
  obtain ⟨_, hgr⟩ := (Work.Asymptotics.psi_InP ℓ).2
  obtain ⟨α, β, γ, hα, hβ, hγ, hbd⟩ := hgr
  set A : ℝ := max β γ with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; exact le_trans hβ (le_max_left β γ)
  refine ⟨CΔ * (α + 1) * ((3 : ℝ) ^ A + 1) + 1, A, ?_, hA0, fun τ hτ => ?_⟩
  · have hK0 : 0 ≤ (3 : ℝ) ^ A + 1 := by
      have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) A
      linarith
    have h1 : 0 ≤ α + 1 := by linarith
    have h2 : 0 ≤ CΔ * (α + 1) := mul_nonneg hCΔpos.le h1
    have h3 : 0 ≤ CΔ * (α + 1) * ((3 : ℝ) ^ A + 1) := mul_nonneg h2 hK0
    linarith
  · have hy : 0 < τ.im := lt_of_lt_of_le (by norm_num) hτ
    have hu : 0 ≤ ‖(τ : ℂ)‖ := norm_nonneg _
    have h1u : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by linarith
    have h1u0 : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by linarith
    have hD := hΔb τ hτ
    rw [Work.Asymptotics.norm_qParamFun τ] at hD
    have hP := hbd τ (Set.mem_univ τ)
    have hinv : (τ.im)⁻¹ ≤ (3 : ℝ) := by
      have h := (inv_le_inv₀ hy (by norm_num : (0 : ℝ) < 1 / 3)).mpr hτ
      rwa [show ((1 : ℝ) / 3)⁻¹ = 3 from by norm_num] at h
    have hpow1 : (τ.im)⁻¹ ^ β ≤ (3 : ℝ) ^ A := by
      have h1 : (τ.im)⁻¹ ^ β ≤ (3 : ℝ) ^ β :=
        Real.rpow_le_rpow (inv_nonneg.mpr hy.le) hinv hβ
      have h2 : (3 : ℝ) ^ β ≤ (3 : ℝ) ^ A := by
        rw [hAdef]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_max_left β γ)
      exact h1.trans h2
    have hpow2 : ‖(τ : ℂ)‖ ^ γ ≤ (1 + ‖(τ : ℂ)‖) ^ A := by
      have h1 : ‖(τ : ℂ)‖ ^ γ ≤ (1 + ‖(τ : ℂ)‖) ^ γ :=
        Real.rpow_le_rpow hu (by linarith) hγ
      have h2 : (1 + ‖(τ : ℂ)‖) ^ γ ≤ (1 + ‖(τ : ℂ)‖) ^ A := by
        rw [hAdef]
        exact Real.rpow_le_rpow_of_exponent_le h1u (le_max_right β γ)
      exact h1.trans h2
    have h3A0 : 0 ≤ (3 : ℝ) ^ A := Real.rpow_nonneg (by norm_num) A
    have hUA : 0 ≤ (1 + ‖(τ : ℂ)‖) ^ A := Real.rpow_nonneg h1u0 A
    have hle2 : (1 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A := Real.one_le_rpow h1u hA0
    have hsum : (τ.im)⁻¹ ^ β + ‖(τ : ℂ)‖ ^ γ
        ≤ ((3 : ℝ) ^ A + 1) * (1 + ‖(τ : ℂ)‖) ^ A := by
      calc (τ.im)⁻¹ ^ β + ‖(τ : ℂ)‖ ^ γ
          ≤ (3 : ℝ) ^ A + (1 + ‖(τ : ℂ)‖) ^ A := add_le_add hpow1 hpow2
        _ ≤ (3 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A + (1 + ‖(τ : ℂ)‖) ^ A := by
            have := mul_le_mul_of_nonneg_left hle2 h3A0
            linarith
        _ = ((3 : ℝ) ^ A + 1) * (1 + ‖(τ : ℂ)‖) ^ A := by ring
    have hKU : 0 ≤ ((3 : ℝ) ^ A + 1) * (1 + ‖(τ : ℂ)‖) ^ A :=
      mul_nonneg (by linarith) hUA
    have hP' : ‖Work.Kernels.psi4 ℓ τ‖
        ≤ (α + 1) * (((3 : ℝ) ^ A + 1) * (1 + ‖(τ : ℂ)‖) ^ A) := by
      calc ‖Work.Kernels.psi4 ℓ τ‖ ≤ α * ((τ.im)⁻¹ ^ β + ‖(τ : ℂ)‖ ^ γ) := hP
        _ ≤ α * (((3 : ℝ) ^ A + 1) * (1 + ‖(τ : ℂ)‖) ^ A) :=
              mul_le_mul_of_nonneg_left hsum hα
        _ ≤ (α + 1) * (((3 : ℝ) ^ A + 1) * (1 + ‖(τ : ℂ)‖) ^ A) :=
              mul_le_mul_of_nonneg_right (by linarith) hKU
    have he0 : 0 ≤ Real.exp (-(2 * Real.pi * τ.im)) := (Real.exp_pos _).le
    have hCe0 : 0 ≤ CΔ * Real.exp (-(2 * Real.pi * τ.im)) :=
      mul_nonneg hCΔpos.le he0
    calc ‖Work.Kernels.DeltaFun τ * Work.Kernels.psi4 ℓ τ‖
        = ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.psi4 ℓ τ‖ := norm_mul _ _
      _ ≤ (CΔ * Real.exp (-(2 * Real.pi * τ.im)))
            * ((α + 1) * (((3 : ℝ) ^ A + 1) * (1 + ‖(τ : ℂ)‖) ^ A)) :=
            mul_le_mul hD hP' (norm_nonneg _) hCe0
      _ = (CΔ * (α + 1) * ((3 : ℝ) ^ A + 1)) * (1 + ‖(τ : ℂ)‖) ^ A
            * Real.exp (-(2 * Real.pi * τ.im)) := by ring
      _ ≤ (CΔ * (α + 1) * ((3 : ℝ) ^ A + 1) + 1) * (1 + ‖(τ : ℂ)‖) ^ A
            * Real.exp (-(2 * Real.pi * τ.im)) := by
            apply mul_le_mul_of_nonneg_right _ he0
            apply mul_le_mul_of_nonneg_right _ hUA
            linarith

end Work.CKFinal
