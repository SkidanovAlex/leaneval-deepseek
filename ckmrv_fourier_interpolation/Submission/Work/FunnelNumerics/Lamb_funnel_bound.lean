/-
# The funnel bound for `Δ · Λ`

This file proves `Work.FunnelNumerics.Lamb_funnel_bound`: on the funnel
`{τ ∈ 𝒟 : 2 ≤ Im τ}` the product `Δ(τ)Λ(τ)` decays like the cusp parameter
`q(τ) = e^{2πiτ}`, up to a polynomial factor in the scale `S τ = 1 + (Im τ)⁻¹ + |τ|`.

The mathematics is the following.  Writing `ψ₂ = ξ₂𝓛 + (ξ₂|₂S)𝓛_S` and
`ψ₄ = ξ₄𝓛 + (ξ₄|₄S)𝓛_S` (CKMRV, Proposition 4.3) and using `Δ j = E₄³`, one has

  `Δ(τ) Λ(τ) = ψ₄(τ)E₄(τ)³ - ψ₂(τ)E₁₄(τ)
             = 𝓛(τ) · P₂(τ) + 𝓛_S(τ) · Q₂(τ)`,

where `P₂ = ξ₄E₄³ - ξ₂E₁₄` and `Q₂ = (ξ₄|₄S)E₄³ - (ξ₂|₂S)E₁₄` are the cusp combinations
of `Work.Residues.KMinusCuspDefs`.  Both vanish at the cusp: `P₂ = V²·S_{P₂}(U-1, V)` and
`Q₂ = V·S_{Q₂}(U-1, V)` with `‖V‖ ≤ C e^{-π Im τ}` (ThetaDecay), so

  `‖P₂ τ‖ ≤ C₂ tpar τ² = C₂ ‖q(τ)‖`,  `‖Q₂ τ‖ ≤ C₁ tpar τ`.

Finally `𝓛 ∈ 𝒫` has moderate growth (from the `LogLambdaData` axioms) while the companion
`𝓛_S` is identified with the explicit branch `Λ_S = 4 log θ₀₁ - 4 log θ₀₀`
(`LogLambdaData_LS_eq_LamS`), which is `O(tpar)` near the cusp (`LamSExpBound`).  Multiplying
out gives `ΔΛ = O(S^N · ‖q‖)`.
-/
import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.psi_InP
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Residues.ThetaExpansion
import Submission.Work.Residues.LamSExpBound
import Submission.Work.Residues.CuspPolyBounds
import Submission.Work.Residues.ThetaAux

set_option maxHeartbeats 1000000

namespace Work.FunnelNumerics

open UpperHalfPlane

noncomputable section

/-! ## A uniform bound for continuous functions of the cusp coordinates -/

/-- A continuous function of two variables is bounded on the closed ball of any radius. -/
lemma exists_norm_poly2_le_radius (S : ℂ → ℂ → ℂ)
    (hS : Continuous fun p : ℂ × ℂ => S p.1 p.2) {R : ℝ} (_hR : 0 ≤ R) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ a b : ℂ, ‖a‖ ≤ R → ‖b‖ ≤ R → ‖S a b‖ ≤ D := by
  have hcomp : IsCompact (Metric.closedBall (0 : ℂ × ℂ) R) := isCompact_closedBall _ _
  obtain ⟨D, hD⟩ := hcomp.exists_bound_of_continuousOn hS.continuousOn
  refine ⟨max D 0, le_max_right _ _, fun a b ha hb => ?_⟩
  have hmem : (a, b) ∈ Metric.closedBall (0 : ℂ × ℂ) R := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [sub_zero, Prod.norm_def]
    exact max_le ha hb
  exact le_trans (hD (a, b) hmem) (le_max_left _ _)

/-- On `{Im τ ≥ 2}` one has `‖V^k · S (U-1, V)‖ ≤ C tpar^k` for every continuous `S`. -/
lemma cusp_bound_two {S : ℂ → ℂ → ℂ}
    (hS : Continuous fun p : ℂ × ℂ => S p.1 p.2) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 2 ≤ τ.im →
      ‖Work.Residues.bcusp τ ^ k * S (Work.Residues.acusp τ) (Work.Residues.bcusp τ)‖
        ≤ C * Work.Residues.tpar τ ^ k := by
  obtain ⟨C1, hC1, h1⟩ := Work.Residues.ThetaDecay.1
  obtain ⟨C2, hC2, h2⟩ := Work.Residues.ThetaDecay.2.2.1
  have hR : (0 : ℝ) ≤ max C1 C2 := le_trans hC1.le (le_max_left _ _)
  obtain ⟨D, hD0, hD⟩ := exists_norm_poly2_le_radius S hS hR
  refine ⟨C2 ^ k * D + 1, by positivity, fun τ hτ => ?_⟩
  have hτ1 : 1 ≤ τ.im := by linarith
  have ht1 : Work.Residues.tpar τ ≤ 1 := Work.Residues.tpar_le_one τ
  have ht0 : 0 ≤ Work.Residues.tpar τ := (Work.Residues.tpar_pos τ).le
  have hb : ‖Work.Residues.bcusp τ‖ ≤ C2 * Work.Residues.tpar τ := by
    have h := h2 τ hτ1
    rw [← Work.Residues.tpar] at h
    exact h
  have ha : ‖Work.Residues.acusp τ‖ ≤ max C1 C2 := by
    show ‖Work.Kernels.UFun τ - 1‖ ≤ max C1 C2
    calc ‖Work.Kernels.UFun τ - 1‖ ≤ C1 * Real.exp (-(Real.pi * τ.im)) := h1 τ hτ1
      _ = C1 * Work.Residues.tpar τ := by rw [Work.Residues.tpar]
      _ ≤ C1 * 1 := mul_le_mul_of_nonneg_left ht1 hC1.le
      _ ≤ max C1 C2 := by rw [mul_one]; exact le_max_left _ _
  have hb' : ‖Work.Residues.bcusp τ‖ ≤ max C1 C2 := by
    have h := hb
    calc ‖Work.Residues.bcusp τ‖ ≤ C2 * 1 := by
          exact le_trans h (mul_le_mul_of_nonneg_left ht1 hC2.le)
      _ ≤ max C1 C2 := by rw [mul_one]; exact le_max_right _ _
  have hSbd : ‖S (Work.Residues.acusp τ) (Work.Residues.bcusp τ)‖ ≤ D := hD _ _ ha hb'
  have hpow : ‖Work.Residues.bcusp τ ^ k‖ ≤ C2 ^ k * Work.Residues.tpar τ ^ k := by
    rw [norm_pow]
    calc ‖Work.Residues.bcusp τ‖ ^ k ≤ (C2 * Work.Residues.tpar τ) ^ k :=
          pow_le_pow_left₀ (norm_nonneg _) hb k
      _ = C2 ^ k * Work.Residues.tpar τ ^ k := by rw [mul_pow]
  rw [norm_mul]
  have htk : 0 ≤ Work.Residues.tpar τ ^ k := pow_nonneg ht0 k
  calc ‖Work.Residues.bcusp τ ^ k‖ * ‖S (Work.Residues.acusp τ) (Work.Residues.bcusp τ)‖
      ≤ (C2 ^ k * Work.Residues.tpar τ ^ k) * D :=
        mul_le_mul hpow hSbd (norm_nonneg _) (by positivity)
    _ = C2 ^ k * D * Work.Residues.tpar τ ^ k := by ring
    _ ≤ (C2 ^ k * D + 1) * Work.Residues.tpar τ ^ k := by nlinarith [hD0, htk]

/-- `P₂ = ξ₄E₄³ - ξ₂E₁₄` is `O(tpar²) = O(‖q‖)` on `{Im τ ≥ 2}`. -/
lemma P2fun_cusp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 2 ≤ τ.im →
      ‖Work.Residues.P2fun τ‖ ≤ C * Work.Residues.tpar τ ^ 2 := by
  obtain ⟨C, hC, h⟩ :=
    cusp_bound_two (S := Work.Residues.S_P2) (by unfold Work.Residues.S_P2; fun_prop) 2
  exact ⟨C, hC, fun τ hτ => by rw [Work.Residues.P2fun_eq τ]; exact h τ hτ⟩

/-- `Q₂ = (ξ₄|₄S)E₄³ - (ξ₂|₂S)E₁₄` is `O(tpar)` on `{Im τ ≥ 2}`. -/
lemma Q2fun_cusp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 2 ≤ τ.im →
      ‖Work.Residues.Q2fun τ‖ ≤ C * Work.Residues.tpar τ := by
  obtain ⟨C, hC, h⟩ :=
    cusp_bound_two (S := Work.Residues.S_Q2) (by unfold Work.Residues.S_Q2; fun_prop) 1
  refine ⟨C, hC, fun τ hτ => ?_⟩
  simpa only [Work.Residues.Q2fun_eq τ, pow_one] using h τ hτ

/-! ## Growth of `𝓛` and exponential decay of `𝓛_S` on the funnel -/

/-- `𝓛` has moderate growth: `‖𝓛 τ‖ ≤ C S τ ^ N`. -/
lemma L_scale_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ τ : ℍ, ‖ℓ.L τ‖ ≤ C * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨α, N, hα, hN, h⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale Set.univ ℓ.L).mp ℓ.memP
  refine ⟨α + 1, N, by linarith, hN, fun τ => ?_⟩
  have h1 := h τ (Set.mem_univ τ)
  have h2 : 0 ≤ (Work.Kernels.scale τ) ^ N :=
    Real.rpow_nonneg (Work.Kernels.scale_pos τ).le N
  nlinarith [h1, h2]

/-- On the funnel, `‖𝓛_S τ‖ ≤ C tpar τ`: the companion logarithm decays like the cusp
parameter. -/
lemma LS_tpar_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 2 ≤ τ.im → ‖ℓ.L_S τ‖ ≤ C * Work.Residues.tpar τ := by
  obtain ⟨C, hC, h⟩ := Work.Residues.LamSExpBound
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have hhalf : (1 / 2 : ℝ) < τ.im := by linarith
  rw [Work.Residues.LogLambdaData_LS_eq_LamS ℓ τ hhalf]
  have hzW : (τ : ℂ) ∈ Work.Kernels.LogLambda.W := by
    show (1 / 2 : ℝ) < (τ : ℂ).im
    rw [UpperHalfPlane.coe_im]; exact hhalf
  have hz1 : (1 : ℝ) ≤ (τ : ℂ).im := by rw [UpperHalfPlane.coe_im]; linarith
  have h1 := h (τ : ℂ) hzW hz1
  have he : Real.exp (-(Real.pi * (τ : ℂ).im)) = Work.Residues.tpar τ := by
    rw [Work.Residues.tpar, UpperHalfPlane.coe_im]
  rwa [he] at h1

/-! ## The algebraic decomposition of `Δ Λ` -/

/-- `Δ Λ = 𝓛 P₂ + 𝓛_S Q₂`. -/
lemma Delta_mul_Lamb_eq (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ
      = ℓ.L τ * Work.Residues.P2fun τ + ℓ.L_S τ * Work.Residues.Q2fun τ := by
  have hD : Work.Kernels.DeltaFun τ ≠ 0 :=
    Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  simp only [Work.Residues.Lamb, Work.Kernels.psi2, Work.Kernels.psi4, Work.Residues.P2fun,
    Work.Residues.Q2fun, Work.Kernels.jInvariantFun]
  field_simp
  ring

/-! ## The main theorem -/

theorem Lamb_funnel_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ‖ ≤
        C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ := by
  obtain ⟨CL, NL, hCL, hNL, hL⟩ := L_scale_bound ℓ
  obtain ⟨CS, hCS, hLS⟩ := LS_tpar_bound ℓ
  obtain ⟨CP, hCP, hP⟩ := P2fun_cusp_bound
  obtain ⟨CQ, hCQ, hQ⟩ := Q2fun_cusp_bound
  refine ⟨CL * CP + CS * CQ, NL, by positivity, hNL, fun τ hτ => ?_⟩
  have hτ2 : 2 ≤ τ.im := hτ.2
  set t := Work.Residues.tpar τ with ht
  have ht0 : 0 ≤ t := (Work.Residues.tpar_pos τ).le
  have ht1 : t ≤ 1 := Work.Residues.tpar_le_one τ
  have hs1 : (1 : ℝ) ≤ (Work.Kernels.scale τ) ^ NL :=
    Real.one_le_rpow (Work.Kernels.one_le_scale τ) hNL
  have hs0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ NL :=
    Real.rpow_nonneg (Work.Kernels.scale_pos τ).le NL
  have hq : ‖Work.Kernels.qParamFun τ‖ = t ^ 2 := by
    rw [Work.Asymptotics.norm_qParamFun, ← Work.Residues.tpar_pow_two]
  rw [Delta_mul_Lamb_eq ℓ τ, hq]
  have hA : ‖ℓ.L τ‖ ≤ CL * (Work.Kernels.scale τ) ^ NL := hL τ
  have hB : ‖Work.Residues.P2fun τ‖ ≤ CP * t ^ 2 := hP τ hτ2
  have hC : ‖ℓ.L_S τ‖ ≤ CS * t := hLS τ hτ2
  have hDd : ‖Work.Residues.Q2fun τ‖ ≤ CQ * t := hQ τ hτ2
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

end

end Work.FunnelNumerics
