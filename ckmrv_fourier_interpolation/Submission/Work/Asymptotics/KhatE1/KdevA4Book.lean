import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.FunnelNumerics.E4_funnel_bounds
import Submission.Work.Asymptotics.KhatE1.Kdev8CoeffAux

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-!
# Monoid bookkeeping for the `K₊`-side `E(z)^4`-coefficient rung (`KdevA4plusBound`)

The three standalone estimates on which the assembly of `KdevA4plusBound` rests:
`‖z‖ ≤ 2(1+t)` on the strip, `‖j(τ)‖ = O(‖q(τ)‖⁻¹)`, and the same for `E₁₄(τ)/Δ(τ)`
(the latter two are the only sources of inverse powers of `‖q‖`; every other atom is
`O((scale τ)^N)`).
-/

/-- **The strip bound for `z`.**  For `-1 ≤ Re z ≤ 2` and `Im z = t`, `‖z‖ ≤ 2(1+t)`. -/
theorem kdevA4_norm_z_le (z : UpperHalfPlane) (t : ℝ) (h1 : -1 ≤ z.re) (h2 : z.re ≤ 2)
    (hz : z.im = t) : ‖(z : ℂ)‖ ≤ 2 * (1 + t) := by
  have hsq : ‖(z : ℂ)‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have h0 : (0 : ℝ) ≤ 1 + t := by rw [← hz]; linarith [z.im_pos]
  have hs : ‖(z : ℂ)‖ ^ 2 ≤ (2 * (1 + t)) ^ 2 := by
    rw [hsq, hz]
    nlinarith [h1, h2, z.im_pos]
  nlinarith [norm_nonneg (z : ℂ), h0]

/-- **`j(τ) = O(‖q(τ)‖⁻¹)`** on the funnel (from `j = E₄³/Δ`, `‖E₄‖ ≤ 3/2` and a lower bound
`c‖q‖ ≤ ‖Δ‖`). -/
theorem kdevA4_norm_j_le :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖Work.Kernels.jInvariantFun τ‖ ≤ C * (‖Work.Kernels.qParamFun τ‖)⁻¹ := by
  obtain ⟨cd, hcd, hd⟩ := Work.Asymptotics.exists_Delta_Funnel_lower
  refine ⟨27 / (8 * cd), by positivity, fun τ hτ => ?_⟩
  have hD : cd * ‖Work.Kernels.qParamFun τ‖ ≤ ‖Work.Kernels.DeltaFun τ‖ := by
    rw [Work.Asymptotics.norm_qParamFun]
    exact hd τ hτ
  have hE4 : ‖Work.Kernels.E4Fun τ‖ ≤ 3 / 2 := Work.FunnelNumerics.E4_funnel_bounds.1 τ hτ
  have hE43 : ‖Work.Kernels.E4Fun τ‖ ^ 3 ≤ 27 / 8 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hE4 3
    norm_num at h ⊢
    linarith
  have hqpos : (0 : ℝ) < cd * ‖Work.Kernels.qParamFun τ‖ :=
    mul_pos hcd (norm_pos_iff.mpr (Work.Asymptotics.qParamFun_ne_zero' τ))
  rw [Work.Kernels.jInvariantFun, norm_div, norm_pow]
  calc ‖Work.Kernels.E4Fun τ‖ ^ 3 / ‖Work.Kernels.DeltaFun τ‖
      ≤ (27 / 8) / (cd * ‖Work.Kernels.qParamFun τ‖) :=
        div_le_div₀ (by norm_num) hE43 hqpos hD
    _ = 27 / (8 * cd) * (‖Work.Kernels.qParamFun τ‖)⁻¹ := by
        field_simp

/-- `E₄` is bounded on the funnel (`= 3/2`). -/
theorem kdevA4_norm_E4_le :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖Work.Kernels.E4Fun τ‖ ≤ C :=
  ⟨3 / 2, by norm_num, fun τ hτ => Work.FunnelNumerics.E4_funnel_bounds.1 τ hτ⟩

/-- `E₆` is bounded on the funnel. -/
theorem kdevA4_norm_E6_le :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖Work.Kernels.E6Fun τ‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.E6Fun_bound
  exact ⟨C, hC, fun τ hτ => h τ (le_trans (by norm_num) hτ.2)⟩

/-- `φ₀(τ) = τE₂(τ) - 3i/π` is `O(scale τ)` on the funnel. -/
theorem kdevA4_norm_phi0_le :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖Work.Kernels.phi0 τ‖ ≤ C * Work.Kernels.scale τ := by
  obtain ⟨M, hM, hM2⟩ := Work.Asymptotics.E2Fun_bound
  refine ⟨M + 3 / Real.pi, by positivity, fun τ hτ => ?_⟩
  have hE2 : ‖Work.Kernels.E2Fun τ‖ ≤ M := hM2 τ (le_trans (by norm_num) hτ.2)
  have hsc : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hsc0 : (0 : ℝ) ≤ Work.Kernels.scale τ := le_trans zero_le_one hsc
  have hτle : ‖(τ : ℂ)‖ ≤ Work.Kernels.scale τ := Work.Kernels.coe_norm_le_scale τ
  have hc : ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 3 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [Work.Kernels.phi0]
  calc ‖(τ : ℂ) * Work.Kernels.E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)‖
      ≤ ‖(τ : ℂ) * Work.Kernels.E2Fun τ‖ + ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ :=
        norm_sub_le _ _
    _ = ‖(τ : ℂ)‖ * ‖Work.Kernels.E2Fun τ‖ + 3 / Real.pi := by rw [norm_mul, hc]
    _ ≤ Work.Kernels.scale τ * M + 3 / Real.pi :=
        add_le_add (mul_le_mul hτle hE2 (norm_nonneg _) hsc0) le_rfl
    _ ≤ (M + 3 / Real.pi) * Work.Kernels.scale τ := by
        have h3 : 3 / Real.pi ≤ (3 / Real.pi) * Work.Kernels.scale τ := by
          calc 3 / Real.pi = (3 / Real.pi) * 1 := by ring
            _ ≤ (3 / Real.pi) * Work.Kernels.scale τ :=
                mul_le_mul_of_nonneg_left hsc (by positivity)
        nlinarith [hsc0, hM.le]

/-- `φ₂(τ) = τE₂(τ)² - (6i/π)E₂(τ)` is `O((scale τ)²)` on the funnel. -/
theorem kdevA4_norm_phi2_le :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖Work.Kernels.phi2 τ‖ ≤ C * (Work.Kernels.scale τ) ^ 2 := by
  obtain ⟨M, hM, hM2⟩ := Work.Asymptotics.E2Fun_bound
  refine ⟨M ^ 2 + 6 / Real.pi * M, by positivity, fun τ hτ => ?_⟩
  have hE2 : ‖Work.Kernels.E2Fun τ‖ ≤ M := hM2 τ (le_trans (by norm_num) hτ.2)
  have hsc : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hsc0 : (0 : ℝ) ≤ Work.Kernels.scale τ := le_trans zero_le_one hsc
  have hs2 : (1 : ℝ) ≤ (Work.Kernels.scale τ) ^ 2 := one_le_pow₀ hsc
  have hτle : ‖(τ : ℂ)‖ ≤ Work.Kernels.scale τ := Work.Kernels.coe_norm_le_scale τ
  have hc : ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 6 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [Work.Kernels.phi2]
  calc ‖(τ : ℂ) * (Work.Kernels.E2Fun τ) ^ 2
        - (6 : ℂ) * Complex.I / (Real.pi : ℂ) * Work.Kernels.E2Fun τ‖
      ≤ ‖(τ : ℂ) * (Work.Kernels.E2Fun τ) ^ 2‖
        + ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ) * Work.Kernels.E2Fun τ‖ := norm_sub_le _ _
    _ ≤ Work.Kernels.scale τ * M ^ 2 + 6 / Real.pi * M := by
        refine add_le_add ?_ ?_
        · rw [norm_mul, norm_pow]
          exact mul_le_mul hτle (pow_le_pow_left₀ (norm_nonneg _) hE2 2) (by positivity) hsc0
        · rw [norm_mul, hc]
          exact mul_le_mul_of_nonneg_left hE2 (by positivity)
    _ ≤ (M ^ 2 + 6 / Real.pi * M) * (Work.Kernels.scale τ) ^ 2 := by
        have h3 : 6 / Real.pi * M ≤ 6 / Real.pi * M * (Work.Kernels.scale τ) ^ 2 := by
          calc 6 / Real.pi * M = 6 / Real.pi * M * 1 := by ring
            _ ≤ 6 / Real.pi * M * (Work.Kernels.scale τ) ^ 2 :=
                mul_le_mul_of_nonneg_left hs2 (by positivity)
        have hsc2 : Work.Kernels.scale τ ≤ (Work.Kernels.scale τ) ^ 2 := by nlinarith [hsc]
        have h4 : Work.Kernels.scale τ * M ^ 2 ≤ M ^ 2 * (Work.Kernels.scale τ) ^ 2 := by
          calc Work.Kernels.scale τ * M ^ 2 = M ^ 2 * Work.Kernels.scale τ := by ring
            _ ≤ M ^ 2 * (Work.Kernels.scale τ) ^ 2 :=
                mul_le_mul_of_nonneg_left hsc2 (by positivity)
        calc Work.Kernels.scale τ * M ^ 2 + 6 / Real.pi * M
            ≤ M ^ 2 * (Work.Kernels.scale τ) ^ 2
              + 6 / Real.pi * M * (Work.Kernels.scale τ) ^ 2 := add_le_add h4 h3
          _ = (M ^ 2 + 6 / Real.pi * M) * (Work.Kernels.scale τ) ^ 2 := by ring

/-- `Λ = πi τ + cuspC ℓ` is `O(scale τ)`. -/
theorem kdevA4_cuspLin_le (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ‖
      ≤ (Real.pi + ‖Work.Asymptotics.Compact.cuspC ℓ‖ + 1) * Work.Kernels.scale τ := by
  have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have h1 : ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ)‖ = Real.pi * ‖(τ : ℂ)‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, hpi]
  have hsc : ‖(τ : ℂ)‖ ≤ Work.Kernels.scale τ := Work.Kernels.coe_norm_le_scale τ
  have hsc1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hc0 : (0 : ℝ) ≤ ‖Work.Asymptotics.Compact.cuspC ℓ‖ := norm_nonneg _
  have h3 : ‖Work.Asymptotics.Compact.cuspC ℓ‖
      ≤ ‖Work.Asymptotics.Compact.cuspC ℓ‖ * Work.Kernels.scale τ := by
    calc ‖Work.Asymptotics.Compact.cuspC ℓ‖ = ‖Work.Asymptotics.Compact.cuspC ℓ‖ * 1 := by ring
      _ ≤ ‖Work.Asymptotics.Compact.cuspC ℓ‖ * Work.Kernels.scale τ :=
          mul_le_mul_of_nonneg_left hsc1 hc0
  calc ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ‖
      ≤ ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ)‖ + ‖Work.Asymptotics.Compact.cuspC ℓ‖ :=
        norm_add_le _ _
    _ = Real.pi * ‖(τ : ℂ)‖ + ‖Work.Asymptotics.Compact.cuspC ℓ‖ := by rw [h1]
    _ ≤ Real.pi * Work.Kernels.scale τ + ‖Work.Asymptotics.Compact.cuspC ℓ‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hsc Real.pi_pos.le) le_rfl
    _ ≤ (Real.pi + ‖Work.Asymptotics.Compact.cuspC ℓ‖ + 1) * Work.Kernels.scale τ := by
        nlinarith [h3, mul_nonneg Real.pi_pos.le (le_trans zero_le_one hsc1)]

/-- **The psi-pair is `O((scale τ)^N)`** on the funnel. -/
theorem kdevA4_norm_psi_le (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      (‖Work.Kernels.psi2 ℓ τ‖ ≤ C * (Work.Kernels.scale τ) ^ N) ∧
      (‖Work.Kernels.psi4 ℓ τ‖ ≤ C * (Work.Kernels.scale τ) ^ N) := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.KhatE1Core.psi_individual_first_order ℓ
  refine ⟨2 * C + 2 * (Real.pi + ‖Work.Asymptotics.Compact.cuspC ℓ‖ + 1), max N 1,
    by positivity, le_trans hN (le_max_left _ _), fun τ hτ => ?_⟩
  obtain ⟨h2, h4⟩ := h τ hτ
  have hsc : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hsc0 : (0 : ℝ) ≤ Work.Kernels.scale τ := le_trans zero_le_one hsc
  have hsN : (Work.Kernels.scale τ) ^ N ≤ (Work.Kernels.scale τ) ^ (max N 1) :=
    Real.rpow_le_rpow_of_exponent_le hsc (le_max_left _ _)
  have hs1' : Work.Kernels.scale τ ≤ (Work.Kernels.scale τ) ^ (max N 1) := by
    simpa using (Real.rpow_le_rpow_of_exponent_le hsc
      (le_max_right (N : ℝ) (1 : ℝ) : (1 : ℝ) ≤ max N 1))
  have hq1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := by
    rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hτ.2]
  have hlin := kdevA4_cuspLin_le ℓ τ
  have hstep : ∀ X : ℂ, ‖X‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ →
      ‖X + 2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)‖
        ≤ (2 * C + 2 * (Real.pi + ‖Work.Asymptotics.Compact.cuspC ℓ‖ + 1))
            * (Work.Kernels.scale τ) ^ (max N 1) := by
    intro X hX
    have h2X : ‖(2 : ℂ) * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
        + Work.Asymptotics.Compact.cuspC ℓ)‖
        = 2 * ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ‖ := by
      rw [norm_mul, Complex.norm_ofNat]
    have ha : C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖
        ≤ C * (Work.Kernels.scale τ) ^ (max N 1) := by
      calc C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖
          ≤ C * (Work.Kernels.scale τ) ^ N * 1 :=
            mul_le_mul_of_nonneg_left hq1 (by positivity)
        _ = C * (Work.Kernels.scale τ) ^ N := by ring
        _ ≤ C * (Work.Kernels.scale τ) ^ (max N 1) := mul_le_mul_of_nonneg_left hsN hC.le
    have hb : 2 * ((Real.pi + ‖Work.Asymptotics.Compact.cuspC ℓ‖ + 1) * Work.Kernels.scale τ)
        ≤ 2 * (Real.pi + ‖Work.Asymptotics.Compact.cuspC ℓ‖ + 1)
            * (Work.Kernels.scale τ) ^ (max N 1) := by
      have h0 : (0 : ℝ) ≤ 2 * (Real.pi + ‖Work.Asymptotics.Compact.cuspC ℓ‖ + 1) := by positivity
      calc 2 * ((Real.pi + ‖Work.Asymptotics.Compact.cuspC ℓ‖ + 1) * Work.Kernels.scale τ)
          = (2 * (Real.pi + ‖Work.Asymptotics.Compact.cuspC ℓ‖ + 1)) * Work.Kernels.scale τ := by ring
        _ ≤ (2 * (Real.pi + ‖Work.Asymptotics.Compact.cuspC ℓ‖ + 1))
              * (Work.Kernels.scale τ) ^ (max N 1) := mul_le_mul_of_nonneg_left hs1' h0
    calc ‖X + 2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)‖
        ≤ ‖X‖ + ‖(2 : ℂ) * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
            + Work.Asymptotics.Compact.cuspC ℓ)‖ := norm_add_le _ _
      _ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖
            + 2 * ((Real.pi + ‖Work.Asymptotics.Compact.cuspC ℓ‖ + 1) * Work.Kernels.scale τ) := by
          rw [h2X]
          exact add_le_add hX (mul_le_mul_of_nonneg_left hlin (by norm_num))
      _ ≤ (2 * C + 2 * (Real.pi + ‖Work.Asymptotics.Compact.cuspC ℓ‖ + 1))
            * (Work.Kernels.scale τ) ^ (max N 1) := by
          have hsum : C + 2 * (Real.pi + ‖Work.Asymptotics.Compact.cuspC ℓ‖ + 1)
              ≤ 2 * C + 2 * (Real.pi + ‖Work.Asymptotics.Compact.cuspC ℓ‖ + 1) := by linarith
          linarith [ha, hb,
            mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg hsc0 (max N 1))]
  constructor
  · have he : Work.Kernels.psi2 ℓ τ
        = (Work.Kernels.psi2 ℓ τ - 2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
            + Work.Asymptotics.Compact.cuspC ℓ))
          + 2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) := by ring
    rw [he]
    exact hstep _ h2
  · have he : Work.Kernels.psi4 ℓ τ
        = (Work.Kernels.psi4 ℓ τ - 2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
            + Work.Asymptotics.Compact.cuspC ℓ))
          + 2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) := by ring
    rw [he]
    exact hstep _ h4

/-- **`E₁₄(τ)/Δ(τ) = O((scale τ)^N ‖q(τ)‖⁻¹)`** on the funnel (`E₁₄ = E₄² E₆`, and
`c‖q‖ ≤ ‖Δ‖`). -/
theorem kdevA4_norm_E14_div_Delta_le :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ‖
        ≤ C * (Work.Kernels.scale τ) ^ N * (‖Work.Kernels.qParamFun τ‖)⁻¹ := by
  obtain ⟨C4, hC4, h4⟩ := kdevA4_norm_E4_le
  obtain ⟨C6, hC6, h6⟩ := kdevA4_norm_E6_le
  obtain ⟨cd, hcd, hd⟩ := Work.Asymptotics.exists_Delta_Funnel_lower
  refine ⟨C4 ^ 2 * C6 / cd, 0, by positivity, le_rfl, fun τ hτ => ?_⟩
  have hE4 : ‖Work.Kernels.E4Fun τ‖ ≤ C4 := h4 τ hτ
  have hE6 : ‖Work.Kernels.E6Fun τ‖ ≤ C6 := h6 τ hτ
  have hD' : cd * ‖Work.Kernels.qParamFun τ‖ ≤ ‖Work.Kernels.DeltaFun τ‖ := by
    rw [Work.Asymptotics.norm_qParamFun]
    exact hd τ hτ
  have hDpos : (0 : ℝ) < cd * ‖Work.Kernels.qParamFun τ‖ :=
    mul_pos hcd (norm_pos_iff.mpr (Work.Asymptotics.qParamFun_ne_zero' τ))
  have hE14 : ‖Work.Kernels.E14Fun τ‖ ≤ C4 ^ 2 * C6 := by
    have h1 : ‖Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ‖ ≤ C4 ^ 2 * C6 := by
      rw [norm_mul, norm_pow]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hE4 2) hE6 (norm_nonneg _)
        (by positivity)
    simpa only [Work.Kernels.E14Fun] using h1
  simp only [Real.rpow_zero, mul_one]
  rw [norm_div]
  calc ‖Work.Kernels.E14Fun τ‖ / ‖Work.Kernels.DeltaFun τ‖
      ≤ (C4 ^ 2 * C6) / (cd * ‖Work.Kernels.qParamFun τ‖) :=
        div_le_div₀ (by positivity) hE14 hDpos hD'
    _ = C4 ^ 2 * C6 / cd * (‖Work.Kernels.qParamFun τ‖)⁻¹ := by
        rw [div_eq_mul_inv, mul_inv]
        ring

end

end Work.Asymptotics.KhatE1
