/-
# Funnel atom bounds for the `d = 24` tail estimate (private auxiliary file)

Atom bounds on the funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}` and on the contour `z = i t` (`t ≥ Im τ + 1`)
used by `Work.Asymptotics.KMinusFunnelMainBound`.

The `τ`-atoms (`ψ₂E₁₀`, `ψ₄E₈`, `Δ`, `j`, `E₄³`) grow at most like `(scale τ)^N` (times
`e^{2π Im τ}` for the `j`-monomials); the `z`-atoms are bounded resp. `O(‖Ept z‖^{±k})` by the
cusp expansions `cusp_invDelta`, `cusp_W_second`, `cusp_D_second`, `cusp_L_second` and the
two-term expansions of `E₄`, `E₆` (from which the `E₁₀`, `E₁₄` deviations are derived).
-/
import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.funnelTailQuant
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Compact.kminus_tail_aux
import Submission.Work.FunnelNumerics.E4_funnel_bounds
import Submission.Work.FunnelNumerics.Lamb_funnel_bound
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.cusp_W_second
import Submission.Work.Asymptotics.cusp_D_second
import Submission.Work.Asymptotics.cusp_invDelta
import Submission.Work.Asymptotics.cusp_L_second

set_option maxHeartbeats 1000000

namespace Work.Asymptotics.Funnel24

open UpperHalfPlane
open Work.Kernels
open Work.Residues (Ept)
open Work.Asymptotics.Compact

noncomputable section

/-! ## Elementary helpers -/

theorem scale_rpow_nonneg' (τ : ℍ) (N : ℝ) : 0 ≤ (scale τ) ^ N :=
  Real.rpow_nonneg (le_of_lt (scale_pos τ)) N

theorem one_le_scale_rpow' (τ : ℍ) {N : ℝ} (hN : 0 ≤ N) : 1 ≤ (scale τ) ^ N :=
  Real.one_le_rpow (one_le_scale τ) hN

/-- Absorb a constant into the `(scale τ)^N` factor. -/
theorem le_max_one_mul {a N : ℝ} (ha : 0 ≤ a) (hN : 0 ≤ N) (τ : ℍ) :
    a ≤ max a 1 * (scale τ) ^ N := by
  have hs : 1 ≤ (scale τ) ^ N := one_le_scale_rpow' τ hN
  calc a ≤ max a 1 := le_max_left _ _
    _ = max a 1 * 1 := by ring
    _ ≤ max a 1 * (scale τ) ^ N := mul_le_mul_of_nonneg_left hs (le_trans ha (le_max_left _ _))

/-- Absorb a constant into a constant `C`. -/
theorem le_max_one {a : ℝ} (ha : 0 ≤ a) : a ≤ max a 1 := le_max_left _ _


/-- `e^A · e^{-A} = 1`. -/
theorem exp_mul_exp_neg (A : ℝ) : Real.exp A * Real.exp (-A) = 1 := by
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- `e^A · e^A · e^{-A} = e^A`. -/
theorem exp_mul_exp_mul_exp_neg (A : ℝ) : Real.exp A * Real.exp A * Real.exp (-A) = Real.exp A := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- `‖Ept z‖ ≤ 1` for `1 ≤ Im z`. -/
theorem norm_Ept_le_one' {z : ℍ} (hz : 1 ≤ z.im) : ‖Ept z‖ ≤ 1 := by
  rw [Work.Residues.norm_Ept]
  exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hz])

/-- The `q`-parameter is `Ept ²`. -/
theorem qParam_eq (z : ℍ) : qParamFun z = (Ept z) ^ 2 := Compact.qParamFun_eq_Ept_sq z

/-- `‖q(z)‖ ≤ 1` for `1 ≤ Im z`. -/
theorem norm_qParam_le_one {z : ℍ} (hz : 1 ≤ z.im) : ‖qParamFun z‖ ≤ 1 := by
  rw [qParam_eq, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (norm_Ept_le_one' hz)

/-! ## The `τ`-atoms on the funnel -/

/-- `‖j(τ)‖ ≤ (27/4) e^{2π Im τ}` on the funnel. -/
theorem norm_j_funnel (τ : ℍ) (hτ : Funnel τ) :
    ‖jInvariantFun τ‖ ≤ (27 / 4) * Real.exp (2 * Real.pi * τ.im) := by
  have hΔlow : (1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * τ.im)) ≤ ‖DeltaFun τ‖ := by
    rw [← norm_qParamFun]
    exact (Work.FunnelNumerics.Delta_funnel_bounds).1 τ hτ.2
  have hE4b : ‖E4Fun τ‖ ≤ (3 / 2 : ℝ) := (Work.FunnelNumerics.E4_funnel_bounds).1 τ hτ
  have hnum : ‖E4Fun τ ^ 3‖ ≤ (3 / 2 : ℝ) ^ 3 := by
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

/-- `‖j(τ) · Δ(τ)‖ = ‖E₄(τ)³‖ ≤ 27/8` on the funnel. -/
theorem norm_j_mul_Delta_funnel (τ : ℍ) (hτ : Funnel τ) :
    ‖jInvariantFun τ * DeltaFun τ‖ ≤ 27 / 8 := by
  rw [mul_comm, Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun]
  exact E4cube_funnel_le τ hτ

/-- `‖Δ(τ)‖ ≤ 2 e^{-2π Im τ}` on the funnel. -/
theorem norm_Delta_funnel (τ : ℍ) (hτ : Funnel τ) :
    ‖DeltaFun τ‖ ≤ 2 * Real.exp (-(2 * Real.pi * τ.im)) :=
  DeltaFun_le_two_exp τ (Funnel.im_one hτ)

/-- `E₆` is bounded on the funnel. -/
theorem norm_E6_funnel : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ → ‖E6Fun τ‖ ≤ C :=
  exists_E6_Funnel_bound

/-- `‖ψ₂(τ)E₁₀(τ)‖ ≤ C (scale τ)^N` on the funnel. -/
theorem psi2E10_funnel (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖psi2 ℓ τ * E10Fun τ‖ ≤ C * (scale τ) ^ N := by
  obtain ⟨Cψ, Nψ, hCψ, hNψ, hψ⟩ := psi_scale_funnel ℓ
  obtain ⟨C6, hC6, h6⟩ := exists_E6_Funnel_bound
  refine ⟨Cψ * (3 / 2) * C6 + 1, Nψ, by positivity, hNψ, fun τ hτ => ?_⟩
  have hE4 : ‖E4Fun τ‖ ≤ 3 / 2 := (Work.FunnelNumerics.E4_funnel_bounds).1 τ hτ
  have hE6 : ‖E6Fun τ‖ ≤ C6 := h6 τ hτ
  have h10 : ‖E10Fun τ‖ ≤ (3 / 2) * C6 := by
    rw [show E10Fun τ = E4Fun τ * E6Fun τ from rfl, norm_mul]
    exact mul_le_mul hE4 hE6 (norm_nonneg _) (by positivity)
  have h2 := (hψ τ hτ).1
  have hs1 : (1 : ℝ) ≤ (scale τ) ^ Nψ := one_le_scale_rpow' τ hNψ
  have hs0 : (0 : ℝ) ≤ (scale τ) ^ Nψ := scale_rpow_nonneg' τ Nψ
  rw [norm_mul]
  calc ‖psi2 ℓ τ‖ * ‖E10Fun τ‖
      ≤ (Cψ * (scale τ) ^ Nψ) * ((3 / 2) * C6) :=
        mul_le_mul h2 h10 (norm_nonneg _) (by positivity)
    _ = (Cψ * (3 / 2) * C6) * (scale τ) ^ Nψ := by ring
    _ ≤ (Cψ * (3 / 2) * C6 + 1) * (scale τ) ^ Nψ := by nlinarith [hs0, hs1]

/-- `‖ψ₄(τ)E₈(τ)‖ ≤ C (scale τ)^N` on the funnel. -/
theorem psi4E8_funnel (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖psi4 ℓ τ * E8Fun τ‖ ≤ C * (scale τ) ^ N := by
  obtain ⟨Cψ, Nψ, hCψ, hNψ, hψ⟩ := psi_scale_funnel ℓ
  refine ⟨Cψ * (9 / 4) + 1, Nψ, by positivity, hNψ, fun τ hτ => ?_⟩
  have hE4 : ‖E4Fun τ‖ ≤ 3 / 2 := (Work.FunnelNumerics.E4_funnel_bounds).1 τ hτ
  have h8 : ‖E8Fun τ‖ ≤ (9 / 4 : ℝ) := by
    rw [show E8Fun τ = E4Fun τ ^ 2 from rfl, norm_pow]
    have h := pow_le_pow_left₀ (norm_nonneg _) hE4 2
    norm_num at h
    exact h
  have h2 := (hψ τ hτ).2
  have hs1 : (1 : ℝ) ≤ (scale τ) ^ Nψ := one_le_scale_rpow' τ hNψ
  have hs0 : (0 : ℝ) ≤ (scale τ) ^ Nψ := scale_rpow_nonneg' τ Nψ
  rw [norm_mul]
  calc ‖psi4 ℓ τ‖ * ‖E8Fun τ‖ ≤ (Cψ * (scale τ) ^ Nψ) * (9 / 4) :=
        mul_le_mul h2 h8 (norm_nonneg _) (by positivity)
    _ = (Cψ * (9 / 4)) * (scale τ) ^ Nψ := by ring
    _ ≤ (Cψ * (9 / 4) + 1) * (scale τ) ^ Nψ := by nlinarith [hs0, hs1]

/-- `‖ψ₄(τ)E₈(τ) - ψ₂(τ)E₁₀(τ)‖ ≤ C (scale τ)^N ‖q(τ)‖` on the funnel. -/
theorem psi_sub_funnel (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ‖
        ≤ C * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) := by
  obtain ⟨C, N, hC, hN, h⟩ := psi4E8_sub_psi2E10_funnel ℓ
  refine ⟨C, N, hC, hN, fun τ hτ => ?_⟩
  rw [← norm_qParamFun]
  exact h τ hτ

/-- `‖j(τ)(ψ₄(τ)E₈(τ) - ψ₂(τ)E₁₀(τ))‖ ≤ C (scale τ)^N` on the funnel. -/
theorem j_psi_sub_funnel (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
        ≤ C * (scale τ) ^ N := by
  obtain ⟨C, N, hC, hN, h⟩ := psi_sub_funnel ℓ
  refine ⟨(27 / 4) * C + 1, N, by positivity, hN, fun τ hτ => ?_⟩
  have hj := norm_j_funnel τ hτ
  have hd := h τ hτ
  have hexp : (27 / 4) * Real.exp (2 * Real.pi * τ.im)
      * (C * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))) = (27 / 4) * C * (scale τ) ^ N := by
    rw [show (27 / 4) * Real.exp (2 * Real.pi * τ.im)
        * (C * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)))
        = (27 / 4) * C * (scale τ) ^ N
          * (Real.exp (2 * Real.pi * τ.im) * Real.exp (-(2 * Real.pi * τ.im))) by ring]
    rw [exp_mul_exp_neg, mul_one]
  have hs1 : (1 : ℝ) ≤ (scale τ) ^ N := one_le_scale_rpow' τ hN
  have hs0 : (0 : ℝ) ≤ (scale τ) ^ N := scale_rpow_nonneg' τ N
  rw [norm_mul]
  calc ‖jInvariantFun τ‖ * ‖psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ‖
      ≤ ((27 / 4) * Real.exp (2 * Real.pi * τ.im))
          * (C * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))) :=
        mul_le_mul hj hd (norm_nonneg _) (by positivity)
    _ = (27 / 4) * C * (scale τ) ^ N := hexp
    _ ≤ ((27 / 4) * C + 1) * (scale τ) ^ N := by nlinarith [hs0, hs1]

/-- `‖j(τ) ψ₂(τ)E₁₀(τ)‖ ≤ C (scale τ)^N e^{2π Im τ}` on the funnel. -/
theorem j_psi2E10_funnel (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖jInvariantFun τ * (psi2 ℓ τ * E10Fun τ)‖
        ≤ C * (scale τ) ^ N * Real.exp (2 * Real.pi * τ.im) := by
  obtain ⟨C, N, hC, hN, h⟩ := psi2E10_funnel ℓ
  refine ⟨(27 / 4) * C, N, by nlinarith [hC], hN, fun τ hτ => ?_⟩
  have hj := norm_j_funnel τ hτ
  have hd := h τ hτ
  rw [norm_mul]
  calc ‖jInvariantFun τ‖ * ‖psi2 ℓ τ * E10Fun τ‖
      ≤ ((27 / 4) * Real.exp (2 * Real.pi * τ.im)) * (C * (scale τ) ^ N) :=
        mul_le_mul hj hd (norm_nonneg _) (by positivity)
    _ = (27 / 4) * C * (scale τ) ^ N * Real.exp (2 * Real.pi * τ.im) := by ring

/-- `‖j(τ) ψ₄(τ)E₈(τ)‖ ≤ C (scale τ)^N e^{2π Im τ}` on the funnel. -/
theorem j_psi4E8_funnel (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖jInvariantFun τ * (psi4 ℓ τ * E8Fun τ)‖
        ≤ C * (scale τ) ^ N * Real.exp (2 * Real.pi * τ.im) := by
  obtain ⟨C, N, hC, hN, h⟩ := psi4E8_funnel ℓ
  refine ⟨(27 / 4) * C, N, by nlinarith [hC], hN, fun τ hτ => ?_⟩
  have hj := norm_j_funnel τ hτ
  have hd := h τ hτ
  rw [norm_mul]
  calc ‖jInvariantFun τ‖ * ‖psi4 ℓ τ * E8Fun τ‖
      ≤ ((27 / 4) * Real.exp (2 * Real.pi * τ.im)) * (C * (scale τ) ^ N) :=
        mul_le_mul hj hd (norm_nonneg _) (by positivity)
    _ = (27 / 4) * C * (scale τ) ^ N * Real.exp (2 * Real.pi * τ.im) := by ring

/-- `‖j(τ)² (ψ₄(τ)E₈(τ) - ψ₂(τ)E₁₀(τ))‖ ≤ C (scale τ)^N e^{2π Im τ}` on the funnel. -/
theorem j2_psi_sub_funnel (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖jInvariantFun τ ^ 2 * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
        ≤ C * (scale τ) ^ N * Real.exp (2 * Real.pi * τ.im) := by
  obtain ⟨C, N, hC, hN, h⟩ := psi_sub_funnel ℓ
  refine ⟨(27 / 4) ^ 2 * C, N, by nlinarith [hC], hN, fun τ hτ => ?_⟩
  have hj := norm_j_funnel τ hτ
  have hd := h τ hτ
  have hjn : ‖jInvariantFun τ ^ 2‖ ≤ ((27 / 4) * Real.exp (2 * Real.pi * τ.im)) ^ 2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hj 2
  have hexp : ((27 / 4) * Real.exp (2 * Real.pi * τ.im)) ^ 2
      * (C * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)))
      = (27 / 4) ^ 2 * C * (scale τ) ^ N * Real.exp (2 * Real.pi * τ.im) := by
    rw [show ((27 / 4) * Real.exp (2 * Real.pi * τ.im)) ^ 2
        * (C * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)))
        = ((27 / 4) ^ 2 * C * (scale τ) ^ N)
          * (Real.exp (2 * Real.pi * τ.im) * Real.exp (2 * Real.pi * τ.im)
              * Real.exp (-(2 * Real.pi * τ.im))) by ring]
    rw [exp_mul_exp_mul_exp_neg]
  rw [norm_mul]
  calc ‖jInvariantFun τ ^ 2‖ * ‖psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ‖
      ≤ ((27 / 4) * Real.exp (2 * Real.pi * τ.im)) ^ 2
          * (C * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))) :=
        mul_le_mul hjn hd (norm_nonneg _) (by positivity)
    _ = (27 / 4) ^ 2 * C * (scale τ) ^ N * Real.exp (2 * Real.pi * τ.im) := hexp

/-! ## The `z`-atoms on the contour -/

/-- `‖E₄ z‖ ≤ 3/2` for `2 ≤ Im z`. -/
theorem norm_E4_le {z : ℍ} (hz : 2 ≤ z.im) : ‖E4Fun z‖ ≤ 3 / 2 := by
  have h := Work.FunnelNumerics.E4_sub_one_le z hz
  have h2 : ‖E4Fun z‖ ≤ ‖E4Fun z - 1‖ + 1 := by
    have h3 := norm_add_le (E4Fun z - 1) (1 : ℂ)
    rw [show E4Fun z - 1 + 1 = E4Fun z by ring, norm_one] at h3
    exact h3
  linarith

/-- `‖E₆ z‖` is bounded for `1 ≤ Im z`. -/
theorem norm_E6_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖E6Fun z‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := E6Fun_two_term
  refine ⟨1 + 504 + C, by positivity, fun z hz => ?_⟩
  have h1 := h z hz
  have hq : ‖qParamFun z‖ ≤ 1 := norm_qParam_le_one hz
  have hq0 : (0:ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq2 : ‖qParamFun z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hq
  have hsplit : E6Fun z = (E6Fun z - 1 + 504 * qParamFun z) + 1 - 504 * qParamFun z := by ring
  rw [hsplit]
  calc ‖(E6Fun z - 1 + 504 * qParamFun z) + 1 - 504 * qParamFun z‖
      ≤ ‖(E6Fun z - 1 + 504 * qParamFun z) + 1‖ + ‖(504 : ℂ) * qParamFun z‖ := norm_sub_le _ _
    _ ≤ (‖E6Fun z - 1 + 504 * qParamFun z‖ + 1) + 504 * ‖qParamFun z‖ := by
        have h3 := norm_add_le (E6Fun z - 1 + 504 * qParamFun z) (1:ℂ)
        rw [norm_one] at h3
        have h4 : ‖(504 : ℂ) * qParamFun z‖ = 504 * ‖qParamFun z‖ := by
          rw [norm_mul]; norm_num
        rw [h4]; linarith
    _ ≤ (C * ‖qParamFun z‖ ^ 2 + 1) + 504 * ‖qParamFun z‖ := by linarith
    _ ≤ 1 + 504 + C := by
        have hC0 : 0 ≤ C := hC.le
        have h1 : C * ‖qParamFun z‖ ^ 2 ≤ C := by
          simpa using mul_le_of_le_one_right hC0 hq2
        nlinarith [hq, h1]

/-- `‖E₁₀ z‖` is bounded for `2 ≤ Im z`. -/
theorem norm_E10_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 2 ≤ z.im → ‖E10Fun z‖ ≤ C := by
  obtain ⟨C6, hC6, h6⟩ := norm_E6_le
  exact ⟨(3/2) * C6, by positivity, fun z hz => by
    rw [show E10Fun z = E4Fun z * E6Fun z from rfl, norm_mul]
    exact mul_le_mul (norm_E4_le hz) (h6 z (by linarith)) (norm_nonneg _) (by norm_num)⟩

/-- `‖E₁₄ z‖` is bounded for `2 ≤ Im z`. -/
theorem norm_E14_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 2 ≤ z.im → ‖E14Fun z‖ ≤ C := by
  obtain ⟨C6, hC6, h6⟩ := norm_E6_le
  refine ⟨(9/4) * C6, by positivity, fun z hz => ?_⟩
  have h4 : ‖E4Fun z ^ 2‖ ≤ (3/2)^2 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_E4_le hz) 2
  rw [show E14Fun z = E4Fun z ^ 2 * E6Fun z from rfl, norm_mul]
  calc ‖E4Fun z ^ 2‖ * ‖E6Fun z‖ ≤ ((3/2)^2) * C6 :=
        mul_le_mul h4 (h6 z (by linarith)) (norm_nonneg _) (by norm_num)
    _ = (9/4) * C6 := by norm_num

/-- `‖Wref z‖ ≤ 33` for `1 ≤ Im z`. -/
theorem norm_Wref_le {z : ℍ} (hz : 1 ≤ z.im) : ‖Wref z‖ ≤ 33 := by
  have he := norm_Ept_le_one' hz
  have he2 : ‖(Ept z) ^ 2‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) he
  rw [Wref]
  calc ‖1 - 8 * Ept z + 24 * (Ept z) ^ 2‖
      ≤ ‖1 - 8 * Ept z‖ + ‖(24 : ℂ) * (Ept z) ^ 2‖ := norm_add_le _ _
    _ ≤ (1 + 8) + 24 := by
        refine add_le_add ?_ ?_
        · have h := norm_sub_le (1:ℂ) (8 * Ept z)
          rw [norm_one] at h
          have h8 : ‖(8 : ℂ) * Ept z‖ ≤ 8 := by
            rw [norm_mul, show ‖(8:ℂ)‖ = 8 by norm_num]; linarith
          linarith
        · rw [norm_mul, show ‖(24:ℂ)‖ = 24 by norm_num]; linarith
    _ = 33 := by norm_num

/-- `‖D2ref z‖ ≤ 161` for `1 ≤ Im z`. -/
theorem norm_D2ref_le {z : ℍ} (hz : 1 ≤ z.im) : ‖D2ref z‖ ≤ 161 := by
  have he := norm_Ept_le_one' hz
  have he2 : ‖(Ept z) ^ 2‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) he
  rw [D2ref]
  calc ‖1 + 16 * Ept z - 144 * (Ept z) ^ 2‖
      ≤ ‖1 + 16 * Ept z‖ + ‖(144 : ℂ) * (Ept z) ^ 2‖ := norm_sub_le _ _
    _ ≤ (1 + 16) + 144 := by
        refine add_le_add ?_ ?_
        · have h := norm_add_le (1:ℂ) (16 * Ept z)
          rw [norm_one] at h
          have h8 : ‖(16 : ℂ) * Ept z‖ ≤ 16 := by
            rw [norm_mul, show ‖(16:ℂ)‖ = 16 by norm_num]; linarith
          linarith
        · rw [norm_mul, show ‖(144:ℂ)‖ = 144 by norm_num]; linarith
    _ = 161 := by norm_num

/-- `dW z = O(‖Ept z‖³)` for `1 ≤ Im z`. -/
theorem norm_dW_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖dW z‖ ≤ C * ‖Ept z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.cusp_W_second
  exact ⟨C, hC, fun z hz => by simpa [dW, Wref] using h z hz⟩

/-- `dD2 z = O(‖Ept z‖³)` for `1 ≤ Im z`. -/
theorem norm_dD2_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖dD2 z‖ ≤ C * ‖Ept z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.cusp_D_second
  exact ⟨C, hC, fun z hz => by simpa [dD2, D2ref] using h z hz⟩

/-- `dDelta z = O(‖Ept z‖²)` for `1 ≤ Im z`. -/
theorem norm_dDelta_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖dDelta z‖ ≤ C * ‖Ept z‖ ^ 2 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.cusp_invDelta
  exact ⟨C, hC, fun z hz => by simpa [dDelta, Dref, einv2] using h z hz⟩

/-- `dL z = O(‖Ept z‖³)` for `1 ≤ Im z`. -/
theorem norm_dL_le (ℓ : LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖dL ℓ z‖ ≤ C * ‖Ept z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Compact.cuspC_spec ℓ
  exact ⟨C, hC, fun z hz => by simpa [dL, Lref, Xc] using h z hz⟩

/-- `‖(Δ z)⁻¹‖ ≤ ‖Ept z‖^{-2} + K` for `1 ≤ Im z`, with a constant `K`. -/
theorem norm_invDelta_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℍ, 1 ≤ z.im → ‖(DeltaFun z)⁻¹‖ ≤ (‖Ept z‖ ^ 2)⁻¹ + K := by
  obtain ⟨C, hC, h⟩ := norm_dDelta_le
  refine ⟨24 + C, by positivity, fun z hz => ?_⟩
  have h1 := h z hz
  have he := norm_Ept_le_one' hz
  have he2 : ‖Ept z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) he
  have hD : (DeltaFun z)⁻¹ = Dref z + dDelta z := by rw [dDelta]; ring
  have hDr : ‖Dref z‖ ≤ (‖Ept z‖ ^ 2)⁻¹ + 24 := by
    rw [Dref, einv2]
    calc ‖(Ept z)⁻¹ ^ 2 + 24‖ ≤ ‖(Ept z)⁻¹ ^ 2‖ + ‖(24 : ℂ)‖ := norm_add_le _ _
      _ = (‖Ept z‖ ^ 2)⁻¹ + 24 := by
          rw [norm_pow, norm_inv, inv_pow, show ‖(24:ℂ)‖ = 24 by norm_num]
  have hd : ‖dDelta z‖ ≤ C := by
    have hX : C * ‖Ept z‖ ^ 2 ≤ C := by
      simpa using mul_le_of_le_one_right hC.le he2
    linarith
  rw [hD]
  calc ‖Dref z + dDelta z‖ ≤ ‖Dref z‖ + ‖dDelta z‖ := norm_add_le _ _
    _ ≤ ((‖Ept z‖ ^ 2)⁻¹ + 24) + C := by linarith
    _ = (‖Ept z‖ ^ 2)⁻¹ + (24 + C) := by ring

/-- `‖Dref z‖ ≤ ‖Ept z‖^{-2} + 24`. -/
theorem norm_Dref_le {z : ℍ} (hz : 1 ≤ z.im) :
    ‖Dref z‖ ≤ (‖Ept z‖ ^ 2)⁻¹ + 24 := by
  have he := norm_Ept_le_one' hz
  have he2 : ‖Ept z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) he
  have hinv1 : (1:ℝ) ≤ (‖Ept z‖ ^ 2)⁻¹ := by
    rw [one_le_inv₀ (pow_pos (norm_pos_iff.mpr (Work.Residues.Ept_ne_zero z)) 2)]; exact he2
  rw [Dref, einv2]
  calc ‖(Ept z)⁻¹ ^ 2 + 24‖ ≤ ‖(Ept z)⁻¹ ^ 2‖ + ‖(24 : ℂ)‖ := norm_add_le _ _
    _ = (‖Ept z‖ ^ 2)⁻¹ + 24 := by
        rw [norm_pow, norm_inv, inv_pow, show ‖(24:ℂ)‖ = 24 by norm_num]

/-- `‖Lref ℓ z‖ ≤ C(1 + ‖z‖)` for `1 ≤ Im z`. -/
theorem norm_Lref_le (ℓ : LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖Lref ℓ z‖ ≤ C * (1 + ‖(z : ℂ)‖) := by
  refine ⟨Real.pi + ‖Compact.cuspC ℓ‖ + 21, by positivity, fun z hz => ?_⟩
  have hX : ‖Xc ℓ z‖ ≤ Real.pi * ‖(z : ℂ)‖ + ‖Compact.cuspC ℓ‖ := by
    rw [Xc]
    calc ‖(Real.pi : ℂ) * Complex.I * (z : ℂ) + Compact.cuspC ℓ‖
        ≤ ‖(Real.pi : ℂ) * Complex.I * (z : ℂ)‖ + ‖Compact.cuspC ℓ‖ := norm_add_le _ _
      _ = Real.pi * ‖(z : ℂ)‖ + ‖Compact.cuspC ℓ‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
  have he := norm_Ept_le_one' hz
  have h8 : ‖(8 : ℂ) * Ept z‖ ≤ 8 := by
    rw [norm_mul, show ‖(8:ℂ)‖ = 8 by norm_num]; linarith
  have h12 : ‖(12 : ℂ) * (Ept z) ^ 2‖ ≤ 12 := by
    have he2 : ‖(Ept z) ^ 2‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) he
    rw [norm_mul, show ‖(12:ℂ)‖ = 12 by norm_num]; linarith
  rw [Lref]
  calc ‖Xc ℓ z - 8 * Ept z + 12 * (Ept z) ^ 2‖
      ≤ ‖Xc ℓ z - 8 * Ept z‖ + ‖(12 : ℂ) * (Ept z) ^ 2‖ := norm_add_le _ _
    _ ≤ (‖Xc ℓ z‖ + 8) + 12 := by
        refine add_le_add ?_ h12
        have h := norm_sub_le (Xc ℓ z) (8 * Ept z)
        linarith [h8]
    _ ≤ (Real.pi + ‖Compact.cuspC ℓ‖ + 21) * (1 + ‖(z : ℂ)‖) := by
        have h1 : (0:ℝ) ≤ ‖(z : ℂ)‖ := norm_nonneg _
        nlinarith [hX, Real.pi_pos, norm_nonneg (Compact.cuspC ℓ)]

/-- `‖𝓛(z)‖ ≤ C(1 + ‖z‖)` for `1 ≤ Im z`. -/
theorem norm_L_le (ℓ : LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖ℓ.L z‖ ≤ C * (1 + ‖(z : ℂ)‖) := by
  obtain ⟨C1, hC1, h1⟩ := norm_dL_le ℓ
  obtain ⟨C2, hC2, h2⟩ := norm_Lref_le ℓ
  refine ⟨C1 + C2, by positivity, fun z hz => ?_⟩
  have he := norm_Ept_le_one' hz
  have he3 : ‖Ept z‖ ^ 3 ≤ 1 := pow_le_one₀ (norm_nonneg _) he
  have hsplit : ℓ.L z = dL ℓ z + Lref ℓ z := by rw [dL]; ring
  have hone : (1:ℝ) ≤ 1 + ‖(z:ℂ)‖ := by linarith [norm_nonneg (z:ℂ)]
  rw [hsplit]
  calc ‖dL ℓ z + Lref ℓ z‖ ≤ ‖dL ℓ z‖ + ‖Lref ℓ z‖ := norm_add_le _ _
    _ ≤ C1 * ‖Ept z‖ ^ 3 + C2 * (1 + ‖(z : ℂ)‖) := add_le_add (h1 z hz) (h2 z hz)
    _ ≤ C1 * (1 + ‖(z : ℂ)‖) + C2 * (1 + ‖(z : ℂ)‖) := by
        have := mul_le_mul_of_nonneg_left (le_trans he3 hone) hC1.le
        linarith
    _ = (C1 + C2) * (1 + ‖(z : ℂ)‖) := by ring

/-- `‖WFun z‖ ≤ C` for `1 ≤ Im z`. -/
theorem norm_W_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖WFun z‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := norm_dW_le
  refine ⟨33 + C, by positivity, fun z hz => ?_⟩
  have he := norm_Ept_le_one' hz
  have he3 : ‖Ept z‖ ^ 3 ≤ 1 := pow_le_one₀ (norm_nonneg _) he
  have hsplit : WFun z = Wref z + dW z := by rw [dW]; ring
  have hd : ‖dW z‖ ≤ C := by
    have := mul_le_of_le_one_right hC.le he3
    linarith [h z hz]
  rw [hsplit]
  calc ‖Wref z + dW z‖ ≤ ‖Wref z‖ + ‖dW z‖ := norm_add_le _ _
    _ ≤ 33 + C := by linarith [norm_Wref_le hz]

/-- `‖U z² - V z²‖ ≤ C` for `1 ≤ Im z`. -/
theorem norm_D2_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖UFun z ^ 2 - VFun z ^ 2‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := norm_dD2_le
  refine ⟨161 + C, by positivity, fun z hz => ?_⟩
  have he := norm_Ept_le_one' hz
  have he3 : ‖Ept z‖ ^ 3 ≤ 1 := pow_le_one₀ (norm_nonneg _) he
  have hsplit : UFun z ^ 2 - VFun z ^ 2 = D2ref z + dD2 z := by rw [dD2]; ring
  have hd : ‖dD2 z‖ ≤ C := by
    have := mul_le_of_le_one_right hC.le he3
    linarith [h z hz]
  rw [hsplit]
  calc ‖D2ref z + dD2 z‖ ≤ ‖D2ref z‖ + ‖dD2 z‖ := norm_add_le _ _
    _ ≤ 161 + C := by linarith [norm_D2ref_le hz]

/-! ## Product bookkeeping -/

theorem norm_mono_le {x y : ℂ} {A B : ℝ} (hx : ‖x‖ ≤ A) (hy : ‖y‖ ≤ B) :
    ‖x * y‖ ≤ A * B := by
  rw [norm_mul]
  exact mul_le_mul hx hy (norm_nonneg _) (le_trans (norm_nonneg x) hx)

theorem norm_three_le {x y z : ℂ} {A B C : ℝ} (hx : ‖x‖ ≤ A) (hy : ‖y‖ ≤ B) (hz : ‖z‖ ≤ C) :
    ‖x * y * z‖ ≤ A * B * C := by
  rw [norm_mul, norm_mul]
  have hAB : ‖x‖ * ‖y‖ ≤ A * B := mul_le_mul hx hy (norm_nonneg _) (le_trans (norm_nonneg x) hx)
  exact mul_le_mul hAB hz (norm_nonneg _) (mul_nonneg (le_trans (norm_nonneg x) hx)
    (le_trans (norm_nonneg y) hy))

/-- `e^{2π Im τ} · ‖Ept z‖² ≤ e^{-2π}` on the funnel for `t ≥ Im τ + 1`. -/
theorem exp_im_mul_Ept_sq_le (τ z : ℍ) (t : ℝ) (hτ : Funnel τ) (ht : τ.im + 1 ≤ t)
    (hz : z.im = t) :
    Real.exp (2 * Real.pi * τ.im) * ‖Ept z‖ ^ 2 ≤ Real.exp (-(2 * Real.pi)) := by
  have he : ‖Ept z‖ ^ 2 = Real.exp (-(2 * Real.pi * t)) := by
    rw [Work.Residues.norm_Ept, hz, sq, ← Real.exp_add]
    congr 1
    ring
  rw [he, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith [ht, Real.pi_pos])

/-! ## Sum bounds -/

theorem norm_seven_le {a b c d e f g : ℂ} {A B C D E F G : ℝ}
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) (he : ‖e‖ ≤ E)
    (hf : ‖f‖ ≤ F) (hg : ‖g‖ ≤ G) :
    ‖a + b + c + d + e + f + g‖ ≤ A + B + C + D + E + F + G := by
  have h1 : ‖a + b + c + d + e + f + g‖ ≤ ‖a + b + c + d + e + f‖ + ‖g‖ := norm_add_le _ _
  have h2 : ‖a + b + c + d + e + f‖ ≤ ‖a + b + c + d + e‖ + ‖f‖ := norm_add_le _ _
  have h3 : ‖a + b + c + d + e‖ ≤ ‖a + b + c + d‖ + ‖e‖ := norm_add_le _ _
  have h4 : ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
  have h5 : ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
  have h6 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
  linarith

theorem norm_six_le' {a b c d e f : ℂ} {A B C D E F : ℝ}
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) (he : ‖e‖ ≤ E)
    (hf : ‖f‖ ≤ F) : ‖a + b + c + d + e + f‖ ≤ A + B + C + D + E + F := by
  have h1 : ‖a + b + c + d + e + f‖ ≤ ‖a + b + c + d + e‖ + ‖f‖ := norm_add_le _ _
  have h2 : ‖a + b + c + d + e‖ ≤ ‖a + b + c + d‖ + ‖e‖ := norm_add_le _ _
  have h3 : ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
  have h4 : ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
  have h5 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
  linarith

/-- `c · ‖q‖^k ≤ c · ‖q‖^2` for `c ≥ 0`, `k ≥ 2`, `‖q‖ ≤ 1`. -/
theorem pow_two_le_of_le {q : ℂ} {c : ℝ} (hq0 : 0 ≤ ‖q‖) (hq1 : ‖q‖ ≤ 1) (hc : 0 ≤ c)
    {k : ℕ} (hk : 2 ≤ k) : c * ‖q‖ ^ k ≤ c * ‖q‖ ^ 2 :=
  mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1 hk) hc

/-! ## The deviations `dE14`, `dE10` -/

/-- `E₁₄ z = 1 - 24 Ept z² + O(‖Ept z‖⁴)` (i.e. `dE14 = O(‖Ept z‖⁴)`), for `1 ≤ Im z`. -/
theorem norm_dE14_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖dE14 z‖ ≤ C * ‖Ept z‖ ^ 4 := by
  obtain ⟨C4, hC4, h4⟩ := E4Fun_two_term
  obtain ⟨C6, hC6, h6⟩ := E6Fun_two_term
  refine ⟨C6 + 2 * C4 + 1008 * C4 + 2 * C4 * C6 + 480 * C6
    + (240 + C4) ^ 2 * (1 + 504 + C6) + 241920, by positivity, fun z hz => ?_⟩
  set q : ℂ := qParamFun z with hqdef
  set a : ℂ := E4Fun z - 1 - 240 * q with hadef
  set b : ℂ := E6Fun z - 1 + 504 * q with hbdef
  have hqn : ‖q‖ = ‖Ept z‖ ^ 2 := by rw [hqdef, qParam_eq]; simp [norm_pow]
  have hq1 : ‖q‖ ≤ 1 := by rw [hqn]; exact pow_le_one₀ (norm_nonneg _) (norm_Ept_le_one' hz)
  have hq0 : (0:ℝ) ≤ ‖q‖ := norm_nonneg _
  have hq2 : ‖q‖ ^ 2 ≤ ‖q‖ := by
    simpa using pow_le_pow_of_le_one hq0 hq1 (show (1:ℕ) ≤ 2 by norm_num)
  have hq3 : ‖q‖ ^ 3 ≤ ‖q‖ ^ 2 := pow_le_pow_of_le_one hq0 hq1 (by norm_num)
  have hq4 : ‖q‖ ^ 4 ≤ ‖q‖ ^ 2 := pow_le_pow_of_le_one hq0 hq1 (by norm_num)
  have ha : ‖a‖ ≤ C4 * ‖q‖ ^ 2 := by rw [hadef, hqdef]; exact h4 z hz
  have hb : ‖b‖ ≤ C6 * ‖q‖ ^ 2 := by rw [hbdef, hqdef]; exact h6 z hz
  have haq : ‖a‖ ≤ C4 * ‖q‖ := le_trans ha (mul_le_mul_of_nonneg_left hq2 hC4.le)
  have hT1 : ‖b‖ ≤ C6 * ‖q‖ ^ 2 := hb
  have hT2 : ‖2 * a‖ ≤ 2 * C4 * ‖q‖ ^ 2 := by
    rw [norm_mul, show ‖(2:ℂ)‖ = 2 by norm_num]; linarith [ha]
  have hT3 : ‖-1008 * q * a‖ ≤ 1008 * C4 * ‖q‖ ^ 2 := by
    rw [show -1008 * q * a = (-1008 : ℂ) * (q * a) by ring, norm_mul,
      show ‖(-1008 : ℂ)‖ = 1008 by norm_num, norm_mul]
    calc 1008 * (‖q‖ * ‖a‖) ≤ 1008 * (C4 * ‖q‖ ^ 3) := by
          have h : ‖q‖ * ‖a‖ ≤ ‖q‖ * (C4 * ‖q‖ ^ 2) := mul_le_mul_of_nonneg_left ha hq0
          have h3 : ‖q‖ * (C4 * ‖q‖ ^ 2) = C4 * ‖q‖ ^ 3 := by ring
          nlinarith [h, h3, hC4.le]
      _ = (1008 * C4) * ‖q‖ ^ 3 := by ring
      _ ≤ (1008 * C4) * ‖q‖ ^ 2 := pow_two_le_of_le hq0 hq1 (by positivity) (by norm_num)
  have hT4 : ‖2 * a * b‖ ≤ 2 * C4 * C6 * ‖q‖ ^ 2 := by
    rw [show 2 * a * b = (2:ℂ) * (a * b) by ring, norm_mul, show ‖(2:ℂ)‖ = 2 by norm_num,
      norm_mul]
    calc 2 * (‖a‖ * ‖b‖) ≤ 2 * ((C4 * ‖q‖ ^ 2) * (C6 * ‖q‖ ^ 2)) := by
          have h : ‖a‖ * ‖b‖ ≤ (C4 * ‖q‖ ^ 2) * (C6 * ‖q‖ ^ 2) :=
            mul_le_mul ha hb (norm_nonneg _) (by positivity)
          linarith
      _ = (2 * C4 * C6) * ‖q‖ ^ 4 := by ring
      _ ≤ (2 * C4 * C6) * ‖q‖ ^ 2 := pow_two_le_of_le hq0 hq1 (by positivity) (by norm_num)
  have hT5 : ‖480 * q * b‖ ≤ 480 * C6 * ‖q‖ ^ 2 := by
    rw [show 480 * q * b = (480 : ℂ) * (q * b) by ring, norm_mul,
      show ‖(480 : ℂ)‖ = 480 by norm_num, norm_mul]
    calc 480 * (‖q‖ * ‖b‖) ≤ 480 * (C6 * ‖q‖ ^ 3) := by
          have h : ‖q‖ * ‖b‖ ≤ ‖q‖ * (C6 * ‖q‖ ^ 2) := mul_le_mul_of_nonneg_left hb hq0
          have h3 : ‖q‖ * (C6 * ‖q‖ ^ 2) = C6 * ‖q‖ ^ 3 := by ring
          nlinarith [h, h3, hC6.le]
      _ = (480 * C6) * ‖q‖ ^ 3 := by ring
      _ ≤ (480 * C6) * ‖q‖ ^ 2 := pow_two_le_of_le hq0 hq1 (by positivity) (by norm_num)
  have hT6 : ‖(240 * q + a) ^ 2 * (1 - 504 * q + b)‖
      ≤ (240 + C4) ^ 2 * (1 + 504 + C6) * ‖q‖ ^ 2 := by
    have h1 : ‖(240:ℂ) * q + a‖ ≤ (240 + C4) * ‖q‖ := by
      calc ‖(240:ℂ) * q + a‖ ≤ ‖(240:ℂ) * q‖ + ‖a‖ := norm_add_le _ _
        _ = 240 * ‖q‖ + ‖a‖ := by rw [norm_mul, show ‖(240:ℂ)‖ = 240 by norm_num]
        _ ≤ 240 * ‖q‖ + C4 * ‖q‖ := by linarith [haq]
        _ = (240 + C4) * ‖q‖ := by ring
    have h1n : ‖(240:ℂ) * q + a‖ ^ 2 ≤ ((240 + C4) * ‖q‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h2 : ‖(1:ℂ) - 504 * q + b‖ ≤ 1 + 504 + C6 := by
      have h3 : ‖(504 : ℂ) * q‖ ≤ 504 := by
        rw [norm_mul, show ‖(504:ℂ)‖ = 504 by norm_num]; linarith [hq1]
      have h4 : ‖(1:ℂ) - 504 * q‖ ≤ 1 + 504 := by
        have hh := norm_sub_le (1:ℂ) ((504:ℂ) * q)
        rw [norm_one] at hh
        linarith
      have h5 : ‖b‖ ≤ C6 := le_trans hb (by
        have h1 := mul_le_mul_of_nonneg_left hq2 hC6.le
        have h2 := mul_le_mul_of_nonneg_left hq1 hC6.le
        linarith)
      have hh := norm_add_le ((1:ℂ) - (504:ℂ) * q) b
      linarith
    rw [norm_mul, norm_pow]
    calc ‖(240:ℂ) * q + a‖ ^ 2 * ‖(1:ℂ) - 504 * q + b‖
        ≤ ((240 + C4) * ‖q‖) ^ 2 * (1 + 504 + C6) :=
          mul_le_mul h1n h2 (norm_nonneg _) (by positivity)
      _ = (240 + C4) ^ 2 * (1 + 504 + C6) * ‖q‖ ^ 2 := by ring
  have hT7 : ‖-241920 * q ^ 2‖ ≤ 241920 * ‖q‖ ^ 2 := by
    rw [show -241920 * q ^ 2 = (-241920 : ℂ) * q ^ 2 by ring, norm_mul, norm_pow,
      show ‖(-241920 : ℂ)‖ = 241920 by norm_num]
  have hgoal : dE14 z = b + 2 * a + -1008 * q * a + 2 * a * b + 480 * q * b
      + (240 * q + a) ^ 2 * (1 - 504 * q + b) + -241920 * q ^ 2 := by
    simp only [dE14, E14ref, hadef, hbdef, hqdef, qParam_eq]
    ring
  rw [hgoal]
  refine le_trans (norm_seven_le hT1 hT2 hT3 hT4 hT5 hT6 hT7) ?_
  rw [show ‖Ept z‖ ^ 4 = ‖q‖ ^ 2 by rw [hqn]; ring]
  have hC40 : 0 ≤ C4 := hC4.le
  have hC60 : 0 ≤ C6 := hC6.le
  nlinarith [hq0, pow_nonneg hq0 2, hq3, hq4,
    mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 1008) hC40) (pow_nonneg hq0 2),
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hC40) hC60) (pow_nonneg hq0 2),
    mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 480) hC60) (pow_nonneg hq0 2)]

/-- `E₁₀ z = 1 - 264 Ept z² + O(‖Ept z‖⁴)` (i.e. `dE10 = O(‖Ept z‖⁴)`), for `1 ≤ Im z`. -/
theorem norm_dE10_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖dE10 z‖ ≤ C * ‖Ept z‖ ^ 4 := by
  obtain ⟨C4, hC4, h4⟩ := E4Fun_two_term
  obtain ⟨C6, hC6, h6⟩ := E6Fun_two_term
  refine ⟨120960 + C4 + 504 * C4 + C6 + 240 * C6 + C4 * C6, by positivity, fun z hz => ?_⟩
  set q : ℂ := qParamFun z with hqdef
  set a : ℂ := E4Fun z - 1 - 240 * q with hadef
  set b : ℂ := E6Fun z - 1 + 504 * q with hbdef
  have hqn : ‖q‖ = ‖Ept z‖ ^ 2 := by rw [hqdef, qParam_eq]; simp [norm_pow]
  have hq1 : ‖q‖ ≤ 1 := by rw [hqn]; exact pow_le_one₀ (norm_nonneg _) (norm_Ept_le_one' hz)
  have hq0 : (0:ℝ) ≤ ‖q‖ := norm_nonneg _
  have ha : ‖a‖ ≤ C4 * ‖q‖ ^ 2 := by rw [hadef, hqdef]; exact h4 z hz
  have hb : ‖b‖ ≤ C6 * ‖q‖ ^ 2 := by rw [hbdef, hqdef]; exact h6 z hz
  have hT1 : ‖-120960 * q ^ 2‖ ≤ 120960 * ‖q‖ ^ 2 := by
    rw [show -120960 * q ^ 2 = (-120960 : ℂ) * q ^ 2 by ring, norm_mul, norm_pow,
      show ‖(-120960 : ℂ)‖ = 120960 by norm_num]
  have hT2 : ‖a‖ ≤ C4 * ‖q‖ ^ 2 := ha
  have hT3 : ‖-504 * q * a‖ ≤ 504 * C4 * ‖q‖ ^ 2 := by
    rw [show -504 * q * a = (-504 : ℂ) * (q * a) by ring, norm_mul,
      show ‖(-504 : ℂ)‖ = 504 by norm_num, norm_mul]
    calc 504 * (‖q‖ * ‖a‖) ≤ 504 * (C4 * ‖q‖ ^ 3) := by
          have h : ‖q‖ * ‖a‖ ≤ ‖q‖ * (C4 * ‖q‖ ^ 2) := mul_le_mul_of_nonneg_left ha hq0
          have h3 : ‖q‖ * (C4 * ‖q‖ ^ 2) = C4 * ‖q‖ ^ 3 := by ring
          nlinarith [h, h3, hC4.le]
      _ = (504 * C4) * ‖q‖ ^ 3 := by ring
      _ ≤ (504 * C4) * ‖q‖ ^ 2 := pow_two_le_of_le hq0 hq1 (by positivity) (by norm_num)
  have hT4 : ‖b‖ ≤ C6 * ‖q‖ ^ 2 := hb
  have hT5 : ‖240 * q * b‖ ≤ 240 * C6 * ‖q‖ ^ 2 := by
    rw [show 240 * q * b = (240 : ℂ) * (q * b) by ring, norm_mul,
      show ‖(240 : ℂ)‖ = 240 by norm_num, norm_mul]
    calc 240 * (‖q‖ * ‖b‖) ≤ 240 * (C6 * ‖q‖ ^ 3) := by
          have h : ‖q‖ * ‖b‖ ≤ ‖q‖ * (C6 * ‖q‖ ^ 2) := mul_le_mul_of_nonneg_left hb hq0
          have h3 : ‖q‖ * (C6 * ‖q‖ ^ 2) = C6 * ‖q‖ ^ 3 := by ring
          nlinarith [h, h3, hC6.le]
      _ = (240 * C6) * ‖q‖ ^ 3 := by ring
      _ ≤ (240 * C6) * ‖q‖ ^ 2 := pow_two_le_of_le hq0 hq1 (by positivity) (by norm_num)
  have hT6 : ‖a * b‖ ≤ C4 * C6 * ‖q‖ ^ 2 := by
    rw [norm_mul]
    calc ‖a‖ * ‖b‖ ≤ (C4 * ‖q‖ ^ 2) * (C6 * ‖q‖ ^ 2) :=
          mul_le_mul ha hb (norm_nonneg _) (by positivity)
      _ = (C4 * C6) * ‖q‖ ^ 4 := by ring
      _ ≤ (C4 * C6) * ‖q‖ ^ 2 := pow_two_le_of_le hq0 hq1 (by positivity) (by norm_num)
  have hgoal : dE10 z = -120960 * q ^ 2 + a + -504 * q * a + b + 240 * q * b + a * b := by
    simp only [dE10, E10ref, hadef, hbdef, hqdef, qParam_eq]
    ring
  rw [hgoal]
  refine le_trans (norm_six_le' hT1 hT2 hT3 hT4 hT5 hT6) ?_
  rw [show ‖Ept z‖ ^ 4 = ‖q‖ ^ 2 by rw [hqn]; ring]
  have hC40 : 0 ≤ C4 := hC4.le
  have hC60 : 0 ≤ C6 := hC6.le
  nlinarith [hq0, pow_nonneg hq0 2,
    mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 504) hC40) (pow_nonneg hq0 2),
    mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 240) hC60) (pow_nonneg hq0 2),
    mul_nonneg (mul_nonneg hC40 hC60) (pow_nonneg hq0 2)]

/-! ## Combining with the `(scale τ)^N` factor -/

theorem scale_inflate {X : ℂ} {C N d : ℝ} {τ : ℍ} (h : ‖X‖ ≤ C * (scale τ) ^ N) (hC : 0 ≤ C)
    (hd : 0 ≤ d) : ‖X‖ ≤ C * (scale τ) ^ (N + d) := by
  have hs : (scale τ) ^ N ≤ (scale τ) ^ (N + d) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_scale τ) (by linarith)
  exact le_trans h (mul_le_mul_of_nonneg_left hs hC)

theorem scale_inflate' {X : ℂ} {C N d e : ℝ} {τ : ℍ}
    (h : ‖X‖ ≤ C * (scale τ) ^ N * e) (hC : 0 ≤ C) (he : 0 ≤ e) (hd : 0 ≤ d) :
    ‖X‖ ≤ C * (scale τ) ^ (N + d) * e := by
  have hs : (scale τ) ^ N ≤ (scale τ) ^ (N + d) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_scale τ) (by linarith)
  calc ‖X‖ ≤ C * (scale τ) ^ N * e := h
    _ ≤ C * (scale τ) ^ (N + d) * e := by
        refine mul_le_mul_of_nonneg_right ?_ he
        exact mul_le_mul_of_nonneg_left hs hC

/-! ## The `τ`-atoms entering the bracket -/

/-- `c · e ≤ c · (scale τ)^N · e` for `c, e ≥ 0`, `N ≥ 0`. -/
theorem mul_exp_scale_le {c e : ℝ} {τ : ℍ} {N : ℝ} (hc : 0 ≤ c) (he : 0 ≤ e)
    (hN : 0 ≤ N) : c * e ≤ c * (scale τ) ^ N * e := by
  have hs : (1:ℝ) ≤ (scale τ) ^ N := one_le_scale_rpow' τ hN
  have h : e ≤ (scale τ) ^ N * e := by
    calc e = 1 * e := by ring
      _ ≤ (scale τ) ^ N * e := mul_le_mul_of_nonneg_right hs he
  calc c * e ≤ c * ((scale τ) ^ N * e) := mul_le_mul_of_nonneg_left h hc
    _ = c * (scale τ) ^ N * e := by ring

/-- `c ≤ c (1+t)` for `c ≥ 0`, `t ≥ 0`. -/
theorem mul_one_add_le {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) : c ≤ c * (1 + t) := by
  have h : (1:ℝ) ≤ 1 + t := by linarith
  calc c = c * 1 := by ring
    _ ≤ c * (1 + t) := mul_le_mul_of_nonneg_left h hc

/-- `e^{-2π Im τ} ≤ (scale τ)^N · e^{-2π Im τ}`. -/
theorem exp_le_scale_mul {τ : ℍ} {N : ℝ} (hN : 0 ≤ N) :
    Real.exp (-(2 * Real.pi * τ.im))
      ≤ (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) := by
  have := mul_exp_scale_le (τ := τ) (c := 1) (e := Real.exp (-(2 * Real.pi * τ.im)))
    (by norm_num) (le_of_lt (Real.exp_pos _)) hN
  simpa using this

/-- `‖Sinvref τ z‖ ≤ 723` on the funnel contour. -/
theorem Sinvref_funnel :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I → ‖Sinvref τ z‖ ≤ C := by
  refine ⟨1 + 27 / 4 + 720, by norm_num, fun τ z t hτ ht hz => ?_⟩
  have hzim : z.im = t := ft_im_of_coe hz
  have hj := norm_j_funnel τ hτ
  have he1 : ‖Ept z‖ ≤ 1 := by
    rw [Work.Residues.norm_Ept, hzim]
    exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hτ.2, ht])
  have he2 : ‖(Ept z) ^ 2‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) he1
  have hprod : Real.exp (2 * Real.pi * τ.im) * ‖Ept z‖ ^ 2 ≤ Real.exp (-(2 * Real.pi)) :=
    exp_im_mul_Ept_sq_le τ z t hτ ht hzim
  have hkey : ‖jInvariantFun τ - 720‖ * ‖(Ept z) ^ 2‖ ≤ 27 / 4 + 720 := by
    have hx : ‖jInvariantFun τ - 720‖ ≤ (27 / 4) * Real.exp (2 * Real.pi * τ.im) + 720 := by
      calc ‖jInvariantFun τ - 720‖ ≤ ‖jInvariantFun τ‖ + ‖(720 : ℂ)‖ := norm_sub_le _ _
        _ ≤ (27 / 4) * Real.exp (2 * Real.pi * τ.im) + 720 := by
            rw [show ‖(720 : ℂ)‖ = 720 by norm_num]; linarith
    have hsq : ‖(Ept z) ^ 2‖ = ‖Ept z‖ ^ 2 := norm_pow _ _
    calc ‖jInvariantFun τ - 720‖ * ‖(Ept z) ^ 2‖
        ≤ ((27 / 4) * Real.exp (2 * Real.pi * τ.im) + 720) * ‖(Ept z) ^ 2‖ :=
          mul_le_mul_of_nonneg_right hx (norm_nonneg _)
      _ = (27 / 4) * (Real.exp (2 * Real.pi * τ.im) * ‖Ept z‖ ^ 2)
            + 720 * ‖(Ept z) ^ 2‖ := by rw [hsq]; ring
      _ ≤ (27 / 4) * Real.exp (-(2 * Real.pi)) + 720 * 1 := by
          have h1 : (27 / 4) * (Real.exp (2 * Real.pi * τ.im) * ‖Ept z‖ ^ 2)
              ≤ (27 / 4) * Real.exp (-(2 * Real.pi)) :=
            mul_le_mul_of_nonneg_left hprod (by norm_num)
          have h2 : 720 * ‖(Ept z) ^ 2‖ ≤ 720 * 1 := by
            have := mul_le_mul_of_nonneg_left he2 (by norm_num : (0:ℝ) ≤ 720)
            simpa using this
          linarith
      _ ≤ 27 / 4 + 720 := by
          have h3 : Real.exp (-(2 * Real.pi)) ≤ 1 := by
            rw [Real.exp_le_one_iff]; linarith [Real.pi_pos]
          nlinarith
  rw [Sinvref]
  calc ‖(1:ℂ) + (jInvariantFun τ - 720) * (Ept z) ^ 2‖
      ≤ ‖(1:ℂ)‖ + ‖(jInvariantFun τ - 720) * (Ept z) ^ 2‖ := norm_add_le _ _
    _ = 1 + ‖jInvariantFun τ - 720‖ * ‖(Ept z) ^ 2‖ := by
        rw [norm_one, norm_mul]
    _ ≤ 1 + (27 / 4 + 720) := by linarith [hkey]
    _ = 1 + 27 / 4 + 720 := by ring

/-- `‖C24 ℓ τ‖ ≤ C (scale τ)^N` on the funnel. -/
theorem C24_funnel (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ → ‖C24 ℓ τ‖ ≤ C * (scale τ) ^ N := by
  obtain ⟨Cp, Np, hCp, hNp, hp⟩ := psi4E8_funnel ℓ
  obtain ⟨Cj, Nj, hCj, hNj, hj⟩ := j_psi_sub_funnel ℓ
  refine ⟨1728 * Cp + Cj + 1, Np + Nj, by positivity, by positivity, fun τ hτ => ?_⟩
  have hs1 : (1:ℝ) ≤ (scale τ) ^ (Np + Nj) := one_le_scale_rpow' τ (by linarith)
  have h1 : ‖(1728 : ℂ) * (psi4 ℓ τ * E8Fun τ)‖
      ≤ 1728 * Cp * (scale τ) ^ (Np + Nj) := by
    rw [norm_mul, show ‖(1728 : ℂ)‖ = 1728 by norm_num,
      show (1728 : ℝ) * ‖psi4 ℓ τ * E8Fun τ‖
        = 1728 * ‖psi4 ℓ τ * E8Fun τ‖ by norm_num]
    have h := scale_inflate (τ := τ) (hp τ hτ) hCp.le hNj
    calc 1728 * ‖psi4 ℓ τ * E8Fun τ‖ ≤ 1728 * (Cp * (scale τ) ^ (Np + Nj)) :=
          mul_le_mul_of_nonneg_left h (by norm_num)
      _ = 1728 * Cp * (scale τ) ^ (Np + Nj) := by ring
  have h2 : ‖-(jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))‖
      ≤ Cj * (scale τ) ^ (Np + Nj) := by
    rw [norm_neg]
    have h := scale_inflate (τ := τ) (hj τ hτ) hCj.le hNp
    calc ‖jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
        ≤ Cj * (scale τ) ^ (Nj + Np) := h
      _ = Cj * (scale τ) ^ (Np + Nj) := by ring_nf
  have hreg : C24 ℓ τ = (1728 : ℂ) * (psi4 ℓ τ * E8Fun τ)
      + -(jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)) := by
    simp only [C24]; ring
  rw [hreg]
  calc ‖(1728 : ℂ) * (psi4 ℓ τ * E8Fun τ)
        + -(jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))‖
      ≤ ‖(1728 : ℂ) * (psi4 ℓ τ * E8Fun τ)‖
        + ‖-(jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))‖ := norm_add_le _ _
    _ ≤ 1728 * Cp * (scale τ) ^ (Np + Nj) + Cj * (scale τ) ^ (Np + Nj) := add_le_add h1 h2
    _ = (1728 * Cp + Cj) * (scale τ) ^ (Np + Nj) := by ring
    _ ≤ (1728 * Cp + Cj + 1) * (scale τ) ^ (Np + Nj) := by
        have hs : (0:ℝ) ≤ (scale τ) ^ (Np + Nj) := scale_rpow_nonneg' τ _
        nlinarith [hs]

/-- `‖B24 ℓ τ‖ ≤ C (scale τ)^N e^{-2π Im τ}` on the funnel. -/
theorem B24_funnel (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖B24 ℓ τ‖ ≤ C * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) := by
  obtain ⟨Cd, Nd, hCd, hNd, hd⟩ := psi_sub_funnel ℓ
  refine ⟨6912 + 2 * Cd, Nd, by positivity, hNd, fun τ hτ => ?_⟩
  have hE : (0:ℝ) < Real.exp (-(2 * Real.pi * τ.im)) := Real.exp_pos _
  have hD := norm_Delta_funnel τ hτ
  have hs1 : (1:ℝ) ≤ (scale τ) ^ Nd := one_le_scale_rpow' τ hNd
  have hΔ : ‖(-3456 : ℂ) * DeltaFun τ‖
      ≤ 6912 * (scale τ) ^ Nd * Real.exp (-(2 * Real.pi * τ.im)) := by
    calc ‖(-3456 : ℂ) * DeltaFun τ‖ = 3456 * ‖DeltaFun τ‖ := by
          rw [norm_mul, show ‖(-3456 : ℂ)‖ = 3456 by norm_num]
      _ ≤ 3456 * (2 * Real.exp (-(2 * Real.pi * τ.im))) :=
          mul_le_mul_of_nonneg_left hD (by norm_num)
      _ = 6912 * Real.exp (-(2 * Real.pi * τ.im)) := by ring
      _ ≤ 6912 * (scale τ) ^ Nd * Real.exp (-(2 * Real.pi * τ.im)) :=
          mul_exp_scale_le (by norm_num) (le_of_lt hE) hNd
  have hP : ‖(2 : ℂ) * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
      ≤ 2 * Cd * (scale τ) ^ Nd * Real.exp (-(2 * Real.pi * τ.im)) := by
    calc ‖(2 : ℂ) * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
        = 2 * ‖psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ‖ := by
          rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
      _ ≤ 2 * (Cd * (scale τ) ^ Nd * Real.exp (-(2 * Real.pi * τ.im))) :=
          mul_le_mul_of_nonneg_left (hd τ hτ) (by norm_num)
      _ = 2 * Cd * (scale τ) ^ Nd * Real.exp (-(2 * Real.pi * τ.im)) := by ring_nf
  have hPneg : ‖(-2 : ℂ) * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
      ≤ 2 * Cd * (scale τ) ^ Nd * Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [show (-2 : ℂ) * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)
      = -((2 : ℂ) * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)) by ring, norm_neg]
    exact hP
  have hreg : B24 ℓ τ = (-3456 : ℂ) * DeltaFun τ
      - (2 : ℂ) * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ) := by
    simp only [B24]; ring
  rw [hreg]
  calc ‖(-3456 : ℂ) * DeltaFun τ
        - (2 : ℂ) * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
      ≤ ‖(-3456 : ℂ) * DeltaFun τ‖
        + ‖(2 : ℂ) * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖ := norm_sub_le _ _
    _ ≤ 6912 * (scale τ) ^ Nd * Real.exp (-(2 * Real.pi * τ.im))
        + 2 * Cd * (scale τ) ^ Nd * Real.exp (-(2 * Real.pi * τ.im)) := add_le_add hΔ hP
    _ = (6912 + 2 * Cd) * (scale τ) ^ Nd * Real.exp (-(2 * Real.pi * τ.im)) := by ring

/-- `‖A24 ℓ τ z‖ ≤ C (scale τ)^N e^{-2π Im τ}(1+t)` on the funnel contour. -/
theorem A24_funnel (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖A24 ℓ τ z‖ ≤ C * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) := by
  obtain ⟨Cd, Nd, hCd, hNd, hdpsi⟩ := psi_sub_funnel ℓ
  obtain ⟨C14, hC14, h14⟩ := norm_E14_le
  obtain ⟨CL, hCL, hL⟩ := norm_L_le ℓ
  obtain ⟨C10, hC10, h10⟩ := norm_E10_le
  obtain ⟨CD2, hCD2, hD2b⟩ := norm_D2_le
  refine ⟨6912 * C14 * CL + Cd * C10 * CD2 + 1, Nd + 1, by positivity, by positivity,
    fun τ z t hτ ht hz => ?_⟩
  set N : ℝ := Nd + 1 with hN
  have hN0 : (0:ℝ) ≤ N := by rw [hN]; linarith
  have hsN0 : (0:ℝ) ≤ (scale τ) ^ N := scale_rpow_nonneg' τ N
  have he0 : (0:ℝ) ≤ Real.exp (-(2 * Real.pi * τ.im)) := (Real.exp_pos _).le
  have hzim : z.im = t := ft_im_of_coe hz
  have ht0 : (0:ℝ) ≤ t := by linarith [hτ.2]
  have hnorm : ‖(z : ℂ)‖ = t := ft_norm_coe hz ht0
  have ht1 : (1:ℝ) ≤ 1 + t := by linarith
  have hE : (0:ℝ) < Real.exp (-(2 * Real.pi * τ.im)) := Real.exp_pos _
  have hz1 : (1:ℝ) ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have hz2 : (2:ℝ) ≤ z.im := by rw [hzim]; linarith [hτ.2, ht]
  have hD := norm_Delta_funnel τ hτ
  have bE14 := h14 z hz2
  have bLz := hL z hz1
  have bE10 := h10 z hz2
  have bD2 := hD2b z hz1
  have bLz' : ‖ℓ.L z‖ ≤ CL * (1 + t) := by
    have := bLz; rw [hnorm] at this; exact this
  have hterm1 : ‖(-3456 : ℂ) * DeltaFun τ * E14Fun z * ℓ.L z‖
      ≤ (6912 * C14 * CL) * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) := by
    rw [show (-3456 : ℂ) * DeltaFun τ * E14Fun z * ℓ.L z
      = ((-3456 : ℂ) * DeltaFun τ) * (E14Fun z * ℓ.L z) by ring]
    calc ‖((-3456 : ℂ) * DeltaFun τ) * (E14Fun z * ℓ.L z)‖
        = ‖(-3456 : ℂ) * DeltaFun τ‖ * ‖E14Fun z * ℓ.L z‖ := norm_mul _ _
      _ ≤ (3456 * (2 * Real.exp (-(2 * Real.pi * τ.im)))) * (C14 * (CL * (1 + t))) := by
          refine mul_le_mul ?_ (norm_mono_le bE14 bLz') (norm_nonneg _) (by positivity)
          calc ‖(-3456 : ℂ) * DeltaFun τ‖ = 3456 * ‖DeltaFun τ‖ := by
                rw [norm_mul, show ‖(-3456 : ℂ)‖ = 3456 by norm_num]
            _ ≤ 3456 * (2 * Real.exp (-(2 * Real.pi * τ.im))) :=
                mul_le_mul_of_nonneg_left hD (by norm_num)
      _ = (6912 * C14 * CL) * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) := by ring
      _ ≤ (6912 * C14 * CL) * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) := by
          have hbase : (6912 * C14 * CL) * Real.exp (-(2 * Real.pi * τ.im))
              ≤ (6912 * C14 * CL) * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) :=
            mul_exp_scale_le (by positivity) (le_of_lt hE) hN0
          exact mul_le_mul_of_nonneg_right hbase (by linarith : (0:ℝ) ≤ 1 + t)
  have hP' : ‖psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ‖
      ≤ Cd * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) := by
    have h := scale_inflate' (τ := τ) (d := 1) (hdpsi τ hτ) hCd.le (le_of_lt hE) (by norm_num)
    rw [hN]; exact h
  have hterm2 : ‖(psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) * E10Fun z
        * (UFun z ^ 2 - VFun z ^ 2)‖
      ≤ (Cd * C10 * CD2) * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) := by
    rw [show (psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) * E10Fun z
          * (UFun z ^ 2 - VFun z ^ 2)
        = -((psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ) * (E10Fun z
          * (UFun z ^ 2 - VFun z ^ 2))) by ring, norm_neg]
    calc ‖(psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ) * (E10Fun z * (UFun z ^ 2 - VFun z ^ 2))‖
        = ‖psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ‖
          * ‖E10Fun z * (UFun z ^ 2 - VFun z ^ 2)‖ := norm_mul _ _
      _ ≤ (Cd * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))) * (C10 * CD2) :=
          mul_le_mul hP' (norm_mono_le bE10 bD2) (norm_nonneg _) (by positivity)
      _ = (Cd * C10 * CD2) * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) := by ring
      _ ≤ (Cd * C10 * CD2) * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) :=
          mul_one_add_le (by positivity) ht0
  have hreg : A24 ℓ τ z = (-3456 : ℂ) * DeltaFun τ * E14Fun z * ℓ.L z
      - (psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) * E10Fun z * (UFun z ^ 2 - VFun z ^ 2) := by
    simp only [A24]
  rw [hreg]
  refine le_trans (norm_sub_le _ _) ?_
  calc _ ≤ (6912 * C14 * CL) * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t)
        + (Cd * C10 * CD2) * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) :=
        add_le_add hterm1 hterm2
    _ = (6912 * C14 * CL + Cd * C10 * CD2) * (scale τ) ^ N
          * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) := by ring
    _ ≤ (6912 * C14 * CL + Cd * C10 * CD2 + 1) * (scale τ) ^ N
          * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) := by
        have hpos : (0:ℝ) ≤ (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) := by
          positivity
        nlinarith [hpos]

/-- `‖A24ref ℓ τ z‖ ≤ C (scale τ)^N e^{-2π Im τ}(1+t)` on the funnel contour. -/
theorem A24ref_funnel (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖A24ref ℓ τ z‖ ≤ C * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) := by
  obtain ⟨Cd, Nd, hCd, hNd, hdpsi⟩ := psi_sub_funnel ℓ
  obtain ⟨CL, hCL, hLr0⟩ := norm_Lref_le ℓ
  refine ⟨6912 * 25 * CL + 2 * Cd * 265 * 161 + 1, Nd + 1, by positivity, by positivity,
    fun τ z t hτ ht hz => ?_⟩
  set N : ℝ := Nd + 1 with hN
  have hN0 : (0:ℝ) ≤ N := by rw [hN]; linarith
  have hsN0 : (0:ℝ) ≤ (scale τ) ^ N := scale_rpow_nonneg' τ N
  have he0 : (0:ℝ) ≤ Real.exp (-(2 * Real.pi * τ.im)) := (Real.exp_pos _).le
  have hzim : z.im = t := ft_im_of_coe hz
  have ht0 : (0:ℝ) ≤ t := by linarith [hτ.2]
  have hnorm : ‖(z : ℂ)‖ = t := ft_norm_coe hz ht0
  have hE : (0:ℝ) < Real.exp (-(2 * Real.pi * τ.im)) := Real.exp_pos _
  have hz1 : (1:ℝ) ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have he1 : ‖Ept z‖ ≤ 1 := by
    rw [Work.Residues.norm_Ept, hzim]
    exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hτ.2, ht])
  have he2 : ‖(Ept z) ^ 2‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) he1
  have hD := norm_Delta_funnel τ hτ
  have hE14ref : ‖E14ref z‖ ≤ 25 := by
    rw [E14ref]
    calc ‖(1:ℂ) - 24 * (Ept z) ^ 2‖ ≤ ‖(1:ℂ)‖ + ‖(24 : ℂ) * (Ept z) ^ 2‖ := norm_sub_le _ _
      _ ≤ 1 + 24 := by
          rw [norm_one, norm_mul, show ‖(24:ℂ)‖ = 24 by norm_num]; linarith
      _ = 25 := by norm_num
  have hE10ref : ‖E10ref z‖ ≤ 265 := by
    rw [E10ref]
    calc ‖(1:ℂ) - 264 * (Ept z) ^ 2‖ ≤ ‖(1:ℂ)‖ + ‖(264 : ℂ) * (Ept z) ^ 2‖ := norm_sub_le _ _
      _ ≤ 1 + 264 := by
          rw [norm_one, norm_mul, show ‖(264:ℂ)‖ = 264 by norm_num]; linarith
      _ = 265 := by norm_num
  have hD2ref : ‖D2ref z‖ ≤ 161 := norm_D2ref_le hz1
  have hLref : ‖Lref ℓ z‖ ≤ CL * (1 + t) := by
    have := hLr0 z hz1; rw [hnorm] at this; exact this
  have hterm1 : ‖(-3456 : ℂ) * DeltaFun τ * E14ref z * Lref ℓ z‖
      ≤ (6912 * 25 * CL) * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) := by
    rw [show (-3456 : ℂ) * DeltaFun τ * E14ref z * Lref ℓ z
      = ((-3456 : ℂ) * DeltaFun τ) * (E14ref z * Lref ℓ z) by ring]
    calc ‖((-3456 : ℂ) * DeltaFun τ) * (E14ref z * Lref ℓ z)‖
        = ‖(-3456 : ℂ) * DeltaFun τ‖ * ‖E14ref z * Lref ℓ z‖ := norm_mul _ _
      _ ≤ (3456 * (2 * Real.exp (-(2 * Real.pi * τ.im)))) * (25 * (CL * (1 + t))) := by
          refine mul_le_mul ?_ (norm_mono_le hE14ref hLref) (norm_nonneg _) (by positivity)
          calc ‖(-3456 : ℂ) * DeltaFun τ‖ = 3456 * ‖DeltaFun τ‖ := by
                rw [norm_mul, show ‖(-3456 : ℂ)‖ = 3456 by norm_num]
            _ ≤ 3456 * (2 * Real.exp (-(2 * Real.pi * τ.im))) :=
                mul_le_mul_of_nonneg_left hD (by norm_num)
      _ = (6912 * 25 * CL) * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) := by ring
      _ ≤ (6912 * 25 * CL) * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) := by
          have hbase : (6912 * 25 * CL) * Real.exp (-(2 * Real.pi * τ.im))
              ≤ (6912 * 25 * CL) * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) :=
            mul_exp_scale_le (by positivity) (le_of_lt hE) hN0
          exact mul_le_mul_of_nonneg_right hbase (by linarith : (0:ℝ) ≤ 1 + t)
  have hP' : ‖psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ‖
      ≤ Cd * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) := by
    have h := scale_inflate' (τ := τ) (d := 1) (hdpsi τ hτ) hCd.le (le_of_lt hE) (by norm_num)
    rw [hN]; exact h
  have hterm2 : ‖(psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) * E10ref z * D2ref z‖
      ≤ (2 * Cd * 265 * 161) * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) := by
    rw [show (psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) * E10ref z * D2ref z
      = -((psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ) * (E10ref z * D2ref z)) by ring, norm_neg]
    calc ‖(psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ) * (E10ref z * D2ref z)‖
        = ‖psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ‖ * ‖E10ref z * D2ref z‖ := norm_mul _ _
      _ ≤ (Cd * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))) * (265 * 161) :=
          mul_le_mul hP' (norm_mono_le hE10ref hD2ref) (norm_nonneg _) (by positivity)
      _ = (Cd * 265 * 161) * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) := by ring
      _ ≤ (2 * Cd * 265 * 161) * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) := by
          have hpos : (0:ℝ) ≤ (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) := by positivity
          nlinarith [hpos, hCd.le]
      _ ≤ (2 * Cd * 265 * 161) * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) :=
          mul_one_add_le (by positivity) ht0
  have hreg : A24ref ℓ τ z = (-3456 : ℂ) * DeltaFun τ * E14ref z * Lref ℓ z
      - (psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) * E10ref z * D2ref z := by
    simp only [A24ref]
  rw [hreg]
  refine le_trans (norm_sub_le _ _) ?_
  calc _ ≤ (6912 * 25 * CL) * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t)
        + (2 * Cd * 265 * 161) * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) :=
        add_le_add hterm1 hterm2
    _ = (6912 * 25 * CL + 2 * Cd * 265 * 161) * (scale τ) ^ N
          * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) := by ring
    _ ≤ (6912 * 25 * CL + 2 * Cd * 265 * 161 + 1) * (scale τ) ^ N
          * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) := by
        have hpos : (0:ℝ) ≤ (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) := by
          positivity
        nlinarith [hpos]

/-- `‖A24 - A24ref‖ ≤ C (scale τ)^N e^{-2π Im τ}(1+t)‖Ept z‖³` on the funnel contour. -/
theorem A24diff_funnel (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖A24 ℓ τ z - A24ref ℓ τ z‖
        ≤ C * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) * ‖Ept z‖ ^ 3 := by
  obtain ⟨Cd, Nd, hCd, hNd, hdpsi⟩ := psi_sub_funnel ℓ
  obtain ⟨C14, hC14, h14⟩ := norm_E14_le
  obtain ⟨CLr, hCLr, hLr0⟩ := norm_Lref_le ℓ
  obtain ⟨CdL, hCdL, hdL0⟩ := norm_dL_le ℓ
  obtain ⟨CdE14, hCdE14, hdE14_0⟩ := norm_dE14_le
  obtain ⟨C10, hC10, h10⟩ := norm_E10_le
  obtain ⟨CdD2, hCdD2, hdD2_0⟩ := norm_dD2_le
  obtain ⟨CdE10, hCdE10, hdE10_0⟩ := norm_dE10_le
  refine ⟨3456 * 2 * (C14 * CdL + CdE14 * CLr) + Cd * (C10 * CdD2 + CdE10 * 161) + 1,
    Nd + 1, by positivity, by positivity, fun τ z t hτ ht hz => ?_⟩
  set N : ℝ := Nd + 1 with hN
  have hN0 : (0:ℝ) ≤ N := by rw [hN]; linarith
  have hsN0 : (0:ℝ) ≤ (scale τ) ^ N := scale_rpow_nonneg' τ N
  have he0 : (0:ℝ) ≤ Real.exp (-(2 * Real.pi * τ.im)) := (Real.exp_pos _).le
  have hzim : z.im = t := ft_im_of_coe hz
  have ht0 : (0:ℝ) ≤ t := by linarith [hτ.2]
  have hnorm : ‖(z : ℂ)‖ = t := ft_norm_coe hz ht0
  have hE : (0:ℝ) < Real.exp (-(2 * Real.pi * τ.im)) := Real.exp_pos _
  have hz1 : (1:ℝ) ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have hz2 : (2:ℝ) ≤ z.im := by rw [hzim]; linarith [hτ.2, ht]
  have hε0 : (0:ℝ) ≤ ‖Ept z‖ ^ 3 := by positivity
  have hε1 : ‖Ept z‖ ^ 3 ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (norm_Ept_le_one' hz1)
  have hε41 : ‖Ept z‖ ^ 4 ≤ ‖Ept z‖ ^ 3 :=
    pow_le_pow_of_le_one (norm_nonneg _) (norm_Ept_le_one' hz1) (by norm_num : 3 ≤ 4)
  have hD := norm_Delta_funnel τ hτ
  have bE14 := h14 z hz2
  have bLr := hLr0 z hz1
  have bdL := hdL0 z hz1
  have bdE14 := hdE14_0 z hz1
  have bE10 := h10 z hz2
  have bdD2 := hdD2_0 z hz1
  have bdE10 := hdE10_0 z hz1
  have hD2ref : ‖D2ref z‖ ≤ 161 := norm_D2ref_le hz1
  have bLr' : ‖Lref ℓ z‖ ≤ CLr * (1 + t) := by
    have := bLr; rw [hnorm] at this; exact this
  have hinner1 : ‖E14Fun z * dL ℓ z + dE14 z * Lref ℓ z‖
      ≤ (C14 * CdL + CdE14 * CLr) * (1 + t) * ‖Ept z‖ ^ 3 := by
    have hA : ‖E14Fun z * dL ℓ z‖ ≤ C14 * CdL * ‖Ept z‖ ^ 3 := by
      calc ‖E14Fun z * dL ℓ z‖ = ‖E14Fun z‖ * ‖dL ℓ z‖ := norm_mul _ _
        _ ≤ C14 * (CdL * ‖Ept z‖ ^ 3) := mul_le_mul bE14 bdL (norm_nonneg _) hC14.le
        _ = C14 * CdL * ‖Ept z‖ ^ 3 := by ring
    have hB : ‖dE14 z * Lref ℓ z‖ ≤ CdE14 * CLr * (1 + t) * ‖Ept z‖ ^ 3 := by
      calc ‖dE14 z * Lref ℓ z‖ = ‖dE14 z‖ * ‖Lref ℓ z‖ := norm_mul _ _
        _ ≤ (CdE14 * ‖Ept z‖ ^ 4) * (CLr * (1 + t)) :=
            mul_le_mul bdE14 bLr' (norm_nonneg _) (by positivity)
        _ ≤ (CdE14 * ‖Ept z‖ ^ 3) * (CLr * (1 + t)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left hε41 hCdE14.le
        _ = CdE14 * CLr * (1 + t) * ‖Ept z‖ ^ 3 := by ring
    calc ‖E14Fun z * dL ℓ z + dE14 z * Lref ℓ z‖
        ≤ ‖E14Fun z * dL ℓ z‖ + ‖dE14 z * Lref ℓ z‖ := norm_add_le _ _
      _ ≤ C14 * CdL * ‖Ept z‖ ^ 3 + CdE14 * CLr * (1 + t) * ‖Ept z‖ ^ 3 := add_le_add hA hB
      _ ≤ (C14 * CdL + CdE14 * CLr) * (1 + t) * ‖Ept z‖ ^ 3 := by
          have h2 : C14 * CdL * ‖Ept z‖ ^ 3 ≤ C14 * CdL * (1 + t) * ‖Ept z‖ ^ 3 := by
            have h3 : C14 * CdL ≤ C14 * CdL * (1 + t) := mul_one_add_le (by positivity) ht0
            exact mul_le_mul_of_nonneg_right h3 hε0
          calc C14 * CdL * ‖Ept z‖ ^ 3 + CdE14 * CLr * (1 + t) * ‖Ept z‖ ^ 3
              ≤ C14 * CdL * (1 + t) * ‖Ept z‖ ^ 3
                + CdE14 * CLr * (1 + t) * ‖Ept z‖ ^ 3 := by linarith [h2]
            _ = (C14 * CdL + CdE14 * CLr) * (1 + t) * ‖Ept z‖ ^ 3 := by ring
  have hinner2 : ‖E10Fun z * dD2 z + dE10 z * D2ref z‖
      ≤ (C10 * CdD2 + CdE10 * 161) * (1 + t) * ‖Ept z‖ ^ 3 := by
    have hA : ‖E10Fun z * dD2 z‖ ≤ C10 * CdD2 * ‖Ept z‖ ^ 3 := by
      calc ‖E10Fun z * dD2 z‖ = ‖E10Fun z‖ * ‖dD2 z‖ := norm_mul _ _
        _ ≤ C10 * (CdD2 * ‖Ept z‖ ^ 3) := mul_le_mul bE10 bdD2 (norm_nonneg _) hC10.le
        _ = C10 * CdD2 * ‖Ept z‖ ^ 3 := by ring
    have hB : ‖dE10 z * D2ref z‖ ≤ CdE10 * 161 * (1 + t) * ‖Ept z‖ ^ 3 := by
      calc ‖dE10 z * D2ref z‖ = ‖dE10 z‖ * ‖D2ref z‖ := norm_mul _ _
        _ ≤ (CdE10 * ‖Ept z‖ ^ 4) * 161 :=
            mul_le_mul bdE10 hD2ref (norm_nonneg _)
              (mul_nonneg hCdE10.le (pow_nonneg (norm_nonneg _) 4))
        _ ≤ (CdE10 * ‖Ept z‖ ^ 3) * 161 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hε41 hCdE10.le) (by norm_num)
        _ = CdE10 * 161 * ‖Ept z‖ ^ 3 := by ring
        _ ≤ CdE10 * 161 * (1 + t) * ‖Ept z‖ ^ 3 := by
            have h3 : CdE10 * 161 ≤ CdE10 * 161 * (1 + t) := mul_one_add_le (by positivity) ht0
            exact mul_le_mul_of_nonneg_right h3 hε0
    calc ‖E10Fun z * dD2 z + dE10 z * D2ref z‖
        ≤ ‖E10Fun z * dD2 z‖ + ‖dE10 z * D2ref z‖ := norm_add_le _ _
      _ ≤ C10 * CdD2 * ‖Ept z‖ ^ 3 + CdE10 * 161 * (1 + t) * ‖Ept z‖ ^ 3 := add_le_add hA hB
      _ ≤ (C10 * CdD2 + CdE10 * 161) * (1 + t) * ‖Ept z‖ ^ 3 := by
          have h2 : C10 * CdD2 * ‖Ept z‖ ^ 3 ≤ C10 * CdD2 * (1 + t) * ‖Ept z‖ ^ 3 := by
            have h3 : C10 * CdD2 ≤ C10 * CdD2 * (1 + t) := mul_one_add_le (by positivity) ht0
            exact mul_le_mul_of_nonneg_right h3 hε0
          calc C10 * CdD2 * ‖Ept z‖ ^ 3 + CdE10 * 161 * (1 + t) * ‖Ept z‖ ^ 3
              ≤ C10 * CdD2 * (1 + t) * ‖Ept z‖ ^ 3
                + CdE10 * 161 * (1 + t) * ‖Ept z‖ ^ 3 := by linarith [h2]
            _ = (C10 * CdD2 + CdE10 * 161) * (1 + t) * ‖Ept z‖ ^ 3 := by ring
  have hP' : ‖psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ‖
      ≤ Cd * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) := by
    have h := scale_inflate' (τ := τ) (d := 1) (hdpsi τ hτ) hCd.le (le_of_lt hE) (by norm_num)
    rw [hN]; exact h
  have hA : ‖(-3456 : ℂ) * DeltaFun τ * (E14Fun z * dL ℓ z + dE14 z * Lref ℓ z)‖
      ≤ (3456 * 2 * (C14 * CdL + CdE14 * CLr)) * (scale τ) ^ N
        * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) * ‖Ept z‖ ^ 3 := by
    rw [show (-3456 : ℂ) * DeltaFun τ * (E14Fun z * dL ℓ z + dE14 z * Lref ℓ z)
      = ((-3456 : ℂ) * DeltaFun τ) * (E14Fun z * dL ℓ z + dE14 z * Lref ℓ z) by ring]
    calc ‖((-3456 : ℂ) * DeltaFun τ) * (E14Fun z * dL ℓ z + dE14 z * Lref ℓ z)‖
        = ‖(-3456 : ℂ) * DeltaFun τ‖ * ‖E14Fun z * dL ℓ z + dE14 z * Lref ℓ z‖ := norm_mul _ _
      _ ≤ (3456 * (2 * Real.exp (-(2 * Real.pi * τ.im))))
            * ((C14 * CdL + CdE14 * CLr) * (1 + t) * ‖Ept z‖ ^ 3) := by
          refine mul_le_mul ?_ hinner1 (norm_nonneg _) (by positivity)
          calc ‖(-3456 : ℂ) * DeltaFun τ‖ = 3456 * ‖DeltaFun τ‖ := by
                rw [norm_mul, show ‖(-3456 : ℂ)‖ = 3456 by norm_num]
            _ ≤ 3456 * (2 * Real.exp (-(2 * Real.pi * τ.im))) :=
                mul_le_mul_of_nonneg_left hD (by norm_num)
      _ = (3456 * 2 * (C14 * CdL + CdE14 * CLr)) * Real.exp (-(2 * Real.pi * τ.im))
            * (1 + t) * ‖Ept z‖ ^ 3 := by ring
      _ ≤ (3456 * 2 * (C14 * CdL + CdE14 * CLr)) * (scale τ) ^ N
            * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) * ‖Ept z‖ ^ 3 := by
          have h := mul_exp_scale_le (τ := τ) (c := 3456 * 2 * (C14 * CdL + CdE14 * CLr))
            (e := Real.exp (-(2 * Real.pi * τ.im))) (by positivity) (le_of_lt hE) hN0
          have h2 : (0:ℝ) ≤ (1 + t) * ‖Ept z‖ ^ 3 := by positivity
          calc 3456 * 2 * (C14 * CdL + CdE14 * CLr) * Real.exp (-(2 * Real.pi * τ.im))
                * (1 + t) * ‖Ept z‖ ^ 3
              = (3456 * 2 * (C14 * CdL + CdE14 * CLr) * Real.exp (-(2 * Real.pi * τ.im)))
                * ((1 + t) * ‖Ept z‖ ^ 3) := by ring
            _ ≤ (3456 * 2 * (C14 * CdL + CdE14 * CLr) * (scale τ) ^ N
                  * Real.exp (-(2 * Real.pi * τ.im))) * ((1 + t) * ‖Ept z‖ ^ 3) :=
                mul_le_mul_of_nonneg_right h h2
            _ = (3456 * 2 * (C14 * CdL + CdE14 * CLr)) * (scale τ) ^ N
                * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) * ‖Ept z‖ ^ 3 := by ring
  have hB : ‖(psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ)
        * (E10Fun z * dD2 z + dE10 z * D2ref z)‖
      ≤ (Cd * (C10 * CdD2 + CdE10 * 161)) * (scale τ) ^ N
        * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) * ‖Ept z‖ ^ 3 := by
    rw [show (psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ)
        * (E10Fun z * dD2 z + dE10 z * D2ref z)
      = -((psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)
        * (E10Fun z * dD2 z + dE10 z * D2ref z)) by ring, norm_neg]
    calc ‖(psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)
          * (E10Fun z * dD2 z + dE10 z * D2ref z)‖
        = ‖psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ‖
          * ‖E10Fun z * dD2 z + dE10 z * D2ref z‖ := norm_mul _ _
      _ ≤ (Cd * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)))
            * ((C10 * CdD2 + CdE10 * 161) * (1 + t) * ‖Ept z‖ ^ 3) :=
          mul_le_mul hP' hinner2 (norm_nonneg _) (by positivity)
      _ = (Cd * (C10 * CdD2 + CdE10 * 161)) * (scale τ) ^ N
            * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) * ‖Ept z‖ ^ 3 := by ring
  have hreg : A24 ℓ τ z - A24ref ℓ τ z
      = (-3456 : ℂ) * DeltaFun τ * (E14Fun z * dL ℓ z + dE14 z * Lref ℓ z)
        - (psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ)
          * (E10Fun z * dD2 z + dE10 z * D2ref z) := by
    simp only [A24, A24ref, dL, dE14, dD2, dE10, Lref, E14ref]
    ring
  rw [hreg]
  refine le_trans (norm_sub_le _ _) ?_
  calc _ ≤ (3456 * 2 * (C14 * CdL + CdE14 * CLr)) * (scale τ) ^ N
        * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) * ‖Ept z‖ ^ 3
        + (Cd * (C10 * CdD2 + CdE10 * 161)) * (scale τ) ^ N
        * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) * ‖Ept z‖ ^ 3 := add_le_add hA hB
    _ = (3456 * 2 * (C14 * CdL + CdE14 * CLr) + Cd * (C10 * CdD2 + CdE10 * 161))
          * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) * ‖Ept z‖ ^ 3 := by ring
    _ ≤ (3456 * 2 * (C14 * CdL + CdE14 * CLr) + Cd * (C10 * CdD2 + CdE10 * 161) + 1)
          * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t) * ‖Ept z‖ ^ 3 := by
        have hpos : (0:ℝ) ≤ (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t)
            * ‖Ept z‖ ^ 3 := by positivity
        nlinarith [hpos]


end

end Work.Asymptotics.Funnel24
