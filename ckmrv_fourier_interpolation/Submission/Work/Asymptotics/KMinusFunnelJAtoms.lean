/-
# `τ`-atom bounds on the funnel (shared interface for the `d = 24` tail estimates)

On the funnel `Funnel τ = {τ ∈ 𝒟 : 2 ≤ Im τ}` the atoms entering the `d = 24` cusp expansion
of `K₋` grow at most like `(scale τ)^N`; the atoms involving the modular `j`-invariant pick up a
factor `e^{2π Im τ}`, and the near-identity

  `ψ₄(τ)E₈(τ) - ψ₂(τ)E₁₀(τ) = O(‖q(τ)‖ (scale τ)^N)`

(`Work.Asymptotics.psi4E8_sub_psi2E10_funnel`) kills that factor whenever the combination
carries `j(τ)`: this is the cancellation underlying the CKMRV `E`-order cancellation.

All statements are in the namespace `Work.Asymptotics.KF24` so that they can be used alongside
the (similarly named) lemmas of other files.
-/
import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Funnel24Aux

namespace Work.Asymptotics.KF24

open UpperHalfPlane
open Work.Kernels
open Work.Residues (Ept)

noncomputable section

/-! ## Elementary helpers -/

theorem scale_rpow_nonneg' (τ : ℍ) (N : ℝ) : 0 ≤ (scale τ) ^ N :=
  Real.rpow_nonneg (le_of_lt (scale_pos τ)) N

theorem one_le_scale_rpow' (τ : ℍ) {N : ℝ} (hN : 0 ≤ N) : 1 ≤ (scale τ) ^ N :=
  Real.one_le_rpow (one_le_scale τ) hN

/-- `e^A · e^{-A} = 1`. -/
theorem exp_mul_exp_neg (A : ℝ) : Real.exp A * Real.exp (-A) = 1 := by
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- `e^A · e^A · e^{-A} = e^A`. -/
theorem exp_mul_exp_mul_exp_neg (A : ℝ) : Real.exp A * Real.exp A * Real.exp (-A) = Real.exp A := by
  rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- `‖Ept z‖ ≤ 1` for `1 ≤ Im z`. -/
theorem norm_Ept_le_one' {z : ℍ} (hz : 1 ≤ z.im) : ‖Ept z‖ ≤ 1 := by
  rw [Work.Residues.norm_Ept]
  exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hz])

/-! ## The `j`-invariant and `Δ` on the funnel -/

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
    rw [Real.exp_neg]; field_simp
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
    ‖DeltaFun τ‖ ≤ 2 * Real.exp (-(2 * Real.pi * τ.im)) := by
  rw [← norm_qParamFun]
  exact DeltaFun_funnel_le τ hτ

/-! ## The `τ`-atoms `ψ₂E₁₀`, `ψ₄E₈` and their difference -/

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
  calc ‖psi2 ℓ τ‖ * ‖E10Fun τ‖ ≤ (Cψ * (scale τ) ^ Nψ) * ((3 / 2) * C6) :=
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

end

end Work.Asymptotics.KF24
