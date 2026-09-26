import Mathlib
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.CKFinal.LineDecay.Ncusp24_V0L_lowstrip

/-!
# The `𝓛`-piece of the `d = 24` cusp numerator on the funnel

This file proves `Work.CKFinal.LineDecay.Ncusp24_V0L_funnel`, the estimate for the
`𝓛`-piece `𝒱₀^𝓛 = (3 j(τ)X(τ) - 1728 ξ₄(τ)E₈(τ))·𝓛(τ)` of the `τ`-factor `𝒱₀ = 3456E₄³ + 3Dj
- 1728ψ₄E₈` of CKMRV Lemma 4.11 for `d = 24` (the companion piece `𝒱₀^{𝓛_S}` is
`Work.CKFinal.LineDecay.Ncusp24_V0LS_funnel`; the two together give the exponentially small
bound on `𝒱₀` used in `Work.Asymptotics.ncusp_delta_funnel_zfree`).

## The mathematics

`Work.Residues.B0core_eq` gives the *exact* identity

  `B0core τ = 1728 ξ₄(τ)E₈(τ) - 3 j(τ)X(τ)`,   `X = ξ₄E₈ - ξ₂E₁₀`,

so `𝒱₀^𝓛 τ = -B0core τ · 𝓛 τ`.  The two classical cusp estimates then apply:

* `B0core = E₄²Ñ/Δ` with `Ñ = 3ξ₂E₄²E₆ - 2ξ₄E₄³ - ξ₄E₆²` vanishing to fourth order at the
  cusp while `Δ` vanishes to second order, so `B0core` vanishes to *second* order:
  `Work.Residues.B0core_cusp : CuspBound B0core 0 2` gives
  `‖B0core τ‖ ≤ C e^{-2π Im τ}` for `Im τ ≥ H`;
* `Work.Residues.L_cusp ℓ : CuspBound 𝓛 1 0` gives `‖𝓛 τ‖ ≤ C(1 + ‖τ‖)` for `Im τ ≥ 1`.

Both are threshold statements, so the bounded strip `2 ≤ Im τ ≤ H` of the funnel is
handled separately, by compactness (`Work.CKFinal.LineDecay.Ncusp24_V0L_lowstrip`).
The conclusion holds with the polynomial exponent `A = 1`.
-/

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

noncomputable section

/-- `e^{-πy}² = e^{-2πy}`. -/
private lemma exp_neg_pi_sq (y : ℝ) :
    Real.exp (-(Real.pi * y)) ^ 2 = Real.exp (-(2 * Real.pi * y)) := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-- **The `𝓛`-piece of `𝒱₀` is `O((1+|τ|) e^{-2π Im τ})` on the funnel.**
Equivalently, the `𝓛`-coefficient `3jX - 1728ξ₄E₈ = -B0core` vanishes to second order at
the cusp. -/
theorem Ncusp24_V0L_funnel (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖(3 * Work.Kernels.jInvariantFun τ * Work.Residues.Xfun τ
          - 1728 * Work.Kernels.xi4Fun τ * Work.Kernels.E8Fun τ) * ℓ.L τ‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * τ.im)) ^ 2 := by
  obtain ⟨HL, CL, hCL, hL⟩ := Work.Residues.L_cusp ℓ
  obtain ⟨HB, CB, hCB, hB⟩ := Work.Residues.B0core_cusp
  set K : ℝ := max (max HL HB) 2 with hK
  have hHL : HL ≤ K := by
    rw [hK]; exact le_trans (le_max_left HL HB) (le_max_left _ 2)
  have hHB : HB ≤ K := by
    rw [hK]; exact le_trans (le_max_right HL HB) (le_max_left _ 2)
  obtain ⟨D, hD⟩ := Ncusp24_V0L_lowstrip ℓ K
  set D' : ℝ := max D 0 with hD'
  have hD'0 : 0 ≤ D' := by rw [hD']; exact le_max_right D 0
  set Cf : ℝ := max (CB * CL) (D' * Real.exp (2 * Real.pi * K)) + 1 with hCf
  have hCf0 : 0 < Cf := by
    have h1 : 0 ≤ CB * CL := mul_nonneg hCB.le hCL.le
    have h2 : 0 ≤ D' * Real.exp (2 * Real.pi * K) := mul_nonneg hD'0 (Real.exp_pos _).le
    have h3 : 0 ≤ max (CB * CL) (D' * Real.exp (2 * Real.pi * K)) := le_trans h1 (le_max_left _ _)
    rw [hCf]; linarith
  refine ⟨Cf, 1, hCf0, by norm_num, ?_⟩
  intro τ hτ
  -- the algebraic reduction: the `𝓛`-piece is `-B0core · 𝓛`
  have hred : (3 * Work.Kernels.jInvariantFun τ * Work.Residues.Xfun τ
        - 1728 * Work.Kernels.xi4Fun τ * Work.Kernels.E8Fun τ) * ℓ.L τ
      = -(Work.Residues.B0core τ * ℓ.L τ) := by
    rw [Work.Residues.B0core_eq τ]
    ring
  rw [hred, norm_neg, exp_neg_pi_sq τ.im, Real.rpow_one]
  by_cases hlow : τ.im ≤ K
  · -- the bounded strip `2 ≤ Im τ ≤ K`
    have hb : ‖Work.Residues.B0core τ * ℓ.L τ‖ ≤ D' := by
      rw [hD']
      exact le_trans (hD τ hτ hlow) (le_max_left D 0)
    have hexp1 : (1 : ℝ) ≤ Real.exp (2 * Real.pi * K) * Real.exp (-(2 * Real.pi * τ.im)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [Real.pi_pos, hlow])
    have step1 : D' ≤ D' * (Real.exp (2 * Real.pi * K) * Real.exp (-(2 * Real.pi * τ.im))) :=
      le_mul_of_one_le_right hD'0 hexp1
    have step2 : D' * (Real.exp (2 * Real.pi * K) * Real.exp (-(2 * Real.pi * τ.im)))
        = (D' * Real.exp (2 * Real.pi * K)) * Real.exp (-(2 * Real.pi * τ.im)) := by ring
    have step3 : (D' * Real.exp (2 * Real.pi * K)) * Real.exp (-(2 * Real.pi * τ.im))
        ≤ Cf * Real.exp (-(2 * Real.pi * τ.im)) := by
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      rw [hCf]
      linarith [le_max_right (CB * CL) (D' * Real.exp (2 * Real.pi * K))]
    have step4 : Cf * Real.exp (-(2 * Real.pi * τ.im))
        ≤ Cf * (1 + ‖(τ : ℂ)‖) * Real.exp (-(2 * Real.pi * τ.im)) := by
      have h1 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by have := norm_nonneg (τ : ℂ); linarith
      have h2 : Cf ≤ Cf * (1 + ‖(τ : ℂ)‖) := le_mul_of_one_le_right hCf0.le h1
      exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    calc ‖Work.Residues.B0core τ * ℓ.L τ‖ ≤ D' := hb
      _ ≤ D' * (Real.exp (2 * Real.pi * K) * Real.exp (-(2 * Real.pi * τ.im))) := step1
      _ = (D' * Real.exp (2 * Real.pi * K)) * Real.exp (-(2 * Real.pi * τ.im)) := step2
      _ ≤ Cf * Real.exp (-(2 * Real.pi * τ.im)) := step3
      _ ≤ Cf * (1 + ‖(τ : ℂ)‖) * Real.exp (-(2 * Real.pi * τ.im)) := step4
  · -- the tail of the funnel `K < Im τ`: the two cusp bounds apply
    have hhigh : K < τ.im := not_le.mp hlow
    have hLτ : ‖ℓ.L τ‖ ≤ CL * (1 + ‖(τ : ℂ)‖) := by
      have h := hL τ (le_trans hHL (le_of_lt hhigh))
      simpa using h
    have hBτ : ‖Work.Residues.B0core τ‖ ≤ CB * Real.exp (-(Real.pi * τ.im)) ^ 2 := by
      have h := hB τ (le_trans hHB (le_of_lt hhigh))
      simpa [Work.Residues.tpar] using h
    rw [norm_mul]
    have hle : CB * CL ≤ Cf := by
      rw [hCf]
      linarith [le_max_left (CB * CL) (D' * Real.exp (2 * Real.pi * K))]
    calc ‖Work.Residues.B0core τ‖ * ‖ℓ.L τ‖
        ≤ (CB * Real.exp (-(Real.pi * τ.im)) ^ 2) * (CL * (1 + ‖(τ : ℂ)‖)) :=
          mul_le_mul hBτ hLτ (norm_nonneg _) (by positivity)
      _ = (CB * CL) * (1 + ‖(τ : ℂ)‖) * Real.exp (-(2 * Real.pi * τ.im)) := by
          rw [exp_neg_pi_sq τ.im]; ring
      _ ≤ Cf * (1 + ‖(τ : ℂ)‖) * Real.exp (-(2 * Real.pi * τ.im)) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hle (by positivity)) (by positivity)

end

end Work.CKFinal.LineDecay
