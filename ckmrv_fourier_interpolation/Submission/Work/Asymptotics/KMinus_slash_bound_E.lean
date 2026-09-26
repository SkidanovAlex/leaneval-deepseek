import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KMinusCuspBallLimit
import Submission.Work.Asymptotics.MFix.Cusp0Flat
import Submission.Work.Asymptotics.ERegDefs
import Submission.Work.Asymptotics.EReg_identities
import Submission.Work.Asymptotics.EReg_atom_bounds
import Submission.Work.Asymptotics.EReg_alpha8_bound
import Submission.Work.Asymptotics.EReg_alpha24_bound
import Submission.Work.Asymptotics.mdiff_eta
import Submission.Work.Asymptotics.Ncusp_EReg_crude
import Submission.Work.Asymptotics.Ncusp_EReg_crude_24

/-!
# The CKMRV `E`-order bound for `K_-`

This file proves `Work.Asymptotics.KMinus_slash_bound_E`: on the cusp-`0` tile
`E = {τ : ℍ | 3/2 ≤ (S • τ).im}` the `q`-expansion of `K_-` along the boundary is controlled
by `(scale τ)^N (1 + ‖z‖)² e^{-π Im z} / ‖Δ(z)(j(τ) − j(z))‖`, with no hypothesis on `τ` beyond
`τ ∈ E` — the `E`-region form of CKMRV Lemma 4.12 (`quotientbounds1new`), in which the factor
`1/Δ(τ)` of the paper's ball version is replaced by a polynomial in `scale τ`.

Two steps:

* `Work.Asymptotics.Ncusp_EReg_crude` — the *crude* bound `‖Ncusp ℓ d τ z‖ ≤ C (scale τ)^N
  e^{π Im z}` on `E` (with `Ncusp` the cleared cusp numerator, so that the `τ`-dependence is
  polynomial); this is where the CKMRV `E`-order cancellation (the identities
  `ψ₄E₈ - ψ₂E₁₀ = 𝓛X + 𝓛_S Y` with `X = (9/2)U V² W E₄`, `Y = (9/2)U V W² E₄`) is used;
* `Work.Asymptotics.slash_bound_of_crude_E` — the Schwarz-lemma upgrade of the crude bound to
  the sharp one, using the `1`-periodicity of `z ↦ Ecusp z · Ncusp ℓ d τ z` and the vanishing
  of its cusp limit.
-/

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

set_option maxHeartbeats 1000000

noncomputable section

/-- **The Schwarz-lemma step.**  A crude bound for the cleared numerator `Ncusp` on the tile `E`
(with the `τ`-dependence in a polynomial in `scale τ`) implies the sharp CKMRV bound. -/
theorem slash_bound_of_crude_E (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hcrude : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : UpperHalfPlane),
      τ ∈ Work.Asymptotics.EReg → 1 ≤ z.im →
        ‖Work.Asymptotics.Ncusp ℓ d τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N * Real.exp (Real.pi * z.im)) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : UpperHalfPlane),
      (3 / 2 : ℝ) ≤ (ModularGroup.S • τ).im → 1 ≤ z.im →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
        ‖(z : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) *
            Work.Kernels.KMinus ℓ d τ (ModularGroup.S • z)‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) *
              Real.exp (-(Real.pi * z.im)) /
            ‖Work.Kernels.DeltaFun z *
              (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
  obtain ⟨C₀, N, hC₀, hN, hbound⟩ := hcrude
  refine ⟨C₀ * Real.exp (2 * Real.pi) + 1, N, by positivity, hN, fun τ z hτ hz hne => ?_⟩
  -- Step 1: the sharp decay of `Ncusp` on `E`
  have hdec : ‖Work.Asymptotics.Ncusp ℓ d τ z‖
      ≤ C₀ * (Work.Kernels.scale τ) ^ N * Real.exp (2 * Real.pi) *
          Real.exp (-(Real.pi * z.im)) := by
    set g : ℍ → ℂ := fun w => Work.Asymptotics.Ecusp w * Work.Asymptotics.Ncusp ℓ d τ w with hg
    have hB : ∀ w : ℍ, 1 ≤ w.im → ‖g w‖ ≤ C₀ * (Work.Kernels.scale τ) ^ N := by
      intro w hw
      rw [hg, norm_mul, Work.Asymptotics.norm_Ecusp]
      have h := hbound τ w hτ hw
      calc Real.exp (-(Real.pi * w.im)) * ‖Work.Asymptotics.Ncusp ℓ d τ w‖
          ≤ Real.exp (-(Real.pi * w.im)) *
              (C₀ * (Work.Kernels.scale τ) ^ N * Real.exp (Real.pi * w.im)) :=
            mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
        _ = C₀ * (Work.Kernels.scale τ) ^ N := by
            rw [show Real.exp (-(Real.pi * w.im)) *
                  (C₀ * (Work.Kernels.scale τ) ^ N * Real.exp (Real.pi * w.im))
                = C₀ * (Work.Kernels.scale τ) ^ N *
                  (Real.exp (-(Real.pi * w.im)) * Real.exp (Real.pi * w.im)) by ring,
              ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    have hperp : ∀ w : ℍ, g ((1 : ℝ) +ᵥ w) = g w := by
      intro w
      simp only [hg, Work.Asymptotics.Ecusp_vadd_one, Work.Asymptotics.Ncusp_vadd_one]
      ring
    have hmd : MDiff g := by
      rw [hg]
      exact (UpperHalfPlane.mdifferentiable_iff).mpr (Work.Asymptotics.mdiff_eta ℓ d τ)
    have h := Work.Asymptotics.periodic_zero_cusp_decay_uhp (B := C₀ * (Work.Kernels.scale τ) ^ N)
      (by have := Work.Kernels.one_le_scale τ; positivity) hperp hmd hB
      (Work.Asymptotics.KMinusCuspBallLimit ℓ d hd τ) z hz
    rw [hg, norm_mul, Work.Asymptotics.norm_Ecusp] at h
    have h1 : ‖Work.Asymptotics.Ncusp ℓ d τ z‖ ≤ Real.exp (Real.pi * z.im) *
        (C₀ * (Work.Kernels.scale τ) ^ N * Real.exp (2 * Real.pi) *
          Real.exp (-(2 * Real.pi * z.im))) := by
      calc ‖Work.Asymptotics.Ncusp ℓ d τ z‖
          = Real.exp (Real.pi * z.im) *
              (Real.exp (-(Real.pi * z.im)) * ‖Work.Asymptotics.Ncusp ℓ d τ z‖) := by
            rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
        _ ≤ Real.exp (Real.pi * z.im) *
              (C₀ * (Work.Kernels.scale τ) ^ N * Real.exp (2 * Real.pi) *
                Real.exp (-(2 * Real.pi * z.im))) :=
            mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
    calc ‖Work.Asymptotics.Ncusp ℓ d τ z‖
        ≤ Real.exp (Real.pi * z.im) *
            (C₀ * (Work.Kernels.scale τ) ^ N * Real.exp (2 * Real.pi) *
              Real.exp (-(2 * Real.pi * z.im))) := h1
      _ = C₀ * (Work.Kernels.scale τ) ^ N * Real.exp (2 * Real.pi) *
            Real.exp (-(Real.pi * z.im)) := by
          rw [show Real.exp (Real.pi * z.im) *
                (C₀ * (Work.Kernels.scale τ) ^ N * Real.exp (2 * Real.pi) *
                  Real.exp (-(2 * Real.pi * z.im)))
              = C₀ * (Work.Kernels.scale τ) ^ N * Real.exp (2 * Real.pi) *
                (Real.exp (Real.pi * z.im) * Real.exp (-(2 * Real.pi * z.im))) by ring,
            ← Real.exp_add,
            show Real.pi * z.im + -(2 * Real.pi * z.im) = -(Real.pi * z.im) by ring]
  -- Step 2: identify the two sides
  have hD : Work.Kernels.DeltaFun z *
      (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) ≠ 0 :=
    mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z) (sub_ne_zero.mpr hne)
  have hkey : (z : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) *
        Work.Kernels.KMinus ℓ d τ (ModularGroup.S • z)
      = Work.Asymptotics.Ncusp ℓ d τ z /
        (Work.Kernels.DeltaFun z *
          (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) := by
    rw [Work.Asymptotics.Ncusp_ident ℓ d hd τ z hne, mul_div_cancel_left₀ _ hD]
  rw [hkey, norm_div]
  refine le_trans (div_le_div_of_nonneg_right ?_ (norm_nonneg _)) (le_refl _)
  have hX : (0 : ℝ) ≤ C₀ * (Work.Kernels.scale τ) ^ N * Real.exp (2 * Real.pi) := by
    have := Work.Kernels.one_le_scale τ
    positivity
  have hY : (1 : ℝ) ≤ (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) := by
    have := norm_nonneg (z : ℂ); nlinarith
  have hE : (0 : ℝ) < Real.exp (-(Real.pi * z.im)) := Real.exp_pos _
  calc ‖Work.Asymptotics.Ncusp ℓ d τ z‖
      ≤ C₀ * (Work.Kernels.scale τ) ^ N * Real.exp (2 * Real.pi) *
          Real.exp (-(Real.pi * z.im)) := hdec
    _ ≤ C₀ * (Work.Kernels.scale τ) ^ N * Real.exp (2 * Real.pi) *
          (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im)) := by
        have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hY hX) hE.le
        simpa [mul_assoc] using h
    _ ≤ (C₀ * Real.exp (2 * Real.pi) + 1) * (Work.Kernels.scale τ) ^ N *
          (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im)) := by
        apply mul_le_mul_of_nonneg_right _ hE.le
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [hX, hY, Real.exp_pos (2 * Real.pi), Work.Kernels.one_le_scale τ,
          Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N]

/-- **The CKMRV `E`-order bound for `K_-`**, `d = 8` or `d = 24`.

This is the `E`-region form of the paper's `quotientbounds1new`: on the tile
`E = {τ : ℍ | 3/2 ≤ (S • τ).im}` the slashed kernel is bounded by
`(scale τ)^N (1 + ‖z‖)² e^{-π Im z} / ‖Δ(z)(j(τ) - j(z))‖`. -/
theorem KMinus_slash_bound_E (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : UpperHalfPlane),
      (3 / 2 : ℝ) ≤ (ModularGroup.S • τ).im → 1 ≤ z.im →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
        ‖(z : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) *
            Work.Kernels.KMinus ℓ d τ (ModularGroup.S • z)‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) *
              Real.exp (-(Real.pi * z.im)) /
            ‖Work.Kernels.DeltaFun z *
              (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
  rcases hd with rfl | rfl
  · exact slash_bound_of_crude_E ℓ 8 (Or.inl rfl) (Ncusp_EReg_crude_8 ℓ)
  · exact slash_bound_of_crude_E ℓ 24 (Or.inr rfl) (Ncusp_EReg_crude_24 ℓ)

end

end Work.Asymptotics
