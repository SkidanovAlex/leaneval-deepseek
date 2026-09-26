import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KMinusCuspBallDefs
import Submission.Work.Asymptotics.KMinusCuspBallLimit
import Submission.Work.Asymptotics.ERegDefs
import Submission.Work.Asymptotics.mdiff_eta
import Submission.Work.Asymptotics.Ncusp_EReg_crude
import Submission.Work.Asymptotics.Ncusp_EReg_crude_24
import Submission.Work.Asymptotics.Xi8_bound_E
import Submission.Work.Asymptotics.Xi24_bound_E
import Submission.Work.Asymptotics.EpointAux
import Submission.Work.Asymptotics.Xi8_bound_E
import Submission.Work.Asymptotics.Xi24_bound_E

/-!
# The two CKMRV slash bounds on the cusp-`0` tile `E`

`Work.Asymptotics.slash_KPlus_E` and `Work.Asymptotics.slash_KMinus_E` are the CKMRV Lemma 4.12
(`quotientbounds1new`) bounds

  `‖z^{-(2-d/2)} K_±(τ, S z)‖ ≤ C (scale τ)^N (1+‖z‖)² e^{-π Im z} / ‖Δ(z)(j τ - j z)‖`

for `Im (S τ) ≥ 3/2` and `Im z ≥ 1`.  The `K₊` case follows from `Xi8_bound_E` / `Xi24_bound_E`
through `Xi8_eq` / `Xi24_eq` (this is `KPlus8_slash_bound_of_Xi8` / `KPlus24_slash_bound_of_Xi24`,
proved in `Epoint_Kfun.lean`).  The `K₋` case is the Schwarz-lemma upgrade of the *crude*
`E`-order bound `Ncusp_EReg_crude_8` / `Ncusp_EReg_crude_24` (`slash_crude_sharp_E`); the file
`KMinus_slash_bound_E.lean` proves exactly this, but its import list contains
`KMinusCuspBallBound`, whose closure clashes with `KPlusXiDefs` (duplicate
`Work.Asymptotics.norm_qParamFun_le_one` on the `E_jdiff_small` side; here the clash is the
duplicate `Work.Asymptotics.continuous_scale` with `MiddleRange.Basic`).  The proof below is the
same argument with the unused import dropped, so that this module can be imported alongside
`Xi8_bound_E`, `Epoint_Kfun` and `Kaxis_local_coincidence`.
-/

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

set_option maxHeartbeats 1000000

noncomputable section

/-- **The Schwarz-lemma step.**  A crude bound for the cleared numerator `Ncusp` on the tile `E`
(with the `τ`-dependence in a polynomial in `scale τ`) implies the sharp CKMRV bound. -/
theorem slash_crude_sharp_E (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
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
theorem slash_KMinus_E (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
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
  · exact slash_crude_sharp_E ℓ 8 (Or.inl rfl) (Ncusp_EReg_crude_8 ℓ)
  · exact slash_crude_sharp_E ℓ 24 (Or.inr rfl) (Ncusp_EReg_crude_24 ℓ)

/-- **The CKMRV `E`-order bound for `K_+`**, `d = 8` or `d = 24`.

This is the `K_+` case of CKMRV Lemma 4.12 (`quotientbounds1new`) on the tile `E`; it follows
from `Xi8_bound_E` / `Xi24_bound_E` through the identifications `Xi8_eq` / `Xi24_eq`, as in
`Epoint_Kfun.lean`. -/
theorem slash_KPlus_E (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : UpperHalfPlane),
      (3 / 2 : ℝ) ≤ (ModularGroup.S • τ).im → 1 ≤ z.im →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
        ‖(z : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) *
            Work.Kernels.KPlus d τ (ModularGroup.S • z)‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) *
              Real.exp (-(Real.pi * z.im)) /
            ‖Work.Kernels.DeltaFun z *
              (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
  rcases hd with rfl | rfl
  · simpa using Work.Asymptotics.KPlus8_slash_bound_of_Xi8 Work.Asymptotics.Xi8_bound_E
  · simpa using Work.Asymptotics.KPlus24_slash_bound_of_Xi24 Work.Asymptotics.Xi24_bound_E

end

end Work.Asymptotics
